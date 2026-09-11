import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlparse
import os
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parent.parent
CONTENT_DOCS = ROOT / "content" / "docs"
PUBLIC = ROOT / "public"
OUT_HTML = ROOT / "print" / "all-docs.html"
KATEX_CSS = ROOT / "assets" / "vendor" / "katex" / "dist" / "katex.min.css"
# Single source of truth for the version, shared with the binary itself.
VERSION_ML = ROOT.parent / "src" / "version.ml"

DOC_TITLE = "Kind 2 User Documentation"

# Hugo bakes the baseURL's path into every site-root-absolute URL it writes, so
# mapping one back to a file under public/ means stripping that path first.
# HUGO_BASEURL is the only thing that sets it (hugo.yaml deliberately carries no
# baseURL), and unset means Hugo defaulted to "/".
BASE_PATH = urlparse(os.environ.get("HUGO_BASEURL", "/")).path or "/"
if not BASE_PATH.endswith("/"):
    BASE_PATH += "/"


def project_version():
    """Version shown on the title page: 'v3.0.0' in version.ml prints as '3.0.0'."""
    override = os.environ.get("KIND2_DOC_VERSION")
    if override:
        return override.lstrip("v")
    if not VERSION_ML.exists():
        print(f"MISSING {VERSION_ML} (set KIND2_DOC_VERSION to override)", file=sys.stderr)
        sys.exit(1)
    match = re.search(
        r'^\s*let\s+base_version\s*=\s*"v?([^"]+)"',
        VERSION_ML.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    if not match:
        print(f"No base_version found in {VERSION_ML} (set KIND2_DOC_VERSION to override)", file=sys.stderr)
        sys.exit(1)
    return match.group(1)


def build_date():
    """Title-page date, honouring SOURCE_DATE_EPOCH for reproducible builds."""
    epoch = os.environ.get("SOURCE_DATE_EPOCH")
    if epoch:
        stamp = datetime.fromtimestamp(int(epoch), tz=timezone.utc)
    else:
        stamp = datetime.now()
    # Written out rather than strftime("%B %-d, %Y") because the no-pad flag
    # isn't portable.
    return f"{stamp.strftime('%B')} {stamp.day}, {stamp.year}"


def frontmatter_weight(path):
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        return 10**9
    end = text.find("\n---", 3)
    if end < 0:
        return 10**9
    for line in text[3:end].splitlines():
        if line.strip().startswith("weight:"):
            try:
                return int(line.split(":", 1)[1].strip())
            except ValueError:
                pass
    return 10**9


def public_path_for(source):
    rel = source.relative_to(CONTENT_DOCS)
    if rel.parent == Path("."):
        return PUBLIC / "docs" / ("index.html" if rel.name == "_index.md" else Path(rel.stem) / "index.html")
    section = rel.parent
    return PUBLIC / "docs" / section / ("index.html" if rel.name == "_index.md" else Path(rel.stem) / "index.html")


def ordered_page_paths():
    """Discover print order from Hugo content weights, not old Sphinx stems."""
    order = []
    root_index = CONTENT_DOCS / "_index.md"
    if root_index.exists():
        order.append(root_index)

    sections = []
    for section_index in CONTENT_DOCS.glob("*/_index.md"):
        sections.append((frontmatter_weight(section_index), section_index))
    for _, section_index in sorted(sections, key=lambda item: (item[0], str(item[1]))):
        text = section_index.read_text(encoding="utf-8")
        body = text.split("\n---", 2)[-1].strip() if text.startswith("---") else text.strip()
        if body:
            order.append(section_index)
        pages = [p for p in section_index.parent.glob("*.md") if p.name != "_index.md"]
        order.extend(sorted(pages, key=lambda p: (frontmatter_weight(p), p.name)))

    # Direct child pages such as the license are printed after the main sections.
    direct_pages = [p for p in CONTENT_DOCS.glob("*.md") if p.name != "_index.md"]
    order.extend(sorted(direct_pages, key=lambda p: (frontmatter_weight(p), p.name)))
    return order

def rewrite_image_sources(main, page_path):
    for img in main.find_all("img"):
        src = img.get("src")
        if not src:
            continue
        parsed = urlparse(src)
        if parsed.scheme in {"http", "https", "data"} or src.startswith("//"):
            continue
        if src.startswith("/"):
            rel = src[len(BASE_PATH):] if src.startswith(BASE_PATH) else src.lstrip("/")
            candidate = PUBLIC / rel
        else:
            candidate = (page_path.parent / src).resolve()
        if not candidate.exists():
            raise FileNotFoundError(f"Image {src!r} referenced by {page_path} resolves to {candidate}")
        # Keep generated HTML portable: an absolute file:// URI would point at
        # the build machine's checkout and break when the tree is moved.
        img["src"] = Path(os.path.relpath(candidate, OUT_HTML.parent)).as_posix()


def number_headings(soup, main, chapter):
    """Number a page's headings the way the Sphinx build did (chapter 1, section
    1.1, subsection 1.1.1) and return the chapter/section entries for the table
    of contents. Each numbered heading gets a unique id so the TOC can link to
    it and ask WeasyPrint for its page number."""
    entries = []
    section = subsection = 0
    for heading in main.find_all(["h1", "h2", "h3"]):
        if heading.name == "h1":
            section = subsection = 0
            number = str(chapter)
        elif heading.name == "h2":
            section += 1
            subsection = 0
            number = f"{chapter}.{section}"
        else:
            if not section:
                # An h3 with no h2 above it has no number to hang off of.
                continue
            subsection += 1
            number = f"{chapter}.{section}.{subsection}"
        title = heading.get_text(strip=True)
        anchor = "pdf-sec-" + number.replace(".", "-")
        heading["id"] = anchor
        label = soup.new_tag("span", attrs={"class": "heading-number"})
        label.string = number
        heading.insert(0, label)
        if heading.name in {"h1", "h2"}:
            entries.append((heading.name, number, title, anchor))
    return entries


def render_toc(soup, entries):
    """Table of contents; page numbers are filled in at render time by the
    target-counter() rule in the stylesheet."""
    nav = soup.new_tag("nav", attrs={"class": "print-toc"})
    items = soup.new_tag("ul")
    nav.append(items)
    for level, number, title, anchor in entries:
        item = soup.new_tag(
            "li", attrs={"class": "toc-chapter" if level == "h1" else "toc-section"}
        )
        link = soup.new_tag("a", href="#" + anchor)
        label = soup.new_tag("span", attrs={"class": "toc-number"})
        label.string = number
        link.append(label)
        text = soup.new_tag("span", attrs={"class": "toc-title"})
        text.string = title
        link.append(text)
        item.append(link)
        items.append(item)
    return nav


def build_front_matter(soup, entries):
    """Title page: title, version, date, then the table of contents, as the
    Sphinx-generated PDF had it."""
    front = soup.new_tag("div", attrs={"class": "front-matter"})
    title = soup.new_tag("h1", attrs={"class": "doc-title"})
    title.string = DOC_TITLE
    front.append(title)
    version = soup.new_tag("p", attrs={"class": "doc-version"})
    version.string = f"Version {project_version()}"
    front.append(version)
    date = soup.new_tag("p", attrs={"class": "doc-date"})
    date.string = build_date()
    front.append(date)
    front.append(render_toc(soup, entries))
    return front


def build_merged_html():
    errors = 0
    OUT_HTML.parent.mkdir(parents=True, exist_ok=True)
    version = project_version()
    sections_html = []
    toc_entries = []
    chapter = 0
    for source_path in ordered_page_paths():
        path = public_path_for(source_path)
        if not path.exists():
            print("MISSING", source_path, path)
            errors += 1
            continue
        soup = BeautifulSoup(path.read_text(encoding="utf-8"), "lxml")
        main = soup.find("main", id="content")
        if not main:
            print("NO MAIN", source_path)
            errors += 1
            continue
        # Take only the page body. Hextra wraps it in <main> together with the
        # breadcrumb trail and the previous/next pager, which are site
        # navigation with nothing to point at in a PDF -- and whose chevron
        # icons render at full size here, since the theme's stylesheet that
        # shrinks them is not part of the print CSS.
        content = main.find("div", class_="content", recursive=False)
        if not content:
            print("NO CONTENT", source_path)
            errors += 1
            continue
        for sel in content.select('[class*="hextra-toc"], nav[aria-label], a[href*="edit/main"], button'):
            sel.decompose()
        for mathml in content.select(".katex-mathml"):
            mathml.decompose()
        try:
            rewrite_image_sources(content, path)
        except FileNotFoundError as exc:
            print("MISSING IMAGE", exc)
            errors += 1
            continue
        chapter += 1
        toc_entries.extend(number_headings(soup, content, chapter))
        sections_html.append(f'<section class="doc-page">{content}</section>')
    if errors:
        print(f"PDF merge failed: {errors} page(s) or assets missing", file=sys.stderr)
        sys.exit(1)
    if not KATEX_CSS.exists():
        print(f"MISSING KaTeX CSS: {KATEX_CSS}", file=sys.stderr)
        sys.exit(1)
    katex_css = KATEX_CSS.read_text(encoding="utf-8")
    font_dir = ROOT / "assets" / "css" / "fonts"

    if not font_dir.exists():
        print(f"MISSING KaTeX fonts: {font_dir}", file=sys.stderr)
        sys.exit(1)
    # The CSS is inlined into print/all-docs.html, so font URLs must be
    # relative to that file rather than absolute file:// URLs.
    font_url = Path(os.path.relpath(font_dir, OUT_HTML.parent)).as_posix() + "/"
    katex_css = katex_css.replace("url(fonts/", f"url({font_url}")
    css = """
    %s
    @page { size: A4; @bottom-center { content: counter(page); font-size: .8rem; color: #555; } }
    /* Front matter is numbered in roman and the body restarts at 1, as the
       LaTeX build did. The reset has to live in an @page rule -- WeasyPrint
       ignores counter-reset: page on an element -- and :nth(1 of body) picks
       the first page of the body page group. That group is the .body-matter
       wrapper: one element, hence one group. Naming the pages on each section
       instead would start a fresh group, and a fresh page 1, per chapter. */
    @page front { @bottom-center { content: counter(page, lower-roman); } }
    @page :nth(1 of body) { counter-reset: page 1; }
    .front-matter { page: front; }
    .body-matter { page: body; }
    body { font-family: -apple-system, Helvetica, Arial, sans-serif; line-height: 1.55; color: #1a1a1a; max-width: 800px; margin: 2rem auto; padding: 0 1rem; }
    h1 { font-size: 1.8rem; margin-top: 3rem; border-bottom: 2px solid #ddd; padding-bottom: .3rem; }
    h2 { font-size: 1.4rem; margin-top: 2rem; }
    h3 { font-size: 1.15rem; }
    .heading-number { margin-right: .5em; }
    pre { background: #f5f5f5; padding: .75rem 1rem; overflow-x: auto; border-radius: 6px; font-size: .85rem; }
    code { background: #f0f0f0; padding: .1rem .3rem; border-radius: 4px; font-size: .9em; }
    pre code { background: none; padding: 0; }
    table { border-collapse: collapse; width: 100%%; margin: 1rem 0; }
    th, td { border: 1px solid #ccc; padding: .4rem .6rem; text-align: left; }
    img { max-width: 100%%; height: auto; }
    section.doc-page { page-break-before: always; }
    a { color: #0969da; text-decoration: none; }
    blockquote { border-left: 4px solid #ccc; margin: 1rem 0; padding: .2rem 1rem; color: #555; background: #fafafa; }
    .front-matter { text-align: center; }
    .front-matter h1.doc-title { border: none; font-size: 2.4rem; margin: 0 0 1.4rem; }
    .front-matter .doc-version { font-size: 1.25rem; font-weight: bold; margin: 0; }
    .front-matter .doc-date { font-size: 1.05rem; margin: .3rem 0 2.5rem; }
    nav.print-toc { text-align: left; }
    nav.print-toc ul { list-style: none; margin: 0; padding: 0; }
    nav.print-toc li { margin: .1rem 0; }
    nav.print-toc a { display: block; color: #1a1a1a; }
    /* WeasyPrint resolves the page each entry's target lives on, and leader()
       fills the gap in between with dots. */
    nav.print-toc a::after { content: leader('.') target-counter(attr(href), page); }
    nav.print-toc .toc-number { display: inline-block; min-width: 2.4em; }
    nav.print-toc li.toc-chapter { font-weight: bold; margin-top: .5rem; }
    nav.print-toc li.toc-section { padding-left: 2.4em; font-size: .95rem; }
    nav.print-toc li.toc-section .toc-number { min-width: 3em; }
    """ % katex_css
    front_soup = BeautifulSoup("", "lxml")
    front_matter = build_front_matter(front_soup, toc_entries)
    doc = '''<!DOCTYPE html>
<html><head><meta charset="utf-8">
<title>%s %s</title>
<style>%s</style>
</head><body>
%s
<div class="body-matter">%s</div>
</body></html>''' % (DOC_TITLE, version, css, front_matter, ''.join(sections_html))
    OUT_HTML.write_text(doc, encoding="utf-8")
    print("Wrote", OUT_HTML, len(sections_html), "sections,", len(toc_entries), "TOC entries")

if __name__ == "__main__":
    build_merged_html()
