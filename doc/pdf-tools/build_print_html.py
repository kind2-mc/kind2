import sys
from pathlib import Path
from urllib.parse import urlparse
import os
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parent.parent
CONTENT_DOCS = ROOT / "content" / "docs"
PUBLIC = ROOT / "public"
OUT_HTML = ROOT / "print" / "all-docs.html"
KATEX_CSS = ROOT / "assets" / "vendor" / "katex" / "dist" / "katex.min.css"

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
            base = "/kind2_user_doc/"
            rel = src[len(base):] if src.startswith(base) else src.lstrip("/")
            candidate = PUBLIC / rel
        else:
            candidate = (page_path.parent / src).resolve()
        if not candidate.exists():
            raise FileNotFoundError(f"Image {src!r} referenced by {page_path} resolves to {candidate}")
        # Keep generated HTML portable: an absolute file:// URI would point at
        # the build machine's checkout and break when the tree is moved.
        img["src"] = Path(os.path.relpath(candidate, OUT_HTML.parent)).as_posix()

def build_merged_html():
    errors = 0
    OUT_HTML.parent.mkdir(parents=True, exist_ok=True)
    sections_html = []
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
        for sel in main.select('[class*="hextra-toc"], nav[aria-label], a[href*="edit/main"], button'):
            sel.decompose()
        for mathml in main.select(".katex-mathml"):
            mathml.decompose()
        try:
            rewrite_image_sources(main, path)
        except FileNotFoundError as exc:
            print("MISSING IMAGE", exc)
            errors += 1
            continue
        sections_html.append(f'<section class="doc-page">{main}</section>')
    if errors:
        print(f"PDF merge failed: {errors} page(s) or assets missing", file=sys.stderr)
        sys.exit(1)
    if not KATEX_CSS.exists():
        print(f"MISSING KaTeX CSS: {KATEX_CSS}", file=sys.stderr)
        sys.exit(1)
    katex_css = KATEX_CSS.read_text(encoding="utf-8")
    font_dir = KATEX_CSS.parent / "fonts"
    # The CSS is inlined into print/all-docs.html, so font URLs must be
    # relative to that file rather than absolute file:// URLs.
    font_url = Path(os.path.relpath(font_dir, OUT_HTML.parent)).as_posix() + "/"
    katex_css = katex_css.replace("url(fonts/", f"url({font_url}")
    css = """
    %s
    body { font-family: -apple-system, Helvetica, Arial, sans-serif; line-height: 1.55; color: #1a1a1a; max-width: 800px; margin: 2rem auto; padding: 0 1rem; }
    h1 { font-size: 1.8rem; margin-top: 3rem; border-bottom: 2px solid #ddd; padding-bottom: .3rem; }
    h2 { font-size: 1.4rem; margin-top: 2rem; }
    h3 { font-size: 1.15rem; }
    pre { background: #f5f5f5; padding: .75rem 1rem; overflow-x: auto; border-radius: 6px; font-size: .85rem; }
    code { background: #f0f0f0; padding: .1rem .3rem; border-radius: 4px; font-size: .9em; }
    pre code { background: none; padding: 0; }
    table { border-collapse: collapse; width: 100%%; margin: 1rem 0; }
    th, td { border: 1px solid #ccc; padding: .4rem .6rem; text-align: left; }
    img { max-width: 100%%; height: auto; }
    section.doc-page { page-break-before: always; }
    section.doc-page:first-child { page-break-before: avoid; }
    a { color: #0969da; text-decoration: none; }
    blockquote { border-left: 4px solid #ccc; margin: 1rem 0; padding: .2rem 1rem; color: #555; background: #fafafa; }
    """ % katex_css
    doc = '''<!DOCTYPE html>
<html><head><meta charset="utf-8">
<title>Kind 2 User Documentation</title>
<style>%s</style>
</head><body>
<h1 style="border:none; font-size:2.4rem; text-align:center; margin-top:0;">Kind 2 User Documentation</h1>
%s
</body></html>''' % (css, ''.join(sections_html))
    OUT_HTML.write_text(doc, encoding="utf-8")
    print("Wrote", OUT_HTML, len(sections_html), "sections")

if __name__ == "__main__":
    build_merged_html()
