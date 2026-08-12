import os, sys, re
from bs4 import BeautifulSoup

sys.path.insert(0, "pdf-tools")
from destmap import DEST_MAP, SECTIONS

PUBLIC = "./public"
OUT_HTML = "./print/all-docs.html"

def html_path_for(stem):
    section, slug, is_index, _ = DEST_MAP[stem]
    parts = [PUBLIC, "docs"]
    if section:
        parts.append(section)
    if is_index:
        parts.append("index.html")
    else:
        parts.append(slug)
        parts.append("index.html")
    return os.path.join(*parts)

def ordered_stems():
    # 1. docs root (Getting Started / home)
    order = ["home"]
    # 2. each section, its own index first, then pages by weight
    by_section = {folder: [] for folder, _, _ in SECTIONS}
    section_index_stem = {}
    for stem, (section, slug, is_index, weight) in DEST_MAP.items():
        if stem == "home" or section == "" :
            continue
        if is_index:
            section_index_stem[section] = stem
        else:
            by_section[section].append((weight, stem))
    for folder, title, _ in SECTIONS:
        if folder in section_index_stem:
            order.append(section_index_stem[folder])
        for _, stem in sorted(by_section[folder]):
            order.append(stem)
    # 3. license (section == "", not home)
    for stem, (section, slug, is_index, weight) in DEST_MAP.items():
        if section == "" and stem != "home":
            order.append(stem)
    return order

def build_merged_html():
    os.makedirs(os.path.dirname(OUT_HTML), exist_ok=True)
    sections_html = []
    for stem in ordered_stems():
        path = html_path_for(stem)
        if not os.path.exists(path):
            print("MISSING", stem, path)
            continue
        with open(path, encoding="utf-8") as f:
            soup = BeautifulSoup(f.read(), "lxml")
        main = soup.find("main", id="content")
        if not main:
            print("NO MAIN", stem)
            continue
        # drop the "on this page" TOC sidebar, edit-this-page links, and code-block copy buttons
        for sel in main.select('[class*="hextra-toc"], nav[aria-label], a[href*="edit/main"], button'):
            sel.decompose()
        sections_html.append(f'<section class="doc-page">{str(main)}</section>')

    css = """
    body { font-family: -apple-system, Helvetica, Arial, sans-serif; line-height: 1.55; color: #1a1a1a; max-width: 800px; margin: 2rem auto; padding: 0 1rem; }
    h1 { font-size: 1.8rem; margin-top: 3rem; border-bottom: 2px solid #ddd; padding-bottom: .3rem; }
    h2 { font-size: 1.4rem; margin-top: 2rem; }
    h3 { font-size: 1.15rem; }
    pre { background: #f5f5f5; padding: .75rem 1rem; overflow-x: auto; border-radius: 6px; font-size: .85rem; }
    code { background: #f0f0f0; padding: .1rem .3rem; border-radius: 4px; font-size: .9em; }
    pre code { background: none; padding: 0; }
    table { border-collapse: collapse; width: 100%; margin: 1rem 0; }
    th, td { border: 1px solid #ccc; padding: .4rem .6rem; text-align: left; }
    img { max-width: 100%; }
    svg { display: none; }
    section.doc-page { page-break-before: always; }
    section.doc-page:first-child { page-break-before: avoid; }
    a { color: #0969da; text-decoration: none; }
    blockquote { border-left: 4px solid #ccc; margin: 1rem 0; padding: .2rem 1rem; color: #555; background: #fafafa; }
    """

    doc = f"""<!DOCTYPE html>
<html><head><meta charset="utf-8">
<title>Kind 2 User Documentation</title>
<style>{css}</style>
</head><body>
<h1 style="border:none; font-size:2.4rem; text-align:center; margin-top:0;">Kind 2 User Documentation</h1>
{''.join(sections_html)}
</body></html>"""

    with open(OUT_HTML, "w", encoding="utf-8") as f:
        f.write(doc)
    print("Wrote", OUT_HTML, len(sections_html), "sections")

if __name__ == "__main__":
    build_merged_html()
