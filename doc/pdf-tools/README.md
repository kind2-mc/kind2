# PDF export

Generates a single combined PDF of the whole documentation site.

## Usage

    make doc     # builds both HTML (public/) and PDF (print/kind2-user-documentation.pdf)
    make pdf     # builds just the PDF (implies html)
    make html    # builds just the static HTML

`make pdf` creates a self-contained virtual environment at `pdf-tools/venv`
the first time it runs (avoids Debian/Ubuntu's PEP 668
"externally-managed-environment" restriction on system-wide `pip install`)
and installs `pdf-tools/requirements.txt` into it. Subsequent runs reuse it
and are fast. Run `make distclean` to remove it and start fresh.

### Manual / non-Make usage

    python3 -m venv pdf-tools/venv
    pdf-tools/venv/bin/pip install -r pdf-tools/requirements.txt
    PYTHON=pdf-tools/venv/bin/python3 ./pdf-tools/build_pdf.sh

WeasyPrint also needs a few system libraries for font/text rendering, which
pip does not install:

    # Debian/Ubuntu
    sudo apt-get install libpango-1.0-0 libpangocairo-1.0-0 libcairo2 libgdk-pixbuf2.0-0 poppler-utils

    # macOS
    brew install pango

## How it works

`pdf-tools/build_print_html.py` discovers every docs page directly from the
Hugo `content/docs/` tree and its `weight` front matter, then merges them into
`print/all-docs.html`. This keeps PDF page order in sync with Hugo without a
second Sphinx-era page map.
`pdf-tools/build_pdf.sh` renders that to
`print/kind2-user-documentation.pdf` with WeasyPrint.

Only the `div.content` body of each page is kept. Hextra also puts the
breadcrumb trail and the previous/next pager inside `<main>`; both are site
navigation with nothing to point at in a PDF, and their chevron icons render at
full size here because the theme stylesheet that shrinks them is not part of the
print CSS.

The merged file opens with a title page carrying the version and build date
followed by a table of contents, as the old Sphinx/LaTeX PDF did. Headings are
numbered `1`, `1.1`, `1.1.1` (one chapter per docs page) and the TOC lists
chapters and sections; WeasyPrint fills in the page numbers at render time via
`target-counter()`.

The front matter is numbered in lower-case roman and the body restarts at 1, so
chapter 1 opens on page 1. WeasyPrint ignores `counter-reset: page` on an
element, so the reset lives in an `@page` rule picked by GCPM's document
sequence selector, `@page :nth(1 of body)`. A page group is one element's run of
pages, which is why every chapter is wrapped in a single `div.body-matter`:
putting `page: body` on each chapter section instead would open a new group, and
restart the numbering, at every chapter.

The version comes from `base_version` in `src/version.ml`, the same string the
`kind2` binary reports. Override it with `KIND2_DOC_VERSION` if needed. The date
is the build date; set `SOURCE_DATE_EPOCH` for a reproducible build.

