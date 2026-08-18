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
    sudo apt-get install libpango-1.0-0 libpangocairo-1.0-0 libcairo2 libgdk-pixbuf2.0-0

    # macOS
    brew install pango

## How it works

`pdf-tools/build_print_html.py` discovers every docs page directly from the
Hugo `content/docs/` tree and its `weight` front matter, then merges them into
`print/all-docs.html`. This keeps PDF page order in sync with Hugo without a
second Sphinx-era page map.
`pdf-tools/build_pdf.sh` renders that to
`print/kind2-user-documentation.pdf` with WeasyPrint.

