# PDF export

Generates a single combined PDF of the whole documentation site.

## Setup (one-time)

    pip install -r pdf-tools/requirements.txt
    # WeasyPrint also needs: apt-get install libpango-1.0-0 libpangocairo-1.0-0 libcairo2 libgdk-pixbuf2.0-0

## Usage

    ./pdf-tools/build_pdf.sh

This runs `hugo build`, merges every docs page (in nav order, defined in
`pdf-tools/destmap.py`) into `print/all-docs.html`, then renders it to
`print/kind2-user-documentation.pdf`.

If you add or reorder pages, update the `DEST_MAP` / `SECTIONS` tables in
`pdf-tools/destmap.py` to match — the print order is driven from there, not
auto-discovered from the content tree.
