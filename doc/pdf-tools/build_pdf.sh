#!/usr/bin/env bash
# Builds the Hugo site, merges all docs pages into one printable HTML file,
# and renders that to a single PDF: print/kind2-user-documentation.pdf
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> hugo build"
if [ -d public ] && [ "${SKIP_HUGO_BUILD:-}" = "1" ]; then
  echo "    (skipped, public/ already built)"
else
  hugo --minify
fi

echo "==> merging pages"
python3 pdf-tools/build_print_html.py

echo "==> rendering PDF"
python3 - <<'PY'
from weasyprint import HTML
HTML("print/all-docs.html", base_url="print").write_pdf("print/kind2-user-documentation.pdf")
PY

echo "Done: print/kind2-user-documentation.pdf"
