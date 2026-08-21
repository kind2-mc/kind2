#!/usr/bin/env bash
# Builds the Hugo site, merges all docs pages into one printable HTML file,
# and renders that to a single PDF: print/kind2-user-documentation.pdf
#
# Set PYTHON to point at a specific interpreter (e.g. a venv) if needed.
# `make pdf` does this automatically via pdf-tools/venv.
set -euo pipefail
cd "$(dirname "$0")/.."

PYTHON="${PYTHON:-python3}"

echo "==> hugo build"
if [ -d public ] && [ "${SKIP_HUGO_BUILD:-}" = "1" ]; then
  echo "    (skipped, public/ already built)"
else
  hugo --minify
fi

echo "==> checking Python dependencies ($PYTHON)"
"$PYTHON" - <<'PY' || { echo; echo "Missing Python deps. Run: pip install -r pdf-tools/requirements.txt"; echo "(or just use 'make pdf' / 'make doc', which sets up a venv automatically)"; exit 1; }
import bs4, weasyprint
PY

echo "==> merging pages"
"$PYTHON" pdf-tools/build_print_html.py

echo "==> rendering PDF"
"$PYTHON" - <<'PY'
from weasyprint import HTML
HTML("print/all-docs.html", base_url="print").write_pdf("print/kind2-user-documentation.pdf")
PY

if ! command -v pdfinfo >/dev/null 2>&1 || ! pdfinfo print/kind2-user-documentation.pdf >/dev/null 2>&1; then
  echo "ERROR: generated PDF is unreadable" >&2
  exit 1
fi
if ! command -v pdfimages >/dev/null 2>&1; then
  echo "ERROR: pdfimages is required to validate embedded images" >&2
  exit 1
fi
if ! pdfimages -list print/kind2-user-documentation.pdf | awk 'NR > 2 && NF {found=1} END {exit found ? 0 : 1}'; then
  echo "ERROR: generated PDF contains no embedded images" >&2
  exit 1
fi

echo "Done: print/kind2-user-documentation.pdf"
