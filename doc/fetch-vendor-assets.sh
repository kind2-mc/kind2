#!/usr/bin/env bash
# Fetches KaTeX and FlexSearch static assets into assets/vendor/, so the
# site doesn't depend on cdn.jsdelivr.net at Hugo build time, without
# committing those third-party files to this repo. Re-run any time
# assets/vendor/ is missing or you bump the pinned versions below.
#
# Only needs curl (or wget) and tar — no Node/npm required.
# FETCHES ONLY .woff2 fonts from KaTeX, not the .woff or .ttf files, to reduce repo size.

set -euo pipefail
cd "$(dirname "$0")"

KATEX_VERSION="0.16.11"
FLEXSEARCH_VERSION="0.8.143"

fetch() {
  # fetch <url> <output-file>
  if command -v curl > /dev/null; then
    curl -fsSL "$1" -o "$2"
  elif command -v wget > /dev/null; then
    wget -q "$1" -O "$2"
  else
    echo "Need curl or wget to fetch vendor assets; neither was found." >&2
    exit 1
  fi
}

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

echo "==> fetching katex@${KATEX_VERSION}"
mkdir -p assets/vendor/katex/dist
mkdir -p assets/css/fonts

fetch "https://registry.npmjs.org/katex/-/katex-${KATEX_VERSION}.tgz" "$WORK/katex.tgz"
tar xzf "$WORK/katex.tgz" -C "$WORK"

cp "$WORK"/package/dist/katex.min.css assets/vendor/katex/dist/
cp "$WORK"/package/dist/fonts/*.woff2 assets/css/fonts/

echo "==> fetching flexsearch@${FLEXSEARCH_VERSION}"
mkdir -p assets/vendor/flexsearch/dist
fetch "https://registry.npmjs.org/flexsearch/-/flexsearch-${FLEXSEARCH_VERSION}.tgz" "$WORK/flexsearch.tgz"
tar xzf "$WORK/flexsearch.tgz" -C "$WORK"
cp "$WORK"/package/dist/flexsearch.bundle.min.js assets/vendor/flexsearch/dist/

echo "==> done: assets/vendor/"
