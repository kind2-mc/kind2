.PHONY: all doc html pdf clean distclean serve theme vendor-assets

# `make doc` builds both output formats, matching the old Sphinx `make all` (html + pdf).
all: doc
doc: html pdf

# Hextra is a git submodule (see .gitmodules), not vendored in this repo — this
# pulls it in automatically the first time you build after `git clone`.
theme: themes/hextra/layouts

themes/hextra/layouts:
	@if git rev-parse --git-dir > /dev/null 2>&1; then \
		echo "==> fetching theme (git submodule)"; \
		git submodule update --init --recursive; \
	else \
		echo "themes/hextra is missing and this isn't a git checkout, so it can't be"; \
		echo "fetched automatically. Either:"; \
		echo "  git clone --recurse-submodules <this-repo-url>"; \
		echo "or, if you already have a plain clone:"; \
		echo "  git submodule update --init --recursive"; \
		exit 1; \
	fi

# KaTeX (math) and FlexSearch (search) are fetched via npm into assets/vendor/
# on demand, not committed — see fetch-vendor-assets.sh. This avoids relying
# on cdn.jsdelivr.net at Hugo build time without checking binary assets into git.
vendor-assets: assets/vendor/katex/dist/katex.min.css

assets/vendor/katex/dist/katex.min.css assets/vendor/flexsearch/dist/flexsearch.bundle.min.js &: fetch-vendor-assets.sh
	./fetch-vendor-assets.sh

html: theme vendor-assets
	hugo --minify

pdf: html
	SKIP_HUGO_BUILD=1 PYTHON=$(VENV)/bin/python3 ./pdf-tools/build_pdf.sh

serve: theme vendor-assets
	hugo server -D

clean:
	rm -rf public resources/_gen print/all-docs.html print/*.pdf

distclean: clean
	rm -rf $(VENV) assets/vendor
