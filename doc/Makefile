.PHONY: all doc html pdf clean distclean serve theme vendor-assets update

# `make doc` builds both output formats, matching the old Sphinx `make all` (html + pdf).
all: doc
doc: html pdf update

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

update:
	@printf "Updating root README.md and LICENSE.md...\n"
	{ \
		printf '<!-- DO NOT EDIT, edit content/docs/_index.md instead -->\n'; \
		cat content/header.md; \
		printf '\n'; \
		awk 'BEGIN{front=0} NR==1 && /^---$$/{front=1; next} front && /^---$$/{front=0; next} !front{print}' content/docs/_index.md | \
		sed -E 's#\{\{< relref "/docs/([^"]+)" >\}\}#https://kind.cs.uiowa.edu/kind2_user_doc/docs/\1#g'; \
	} > ../README.md
	awk 'BEGIN{front=0} NR==1 && /^---$$/{front=1; next} front && /^---$$/{front=0; next} !front{print}' content/docs/license.md > ../LICENSE.md
	@printf '<!-- DO NOT EDIT, edit content/README.md instead -->\n' > README.md
	cat content/README.md >> README.md

# KaTeX (math) and FlexSearch (search) are fetched via npm into assets/vendor/
# on demand, not committed — see fetch-vendor-assets.sh. This avoids relying
# on cdn.jsdelivr.net at Hugo build time without checking binary assets into git.
vendor-assets: assets/vendor/katex/dist/katex.min.css

assets/vendor/katex/dist/katex.min.css assets/vendor/flexsearch/dist/flexsearch.bundle.min.js &: fetch-vendor-assets.sh
	./fetch-vendor-assets.sh

html: theme vendor-assets
	hugo --minify

VENV := pdf-tools/venv

venv: $(VENV)/bin/activate

$(VENV)/bin/activate: pdf-tools/requirements.txt
	@if ! python3 -m venv $(VENV); then \
		rm -rf $(VENV); \
		echo; \
		echo "ERROR: could not create a Python virtual environment at $(VENV)."; \
		echo "This system may restrict or disallow venv creation (e.g. a"; \
		echo "locked-down Python, or a missing python3-venv package)."; \
		echo; \
		echo "Install the PDF dependencies manually instead, then tell make"; \
		echo "to use that interpreter directly instead of a venv:"; \
		echo "  pip install -r pdf-tools/requirements.txt --break-system-packages"; \
		echo "  PYTHON=python3 make pdf"; \
		echo; \
		exit 1; \
	fi
	$(VENV)/bin/pip install --quiet --upgrade pip
	$(VENV)/bin/pip install --quiet -r pdf-tools/requirements.txt
	touch $(VENV)/bin/activate

# If PYTHON is set explicitly (env var or `make PYTHON=... pdf`), use it
# directly and skip venv creation altogether — this is the manual-install
# escape hatch referenced in the error message above.
ifneq ($(filter command line environment,$(origin PYTHON)),)
pdf: html
	SKIP_HUGO_BUILD=1 PYTHON=$(PYTHON) ./pdf-tools/build_pdf.sh
else
pdf: html venv
	SKIP_HUGO_BUILD=1 PYTHON=$(VENV)/bin/python3 ./pdf-tools/build_pdf.sh
endif

serve: theme vendor-assets
	hugo server -D

clean:
	rm -rf public resources/_gen print/all-docs.html print/*.pdf

distclean: clean
	rm -rf $(VENV) assets/vendor
