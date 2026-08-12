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
	# Generate the project README with CI links for Github
	echo '<!-- DO NOT EDIT, see doc/README.md for details -->\n' > ../README.md
	cat content/header.md >> ../README.md
	cat content/home.md >> ../README.md
	# Replace internal references with explicit ones to render README on Github
	sed -E -i 's/:ref:`(.*)<(.*)>`/`\1<${doc_root}\2\.html>`_/g' ../README.md
	# Replace include directives with the file contents, as the
	# directives are not currently supported/rendered on Github.
	# The source/ directory is where files included in
	# this manner are expected to reside.
	#     https://unix.stackexchange.com/a/128797/248178
	sed -i '/\.\. include:: \(.*\)/{s//source\/\1/;s/'\''/&\\&&/g;s/.*/cat<'"'&'/e}" ../README.md
	# Generate the documentation README
	echo '<!-- DO NOT EDIT, edit content/README.md instead -->\n' > README.md
	cat content/README.md >> README.md
	sed -i '/\.\. include:: \(.*\)/{s//source\/\1/;s/'\''/&\\&&/g;s/.*/cat<'"'&'/e}" README.md
	cp content/docs/license.md ../LICENSE.md

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
