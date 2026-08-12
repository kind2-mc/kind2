.PHONY: all doc html pdf update clean distclean serve venv

# `make doc` builds both output formats, matching the old Sphinx `make all` (html + pdf).
all: doc
doc: html pdf update

html:
	hugo --minify

# Debian/Ubuntu (PEP 668) block system-wide `pip install`, so PDF tooling gets
# its own venv, created on first use. Run `make distclean` to force a rebuild.
VENV := pdf-tools/venv

venv: $(VENV)/bin/activate

$(VENV)/bin/activate: pdf-tools/requirements.txt
	python3 -m venv $(VENV)
	$(VENV)/bin/pip install --quiet --upgrade pip
	$(VENV)/bin/pip install --quiet -r pdf-tools/requirements.txt
	touch $(VENV)/bin/activate

pdf: html venv
	SKIP_HUGO_BUILD=1 PYTHON=$(VENV)/bin/python3 ./pdf-tools/build_pdf.sh

update:
	echo '<!-- DO NOT EDIT, see doc/usr/README.rst for details -->\n' > ../README.md
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

	cp content/docs/license.md ../../LICENSE.md

serve:
	hugo server -D

clean:
	rm -rf public resources/_gen print/all-docs.html print/*.pdf

distclean: clean
	rm -rf $(VENV)
