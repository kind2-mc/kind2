.PHONY: all doc html pdf clean distclean serve venv

# `make doc` builds both output formats, matching the old Sphinx `make all` (html + pdf).
all: doc update
doc: html pdf

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
	echo '.. DO NOT EDIT, see doc/README.md for details\n' > ../../README.md
	

serve:
	hugo server -D

clean:
	rm -rf public resources/_gen print/all-docs.html print/*.pdf

distclean: clean
	rm -rf $(VENV)
