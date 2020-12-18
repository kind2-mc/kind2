.PHONY: all clean replace-include update build-pdf build-html pdf html
doc_root := https:\/\/kind.cs.uiowa.edu\/kind2_user_doc\/

all: html pdf

clean:
	rm -rf build/*

update:
	# Generate the project README with CI links for Github
	echo '.. DO NOT EDIT, see doc/usr/README.rst for details\n' > ../../README.rst
	cat source/header.rst >> ../../README.rst
	cat source/home.rst >> ../../README.rst
	# Replace internal references with explicit ones to render README on Github
	sed -E -i 's/:ref:`(.*)<(.*)>`/`\1<${doc_root}\2\.html>`_/g' ../../README.rst
	# Replace include directives with the file contents, as the
	# directives are not currently supported/rendered on Github.
	# The source/ directory is where files included in
	# this manner are expected to reside.
	#     https://unix.stackexchange.com/a/128797/248178
	sed -i '/\.\. include:: \(.*\)/{s//source\/\1/;s/'\''/&\\&&/g;s/.*/cat<'"'&'/e}" ../../README.rst
	# Generate the documentation README
	echo '.. DO NOT EDIT, edit source/README.rst instead\n' > README.rst
	cat source/README.rst >> README.rst
	sed -i '/\.\. include:: \(.*\)/{s//source\/\1/;s/'\''/&\\&&/g;s/.*/cat<'"'&'/e}" README.rst
	cp source/9_other/license.rst ../../LICENSE.rst

build-pdf: 
	sphinx-build -W -b latex source build/pdf && cd build/pdf && make && cd ../..

build-html:
	sphinx-build -W -b html source build/html

pdf: clean update build-pdf

html: clean update build-html
