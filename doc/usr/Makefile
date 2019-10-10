.PHONY: all clean update build-pdf build-html pdf html
doc_root := doc\/usr\/source

all: clean html pdf

clean:
	rm -rf build/*
	rm -f ../../README.rst
	rm -f ../../LICENSE.rst

update:
	# Generate the project README with CI links for Github
	cat source/travis_links.rst >> ../../README.rst
	cat source/home.rst >> ../../README.rst
	# Replace internal references with explicit ones to render README on Github
	sed -E -i 's/:ref:`(.*)<(.*)>`/`\1<${doc_root}\/\2\.rst>`_/g' ../../README.rst
	cp source/9_other/license.rst ../../LICENSE.rst

build-pdf: 
	sphinx-build -W -b latex source build && cd build && make && cd ..

build-html:
	sphinx-build -W -b html source build

pdf: clean update build-pdf

html: clean update build-html
