.PHONY: all clean update build-pdf build-html pdf html
doc_root := doc\/usr\/source

all: pdf html

clean:
	rm -f ../../README.md
	rm -f ../../LICENSE.md
	rm -f source/about.md

update:
	cat source/title.md >> source/about.md
	cat source/home.md >> source/about.md
	echo "\n<!-- DO NOT EDIT, see ./doc/usr/README.md for details -->\n" > ../../README.md
	cat source/travis_links.md >> ../../README.md
	cat source/title.md >> ../../README.md
	cat source/home.md >> ../../README.md
	sed -i -E "s/(\[.*\])(\()(\.)([^)]*\))/\1\2$(doc_root)\4/" ../../README.md
	cp source/9_other/license.md ../../LICENSE.md

build-pdf: 
	sphinx-build -b latex source build && cd build && make && cd ..

build-html:
	sphinx-build -b html source build

pdf: clean update build-pdf

html: clean update build-html
