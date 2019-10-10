.PHONY: all clean update build-pdf build-html pdf html
doc_root := doc\/usr\/source

all: clean html pdf

clean:
	rm -rf build/*
	#rm -f ../../README.md
	#rm -f ../../LICENSE.md
	rm -f source/about.rst

update:
	cat source/title.rst >> source/about.rst
	cat source/home.rst >> source/about.rst
	#echo "\n<!-- DO NOT EDIT, see ./doc/usr/README.md for details -->\n" > ../../README.md
	#cat source/travis_links.md >> ../../README.md
	#cat source/title.md >> ../../README.md
	#cat source/home.md >> ../../README.md
	#sed -i -E "s/(\[.*\])(\()(\.)([^)]*\))/\1\2$(doc_root)\4/" ../../README.md
	#cp source/9_other/license.md ../../LICENSE.md

build-pdf: 
	sphinx-build -W -b latex source build && cd build && make && cd ..

build-html:
	sphinx-build -W -b html source build

pdf: clean update build-pdf

html: clean update build-html
