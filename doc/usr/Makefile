CONTENT = $(shell find content -iname "*.md")

all: pdf html

preprocess: src/preprocess.ml
	ocamlc -o preprocess unix.cma src/preprocess.ml

target/target.md: $(CONTENT) preprocess
	mkdir -p target
	./preprocess ./target/target.md ./content/Home.md \
		`find ./content/*/ -iname "*.md" | sort | sed -e 's:\n: :g' -e 's://*:/:g'`
	find content -iname "*.png" -exec cp -f {} target/. \;

pdf: target/target.md
	cd target ; \
	cat ../rsc/options | \
	sed 's:^\([a-z]\):-V \1:; s:##version##:$(version):g'| \
	tr '\n' ' ' |  xargs \
	pandoc --template=./../rsc/template ./target.md \
	-s -o ./doc.pdf

html: target/target.md
	cat ./rsc/options | \
	sed 's:^\([a-z]\):-V \1:; s:##version##:$(version):g'| \
	tr '\n' ' ' |  xargs \
	pandoc --toc -S -H ./rsc/github-pandoc.css.include ./target/target.md \
	-s -o ./target/doc.html

update:
	rm -f ../../README.md
	echo "\n\n<!-- DO NOT EDIT, see ./doc/usr/content/{Home.md,TravisLinks} -->\n\n" > \
		../../README.md
	cat content/TravisLinks >> ../../README.md
	cat content/Home.md | \
		sed -e 's:](\./\([^)]*\)):](doc/usr/content/\1):g' >> \
		../../README.md
	cp content/9_other/license.md ../../LICENSE.md

clean:
	rm -f src/*.cmi src/*.cmo src/*.cmx src/*.o
	rm -f preprocess texput.log
	rm -rf target

.PHONY: pdf html
