all:
	ocamlc -o preprocess unix.cma src/preprocess.ml
	./preprocess ./target.md ./content/Home.md \
		`find ./content/*/ -iname "*.md" | sed -e 's:\n: :g' -e 's://*:/:g'`
	cat ./rsc/options | sed 's:^\([a-z]\):-V \1:' | tr '\n' ' ' | \
		xargs \
		pandoc --template=./rsc/template ./target.md -s -o doc.pdf

pandoc:
	cat ./rsc/options | sed 's:^\([a-z]\):-V \1:' | tr '\n' ' ' | \
	xargs \
		pandoc --template=./rsc/template ./target.md -s -o doc.pdf

update:
	rm -f ../../README.md
	echo "<!-- DO NOT EDIT, see ./doc/usr/README.md -->\n\n" > ../../README.md
	cat content/Home.md | \
		sed -e 's:](\./\([^)]*\)):](doc/usr/content/\1):g' >> \
		../../README.md
	cp content/9_other/license.md ../../LICENSE.md

clean:
	rm -f src/*.cmi src/*.cmo src/*.cmx src/*.o
	rm -f preprocess
	rm -f target.md

.PHONY: pandoc
