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

readme_update:
	cat content/Home.md | \
	sed -e 's:](\./\([^)]*\)):](doc/usr/content/\1):g' > \
	../../README.md

clean:
	rm -f src/*.cmi src/*.cmo src/*.cmx src/*.o
	rm -f preprocess
	rm -f target.md

.PHONY: pandoc
