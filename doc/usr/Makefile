all:
	ocamlc -o preprocess unix.cma src/preprocess.ml
	./preprocess ./target.md ./content/Home.md \
		`find ./content/*/ -iname "*.md" | sed -e 's:\n: :g' -e 's://*:/:g'`
	cat ./locals | sed 's:^\([a-z]\):-V \1:' | tr '\n' ' ' | \
	xargs \
		pandoc --template=./latex_template ./target.md -s -o doc.pdf

pandoc:
	cat ./locals | sed 's:^\([a-z]\):-V \1:' | tr '\n' ' ' | \
	xargs \
		pandoc --template=./templates/default.latex ./target.md -s -o doc.pdf

clean:
	rm -f src/*.cmi src/*.cmo src/*.cmx src/*.o
	rm -f preprocess
	rm -f target.md
