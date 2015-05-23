all:
	ocamlc -o preprocess unix.cma src/preprocess.ml
	./preprocess ./target.md ./content/Home.md \
		`find ./content/*/ -iname "*.md" | sed -e 's:\n: :g' -e 's://*:/:g'`
	pandoc ./target.md -s -o doc.pdf

clean:
	rm -f src/*.cmi src/*.cmo src/*.cmx src/*.o
	rm -f preprocess
	rm -f target.md

	