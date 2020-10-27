DUNE_DOCDIR=$(CURDIR)/_build/default/_doc/_html
LOCAL_ALLDOCDIR=$(CURDIR)/doc
LOCAL_BINDIR=$(CURDIR)/bin
LOCAL_DOCDIR=$(CURDIR)/ocamldoc
LOCAL_USRDOCDIR=$(CURDIR)/doc/usr

.PHONY: all build clean doc install kind2-doc test uninstall

all: build

build:
	@dune build src @install
	@dune install --sections=bin --prefix . 2> /dev/null

clean:
	@dune clean
	@rm -rf $(LOCAL_BINDIR) $(LOCAL_DOCDIR)

doc:
	make -C $(LOCAL_USRDOCDIR) all
	cp $(LOCAL_USRDOCDIR)/build/pdf/kind2.pdf $(LOCAL_ALLDOCDIR)/user_documentation.pdf

install:
	@opam pin add -n -y kind2 https://github.com/kind2-mc/kind2.git
	@opam depext -y kind2
	@opam install -y kind2

kind2-doc:
	@dune build @doc-private
	@dune build @copy
	@mkdir -p $(LOCAL_DOCDIR)
	@cp -rf $(DUNE_DOCDIR)/* $(LOCAL_DOCDIR)

test:
	@$(CURDIR)/tests/run.sh $(CURDIR)/tests/regression $(CURDIR)/bin/kind2 --timeout 42 --no_tc false

uninstall:
	@opam remove -y kind2
	@opam unpin kind2
