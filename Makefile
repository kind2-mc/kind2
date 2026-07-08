DUNE_DOCDIR=$(CURDIR)/_build/default/_doc/_html
LOCAL_ALLDOCDIR=$(CURDIR)/doc
LOCAL_BINDIR=$(CURDIR)/bin
LOCAL_DOCDIR=$(CURDIR)/ocamldoc
LOCAL_USRDOCDIR=$(CURDIR)/doc/usr

.PHONY: all build clean doc install kind2-doc test uninstall

all: build

build:
	@dune build -p kind2 @install
	@dune install -p kind2 --sections=bin --prefix . 2> /dev/null

check:
	@dune build -p kind2 --profile strict @check @install
	@dune install -p kind2 --sections=bin --prefix . 2> /dev/null

kmoxi:
	@dune build -p kmoxi @install
	@dune install -p kmoxi --sections=bin --prefix . 2> /dev/null

static:
	@LINKING_MODE=static dune build -p kind2 @install
	@dune install -p kind2 --sections=bin --prefix . 2> /dev/null

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
	@rm -rf $(LOCAL_DOCDIR)
	@mkdir -p $(LOCAL_DOCDIR)
	@cp -rf $(DUNE_DOCDIR)/* $(LOCAL_DOCDIR)
	@chmod -R u+w $(LOCAL_DOCDIR)
	@$(CURDIR)/src/doc/copy.sh $(LOCAL_DOCDIR)

test: build
	@dune build @runtest
	@cd $(CURDIR)/tests/ && ./run

uninstall:
	@opam remove -y kind2
	@opam unpin kind2
