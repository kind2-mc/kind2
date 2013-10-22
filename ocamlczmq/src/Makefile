# src/Makefile.  Generated from Makefile.in by configure.

# Makefile for the OCaml CZMQ library 

top_builddir = ..
SHELL = /bin/sh

OCAMLCC=$(CC) $(CFLAGS)
OCAMLC=ocamlc.opt -cc "$(OCAMLCC)"
OCAMLOPT=ocamlopt.opt -cc "$(OCAMLCC)"
LIBTOOL=$(SHELL) ../zeromq/libtool

OCAMLCCLIB=$(patsubst -l%, -cclib -l%,-lpthread )

# Compile with libtool and pack all object files into one library

all: install

czmq_stubs.o: czmq_stubs.c
	$(LIBTOOL) --tag=CC --mode=compile $(CC) $(CFLAGS) -c -g -O2 -I ../include -I `ocamlc -where` -lczmq -lzmq czmq_stubs.c -o czmq_stubs.o

libczmq_stubs.la: czmq_stubs.o
	$(LIBTOOL) --tag=CC --mode=link $(CC) $(CFLAGS) -static -g -O -o libczmq_stubs.la -rpath $(CURDIR)/../lib czmq_stubs.lo ../zeromq/src/*.lo ../czmq/src/*.lo

ZMQ.cmi: ZMQ.mli
	$(OCAMLC) -c $< 

# TODO: make this work for byte-code

# ZMQ.cmo: ZMQ.ml ZMQ.cmi
# 	$(OCAMLC) -c $<

# ZMQ.cma: ZMQ.cmo 
# 	$(OCAMLC) -a  -o $@  $< -cclib -lczmq_stubs -cclib -lpthread -cclib -lstdc++ -cclib -L$(CURDIR)/../lib

ZMQ.cmx: ZMQ.ml ZMQ.cmi
	$(OCAMLOPT) -c $<

ZMQ.cmxa: ZMQ.cmx libczmq_stubs.la
	$(OCAMLOPT) -a -o $@ $< -cclib -lczmq_stubs $(OCAMLCCLIB) -cclib -lstdc++ -cclib -L$(CURDIR)/../lib

install: libczmq_stubs.la ZMQ.cmi ZMQ.cmxa 
	$(LIBTOOL) --mode=install cp libczmq_stubs.la $(CURDIR)/../lib
	$(LIBTOOL) --finish $(CURDIR)/../lib
	cp ZMQ.cmi ZMQ.a ZMQ.cmxa ../lib

clean:
	rm -f *.[oa] *.so *.cm[ixoa] *.cmxa 








# # C compiler and flags
# CC=gcc
# CFLAGS=-g -O2 -I$(CURDIR)/../include -fPIC

# # Flags to compile the OCaml CZMQ library
# OCAMLCZMQ_LFLAGS=@OCAMLCZMQ_LFLAGS@ -L$(CURDIR)/../lib
# OCAMLCZMQ_CCOPTFLAGS=@OCAMLCZMQ_CCOPTFLAGS@ -ccopt -L$(CURDIR)/../lib 

# # OCaml compilers and flags 
# OCAMLCC=$(CC) $(CFLAGS)
# OCAMLC=ocamlc.opt -cc "$(OCAMLCC)"
# OCAMLOPT=ocamlopt.opt -cc "$(OCAMLCC)"
# OCAMLMKLIB=ocamlmklib -verbose -ocamlc "ocamlc.opt -cc $(OCAMLCC)" -ocamlopt "ocamlopt.opt -cc $(OCAMLCC)"


# all: Makefile ZMQ.cma ZMQ.cmxa
# 	mkdir -p build

# czmq_stubs.o: czmq_stubs.c
# 	$(OCAMLC) -c $< -o $@

# dll_wrap_stubs.so lib_wrap_stubs.a: czmq_stubs.o
# 	$(OCAMLMKLIB) -o _wrap_stubs $< -lczmq -lzmq $(OCAMLCZMQ_LFLAGS)

# ZMQ.cmi: ZMQ.mli
# 	$(OCAMLC) -c $< 

# ZMQ.cmo: ZMQ.ml ZMQ.cmi
# 	$(OCAMLC) -c $<

# ZMQ.cma: ZMQ.cmo dll_wrap_stubs.so
# 	$(OCAMLC) -a  -o $@  $<  -dllib -l_wrap_stubs \
# 	-cclib -lczmq -cclib -lzmq $(OCAMLCZMQ_CCOPTFLAGS)

# ZMQ.cmx: ZMQ.ml ZMQ.cmi
# 	$(OCAMLOPT) -c $<

# ZMQ.cmxa: ZMQ.cmx lib_wrap_stubs.a
# 	$(OCAMLOPT) -a -o $@ $< -cclib -l_wrap_stubs \
# 	-cclib -lczmq -cclib -lzmq  $(OCAMLCZMQ_CCOPTFLAGS)

# Remake this Makefile if configuration has changed 
Makefile: Makefile.in ../../config.status
	cd ../.. && ./config.status

../../config.status: ../../configure
	../../config.status --recheck

