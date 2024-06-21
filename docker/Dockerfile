FROM ocaml/opam:alpine-ocaml-5.2-flambda as builder

USER root

RUN apk add make m4 g++ musl-dev git \
    zeromq-dev libzmq-static libsodium-static

USER opam

COPY --chown=opam:opam . kind2-build/

# Build Kind 2
WORKDIR kind2-build

# Note: we use remote OPAM repo until local one is updated
RUN eval $(opam env) && \
    opam repo set-url default https://opam.ocaml.org && \
    opam update && opam install -y . --deps-only && \
    make static && strip bin/kind2

FROM alpine:latest

# Retrieve Yices 2
RUN wget -qq https://yices.csl.sri.com/releases/2.6.4/yices-2.6.4-x86_64-pc-linux-gnu.tar.gz \
 && tar xvf yices-2.6.4-x86_64-pc-linux-gnu.tar.gz \
 && cp ./yices-2.6.4/bin/yices-smt2 /bin/ \
 && rm -rf yices-* \
 && echo Success || true

# Retrieve JKind and cvc5 (required for certification)
RUN wget -qq https://github.com/loonwerks/jkind/releases/download/v4.5.2/jkind-4.5.2.zip && unzip jkind-4.5.2.zip \
 && cp ./jkind/jkind ./jkind/*.jar /bin/ \
 && rm -rf jkind* \
 && wget -qq https://github.com/cvc5/cvc5/releases/download/cvc5-1.1.1/cvc5-Linux-static.zip && unzip cvc5-Linux-static.zip \
 && cp ./cvc5-Linux-static/bin/cvc5 /bin \
 && rm -rf cvc5-Linux-static \
 && chmod a+x /bin/cvc5 \
 && echo Success || true

# Install Z3 and Java (required by JKind)
RUN apk add z3 openjdk11 && adduser --disabled-password --gecos KIND2 kind2

COPY --chown=kind2:kind2 --from=builder /home/opam/kind2-build/bin/kind2 /

# Entry point.
USER kind2
ENTRYPOINT ["./kind2"]
