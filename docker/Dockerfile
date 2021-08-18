FROM ocaml/opam:alpine-ocaml-4.12-flambda as builder

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
RUN wget -qq https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && tar xvf yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && cp ./yices-2.6.2/bin/yices-smt2 /bin/ \
 && rm -rf yices-* \
 && echo Success || true

# Retrieve JKind and CVC4 (required for certification)
RUN wget -qq https://github.com/loonwerks/jkind/releases/download/v4.4.2/jkind-4.4.2.zip && unzip jkind-4.4.2.zip \
 && cp ./jkind/jkind ./jkind/*.jar /bin/ \
 && rm -rf jkind* \
 && wget -qq https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt -O cvc4 \
 && mv cvc4 /bin/ \
 && chmod a+x /bin/cvc4 \
 && echo Success || true

# Install Z3 and Java (required by JKind)
RUN apk add z3 openjdk11 && adduser --disabled-password --gecos KIND2 kind2

COPY --chown=kind2:kind2 --from=builder /home/opam/kind2-build/bin/kind2 /

# Entry point.
USER kind2
ENTRYPOINT ["./kind2"]
