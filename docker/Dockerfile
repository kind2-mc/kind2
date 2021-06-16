FROM ocaml/opam:ubuntu-21.04-ocaml-4.12 as builder

USER root

RUN apt-get update && apt-get install -y \
    gcc \
    git \
    libzmq3-dev \
    m4 \
    make \
    patch \
    unzip \
    wget

USER opam

# Create directory for external tools (Yices 2, JKind, CVC4)
RUN mkdir ./tools

# Retrieve Yices 2
RUN wget -qq https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && tar xvf yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && cp ./yices-2.6.2/bin/yices-smt2 ./tools/ \
 && echo Success || true

# Retrieve JKind and CVC4 (required for certification)
RUN wget -qq https://github.com/loonwerks/jkind/releases/download/v4.3.0/jkind-4.3.0.zip && unzip jkind-4.3.0.zip \
 && cp ./jkind/jkind ./jkind/*.jar ./tools/ \
 && wget -qq https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt -O cvc4 \
 && cp cvc4 ./tools/ \
 && echo Success || true

COPY --chown=opam:opam . kind2-build/

# Build Kind 2
WORKDIR kind2-build

# Note: we use remote OPAM repo until local one is updated
RUN eval $(opam env) && \
    opam repo set-url default https://opam.ocaml.org && \
    opam update && opam install -y . --deps-only && \
    make && strip bin/kind2

FROM ubuntu:20.04
# Install runtime dependencies:
# JRE (required by JKind)
RUN apt-get update && apt-get install -y --no-install-recommends \
    default-jre \
    libzmq5 \
    z3 \
    && rm -rf /var/lib/apt/lists/* \
    && adduser --disabled-password --gecos KIND2 kind2

COPY --chown=kind2:kind2 --from=builder /home/opam/tools /bin/
COPY --chown=kind2:kind2 --from=builder /home/opam/kind2-build/bin/kind2 /

# Entry point.
USER kind2
ENTRYPOINT ["./kind2"]
