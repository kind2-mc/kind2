FROM ubuntu:18.04 as builder

COPY . kind2-build/

# Install build dependencies
RUN apt-get update && apt-get install -y \
    automake \
    libtool \
    pkg-config \
    unzip \
    wget

# Install opam and ocaml from GitHub (Ubuntu version causes problems)
RUN wget -qq https://github.com/ocaml/opam/releases/download/2.0.1/opam-2.0.1-x86_64-linux \
  && mv opam-2.0.1-x86_64-linux /usr/local/bin/opam && chmod a+x /usr/local/bin/opam \
  && opam init --disable-sandboxing --yes --comp 4.04.0 && eval $(opam env)

# Install ocaml packages needed for Kind 2.
RUN opam install --yes ocamlfind camlp4 menhir

# Force to use opam version of ocamlc.
ENV PATH="/root/.opam/4.04.0/bin:${PATH}"

# Retrieve Z3 binary
RUN wget -qq https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip \
 && unzip z3-4.7.1-x64-ubuntu-16.04.zip

# Retrieve Yices 2
RUN wget -qq http://yices.csl.sri.com/releases/2.6.0/yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && tar xvf yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz

# Retrieve JKind and CVC4 (required for certification)
RUN wget -qq https://github.com/agacek/jkind/releases/download/v4.0.1/jkind.zip && unzip jkind.zip
 && ./kind2-build/docker_scripts/latest_cvc4.sh

# Build Kind 2
WORKDIR kind2-build
RUN if [ -f "Makefile" ] ; then make clean \
  && rm -rf src/_build configure Makefile bin src/Makefile src/kind2.native \
  && autoreconf ; fi
RUN ./autogen.sh && ./build.sh


FROM ubuntu:18.04
# Install runtime dependencies:
# JRE (required by JKind) and libgomp1 (required by Z3)
RUN apt-get update && apt-get install -y default-jre libgomp1 \
  && rm -rf /var/lib/apt/lists/*

COPY --from=builder /z3-4.7.1-x64-ubuntu-16.04/bin/z3 /bin/
COPY --from=builder /yices-2.6.0/bin/yices-smt2 bin/
COPY --from=builder /cvc4 /bin/
COPY --from=builder /jkind/jkind /jkind/*.jar /bin/
COPY --from=builder /kind2-build/bin/kind2 /

# Entry point.
ENTRYPOINT ["./kind2"]

