FROM ubuntu:18.04 as builder

ARG BRANCH=develop
ARG COMMIT

# Install build dependencies
RUN apt-get update && apt-get install -y \
    gcc \
    git \
    libzmq3-dev \
    m4 \
    make \
    patch \
    unzip \
    wget

# Install opam and ocaml from GitHub (Ubuntu version causes problems)
RUN wget -qq https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh && \
    echo "/usr/local/bin" | sh install.sh && \
    opam init --disable-sandboxing --yes --compiler 4.07.1 && \
    eval $(opam env)

# Force to use opam version of ocamlc.
ENV PATH="/root/.opam/4.07.1/bin:${PATH}"

# Retrieve Z3 binary
RUN wget -qq https://github.com/Z3Prover/z3/releases/download/z3-4.8.7/z3-4.8.7-x64-ubuntu-16.04.zip \
 && unzip z3-4.8.7-x64-ubuntu-16.04.zip

# Retrieve Yices 2
RUN wget -qq https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && tar xvf yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz

# Retrieve JKind and CVC4 (required for certification)
RUN wget -qq https://github.com/loonwerks/jkind/releases/download/v4.3.0/jkind-4.3.0.zip && unzip jkind-4.3.0.zip \
 && wget -qq https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt -O cvc4

# Command for DockerHub
RUN if [ -n "${COMMIT}" ] ; then \
  git clone --depth 25 --branch ${BRANCH} https://github.com/kind2-mc/kind2.git kind2-build && \
  cd kind2-build && git checkout ${COMMIT} && cd .. ; fi

COPY . kind2-build/

# Build Kind 2
WORKDIR kind2-build
RUN opam install -y .

FROM ubuntu:18.04
# Install runtime dependencies:
# JRE (required by JKind) and libgomp1 (required by Z3)
RUN apt-get update && apt-get install -y --no-install-recommends \
    default-jre \
    libgomp1 \
    libzmq5 \
    && rm -rf /var/lib/apt/lists/* \
    && adduser --disabled-password --gecos KIND2 kind2

COPY --from=builder /z3-4.8.7-x64-ubuntu-16.04/bin/z3 /bin/
COPY --from=builder /yices-2.6.2/bin/yices-smt2 bin/
COPY --from=builder /cvc4 /bin/
COPY --from=builder /jkind/jkind /jkind/*.jar /bin/
COPY --from=builder /root/.opam/4.07.1/bin/kind2 /

# Entry point.
USER kind2
ENTRYPOINT ["./kind2"]

