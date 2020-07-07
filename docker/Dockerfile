FROM ubuntu:18.04 as builder

ARG BRANCH=develop
ARG COMMIT

# Install build dependencies
RUN apt-get update && apt-get install -y \
    bubblewrap \
    gcc \
    libzmq3-dev \
    m4 \
    make \
    patch \
    rsync \
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
RUN wget -qq https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip \
 && unzip z3-4.7.1-x64-ubuntu-16.04.zip

# Retrieve Yices 2
RUN wget -qq https://yices.csl.sri.com/releases/2.6.1/yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz \
 && tar xvf yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz

# Retrieve JKind and CVC4 (required for certification)
RUN wget -qq https://github.com/agacek/jkind/releases/download/v4.0.1/jkind.zip && unzip jkind.zip \
 && wget -qq https://github.com/CVC4/CVC4/releases/download/1.7/cvc4-1.7-x86_64-linux-opt -O cvc4

# Command for DockerHub
RUN if [ -n "${COMMIT}" ] ; then \
  apt-get install -y git && \
  git clone --depth 25 --branch ${BRANCH} https://github.com/kind2-mc/kind2.git kind2-build && \
  cd kind2-build && git checkout ${COMMIT} && cd .. ; fi

COPY . kind2-build/

# Build Kind 2
WORKDIR kind2-build
RUN opam install -y .

FROM ubuntu:18.04
# Install runtime dependencies:
# JRE (required by JKind) and libgomp1 (required by Z3)
RUN apt-get update && apt-get install -y default-jre libgomp1 libzmq3-dev \
  && rm -rf /var/lib/apt/lists/*

COPY --from=builder /z3-4.7.1-x64-ubuntu-16.04/bin/z3 /bin/
COPY --from=builder /yices-2.6.1/bin/yices-smt2 bin/
COPY --from=builder /cvc4 /bin/
COPY --from=builder /jkind/jkind /jkind/*.jar /bin/
COPY --from=builder /root/.opam/4.07.1/bin/kind2 /

# Entry point.
ENTRYPOINT ["./kind2"]

