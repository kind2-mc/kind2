FROM ubuntu:18.04
LABEL maintainer="Cesare Tinelli <cesare-tinelli@uiowa.edu>"

COPY . kind2-build/

# Build Kind 2 binary and retrieve third-party binaries (Z3, JKind, CVC4)
RUN kind2-build/docker_scripts/build.sh

# Entry point
ENTRYPOINT ["./kind2"]
