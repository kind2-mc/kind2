#!/bin/sh
set -ue

LINKING_MODE="$1"
OS="$2"
OCAML_VERSION="$3"
FLAGS=
CCLIB=

case "$LINKING_MODE" in
    dynamic)
        ;; # No extra flags needed
    static)
        case "$OS" in
            linux) # Assuming Alpine here
                CCLIB="-static -lstdc++ -lsodium";;
            macosx)
                FLAGS="-noautolink"
                NAT=$(echo $OCAML_VERSION | awk -F. '{print ($1 <= 4 || ($1 == 5 && $2 == 0)) ? "" : "nat"}')
                PTHREAD=$(echo $OCAML_VERSION | awk -F. '{print ($1 <= 4) ? "-lpthread" : ""}')
                CCLIB="-lzmq_stubs -lthreadsnat -lunix$NAT -lcamlstr$NAT -lnums $PTHREAD -lstdc++"
                LIBS="libzmq libsodium"
                for lib in $LIBS; do
                    CCLIB="$CCLIB $(pkg-config $lib --variable libdir)/$lib.a"
                done;;
            *)
                echo "No known static compilation flags for '$OS'" >&2
                exit 1
        esac;;
    *)
        echo "Invalid linking mode '$LINKING_MODE'" >&2
        exit 2
esac

echo '('
for f in $FLAGS; do echo "  $f"; done
for f in $CCLIB; do echo "  -cclib $f"; done
echo ')'
