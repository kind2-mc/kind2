#!/bin/sh
set -ue

LINKING_MODE="$1"
OS="$2"
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
                CCLIB="-lzmq_stubs -lstdint_stubs -lthreadsnat -lunix -lcamlstr -lnums -lpthread -lstdc++"
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
