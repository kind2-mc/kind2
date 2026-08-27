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
                CCLIB="-static -no-pie";;
            macosx)
                FLAGS="-noautolink"
                NAT=$(echo $OCAML_VERSION | awk -F. '{print ($1 <= 4 || ($1 == 5 && $2 == 0)) ? "" : "nat"}')
                PTHREAD=$(echo $OCAML_VERSION | awk -F. '{print ($1 <= 4) ? "-lpthread" : ""}')
                # -noautolink means every C stub archive has to be named
                # here. kind2dev_stubs is ours; the rest belong to the
                # libraries it uses. A stub added to `foreign_stubs`
                # without a line here fails only in a static build, which
                # no pull request runs.
                CCLIB="-lkind2dev_stubs -lthreadsnat -lunix$NAT -lcamlstr$NAT -lnums $PTHREAD";;
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
