# Kind 2 dependencies.
OPAM_DEPENDS="ocamlfind menhir camlp4"

sudo apt-get update -y -qq

# Install z3.
wget https://github.com/Z3Prover/z3/releases/download/z3-4.5.0/z3-4.5.0-x64-ubuntu-14.04.zip
unzip z3-4.5.0-x64-ubuntu-14.04.zip
sudo cp z3-4.5.0-x64-ubuntu-14.04/bin/z3 /usr/bin/z3

sudo apt-get install -y -qq ocaml ocaml-native-compilers

# Retrieve opam.
wget -qq https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin
export OPAMYES=1
opam switch 4.04.0
opam init
eval $(opam config env)
opam update

# Install ocaml packages needed for Kind 2.
opam install ocamlfind camlp4 menhir
opam init && eval $(opam config env)
eval $(opam config env)

# Build the PR's Kind 2.
./autogen.sh
./build.sh

# Checking regression test .
make test
