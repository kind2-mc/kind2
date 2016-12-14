# Kind 2 dependencies.
OPAM_DEPENDS="ocamlfind menhir camlp4"

sudo apt-get update -y -qq

# Install z3.
git clone https://github.com/Z3Prover/z3
cd z3
./configure
cd build
make -j4
sudo make install
cd ../../

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

# Checking regression test first.
make test

# Retrieve and build Kind 2 develop.
dev_dir="kind2-dev"
git clone https://github.com/kind2-mc/kind2 $dev_dir
cd $dev_dir
./autogen.sh
./build.sh
cd ..
cp $dev_dir/bin/kind2 bin/kind2-dev

# Unimplemented.
ls bin/
