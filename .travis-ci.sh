# Install z3.
if [ "$TRAVIS_OS_NAME" = "linux" ]; then
  z3_version="z3-4.7.1-x64-ubuntu-14.04"
  install_dir="/usr/bin/z3"
elif [ "$TRAVIS_OS_NAME" = "osx" ]; then 
  z3_version="z3-4.7.1-x64-osx-10.11.6"
  install_dir="/usr/local/bin/z3"
fi

wget "https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/${z3_version}.zip"
unzip "${z3_version}.zip"
sudo cp "${z3_version}/bin/z3" $install_dir

# Retrieve opam.
wget -qq https://github.com/ocaml/opam/releases/download/2.0.6/opam-2.0.6-x86_64-linux
mv opam-2.0.6-x86_64-linux /usr/local/bin/opam && chmod a+x /usr/local/bin/opam
opam init --disable-sandboxing --yes --comp 4.04.0 && eval $(opam env)

# Install ocaml packages needed for Kind 2.
opam install --yes ocamlbuild ocamlfind menhir yojson

# Build the PR's Kind 2.
./autogen.sh
./build.sh --prefix=$(pwd)  # prefix installs the binary into the working directory for Travis

# Checking regression test.
make test
