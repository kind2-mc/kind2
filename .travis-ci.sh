
# Install z3.
if [ "$TRAVIS_OS_NAME" = "linux" ]; then
  z3_version="z3-4.7.1/z3-4.7.1-x64-ubuntu-14.04"
  install_dir="/usr/bin/z3"
elif [ "$TRAVIS_OS_NAME" = "osx" ]; then 
  z3_version="z3-4.7.1/z3-4.7.1-x64-osx-10.11.6"
  install_dir="/usr/local/bin/z3"
fi

wget "https://github.com/Z3Prover/z3/releases/download/${z3_version}.zip"
unzip "${z3_version}.zip"
sudo cp "${z3_version}/bin/z3" $install_dir

# Retrieve opam.
wget -qq https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin 4.04.0
export OPAMYES=1
eval $(opam config env)

# Install ocaml packages needed for Kind 2.
opam install ocamlfind camlp4 menhir yojson

# Build the PR's Kind 2.
./autogen.sh
./build.sh

# Checking regression test .
make test
