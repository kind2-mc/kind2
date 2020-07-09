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
wget -qq https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh
echo "/usr/local/bin" | sh install.sh
opam init -y --disable-sandboxing -c $OCAML_VERSION
eval $(opam env)

# Install ocaml packages needed for Kind 2.
opam install -y . --deps-only
make build
make test
