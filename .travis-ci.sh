# Kind 2 dependencies.
OPAM_DEPENDS="ocamlfind menhir camlp4"
   
# sudo -y -qq add-apt-repository ocaml opam
sudo apt-get update -qq
sudo apt-get install -y -qq ocaml ocaml-native-compilers camlp4-extra opam
export OPAMYES=1
opam init
opam switch "$OCAML_VERSION"
opam install ${OPAM_DEPENDS}
eval `opam config env`
make
make test