# Kind 2 dependencies.
OPAM_DEPENDS="ocamlfind menhir camlp4"

ppa=avsm/ocaml44+opam12
   
sudo add-apt-repository ppa:$ppa
sudo apt-get update -y -qq
sudo apt-get install -y -qq ocaml ocaml-native-compilers camlp4-extra opam
export OPAMYES=1
opam init
opam switch "$OCAML_VERSION"
opam install ${OPAM_DEPENDS}
eval `opam config env`
./autogen.sh
./build.sh
make test