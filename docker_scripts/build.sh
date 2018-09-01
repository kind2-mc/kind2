
# Update package list
apt-get update

# Install Kind 2 (build) requirements
apt-get install -y automake camlp4 libtool menhir pkg-config ocaml ocamlbuild unzip wget

# Install Z3 library dependency
apt-get install -y libgomp1

# Install JRE (required by JKind)
apt-get install -y default-jre

# Clean up the apt cache
rm -rf /var/lib/apt/lists/*

# Build Kind 2
cd kind2-build
./autogen.sh
./build.sh

# Copy Kind 2 binary and remove build directory
mv bin/kind2 ../
cd ..
rm -rf kind2-build

# Retrieve Z3
wget -qq https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip
unzip z3-4.7.1-x64-ubuntu-16.04.zip
mv z3-4.7.1-x64-ubuntu-16.04/bin/z3 bin/.
rm -rf z3-4.7.1-x64-ubuntu-16.04.zip z3-4.7.1-x64-ubuntu-16.04/

# Retrieve Yices 2
wget -qq http://yices.csl.sri.com/releases/2.6.0/yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz
tar xvf yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz
mv yices-2.6.0/bin/yices-smt2 bin/
rm -rf yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz yices-2.6.0

# Retrieve JKind and CVC4 (required for certification)
wget -qq https://github.com/agacek/jkind/releases/download/v4.0.1/jkind.zip
unzip jkind.zip && mv jkind/jkind jkind/*.jar bin/ && chmod a+x bin/jkind*
rm -rf jkind.zip jkind

wget -qq http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/cvc4-2018-08-31-x86_64-linux-opt
mv cvc4-2018-08-31-x86_64-linux-opt bin/cvc4 && chmod a+x bin/cvc4

# Remove packages not required anymore
apt-get purge -y automake camlp4 libtool menhir pkg-config ocaml ocamlbuild unzip wget
apt autoremove -y

