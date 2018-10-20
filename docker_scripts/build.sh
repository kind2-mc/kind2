
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

# Copy Kind 2 binary
mv bin/kind2 ../
cd ..

# Retrieve Z3
wget -qq https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip
unzip z3-4.7.1-x64-ubuntu-16.04.zip
mv z3-4.7.1-x64-ubuntu-16.04/bin/z3 ./
rm -rf z3-4.7.1-x64-ubuntu-16.04.zip z3-4.7.1-x64-ubuntu-16.04/

# Retrieve Yices 2
wget -qq http://yices.csl.sri.com/releases/2.6.0/yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz
tar xvf yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz
mv yices-2.6.0/bin/yices-smt2 ./
rm -rf yices-2.6.0-x86_64-pc-linux-gnu-static-gmp.tar.gz yices-2.6.0

# Retrieve JKind and CVC4 (required for certification)
wget -qq https://github.com/agacek/jkind/releases/download/v4.0.1/jkind.zip
unzip jkind.zip && mv jkind jkind_zip && mv jkind_zip/jkind jkind_zip/*.jar ./
rm -rf jkind.zip jkind_zip
chmod a+x ./jkind*

./kind2-build/docker_scripts/latest_cvc4.sh
chmod a+x ./cvc4

# Remove Kind 2 build directory
rm -rf kind2-build

# Remove packages not required anymore
apt-get purge -y automake camlp4 libtool menhir pkg-config ocaml ocamlbuild unzip wget
apt autoremove -y

