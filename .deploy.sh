git config --global user.email "travis@travis-ci.org"
git config --global user.name "Travis CI"
git config --global push.default simple
git tag -f nightly
git push --tags -f