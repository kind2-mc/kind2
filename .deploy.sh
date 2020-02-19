DATE_STRING=$(date -I)

# Add a suffix to the built binary to distinguish
# OSX from Linux and prevent a race condition where
# one may overwrite another:
#   https://dev.to/hawkinjs/leveraging-travis-ci-for-continuous-deployment-to-publish-compiled-binaries-to-github-2k06
# 
if [[ -f bin/kind2 ]]; then 
  mv bin/kind2 bin/kind2-$DATE_STRING-$TRAVIS_OS_NAME
  tar -czf "kind2-$DATE_STRING-$TRAVIS_OS_NAME.tar.gz" bin/kind2-$DATE_STRING-$TRAVIS_OS_NAME
fi

# In order to update where the 'nightly' tag points to, we
# need write access to the repository:
#   http://markbucciarelli.com/posts/2019-01-26_how-to-push-to-github-from-travis-ci.html
# 
openssl aes-256-cbc -k "$TRAVIS_KEY_PASSWORD" -d -md sha256 -a -in travis_key_test.enc -out travis_key
echo "Host github.com" > ~/.ssh/config
echo "  IdentityFile  $(pwd)/travis_key" >> ~/.ssh/config
chmod 400 travis_key
git remote set-url origin "git@github.com:$TRAVIS_REPO_SLUG.git"
echo "github.com ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAQEAq2A7hRGmdnm9tUDbO9IDSwBK6TbQa+PXYPCPy6rbTrTtw7PHkccKrpp0yVhp5HdEIcKr6pLlVDBfOLX9QUsyCOV0wzfjIJNlGEYsdlLJizHhbn2mUjvSAHQqZETYP81eFzLQNnPHt4EVVUh7VfDESU84KezmD5QlWpXLmvU31/yMf+Se8xhHTvKSCZIFImWwoG6mbUoWf9nzpIoaSjB+weqqUUmpaaasXVal72J+UX2B+2RPW3RcT0eOzQgqlJL3RKrTJvdsjE3JEAvGq3lGHSZXy28G3skua2SmVi/w4yCE6gbODqnTWlg7+wC604ydGXA8VJiS5ap43JXiUFFAaQ==" > ~/.ssh/known_hosts 

# We must force-push the newly updated tag. This will then
# allow us to assign a release to it.
git tag -f nightly
git push --tags -f

# Clear all older uploaded release artifacts for the `nightly` tag
pip3 install requests
python3 scripts/travis-clean-nightly.py