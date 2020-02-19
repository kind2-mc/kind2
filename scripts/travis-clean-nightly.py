# Reference:
#     https://developer.github.com/v3/repos/releases/
import os
import sys
import time

from requests import *


BASE_URL = 'https://api.github.com/repos/{}'.format(os.getenv('TRAVIS_REPO_SLUG'))
# Argument passed during the invocation of this script to prevent unwanted overwrites
TIMESTAMP = sys.argv[1]
# Authorization is needed to delete release assets
AUTH_HEADER = {'Authorization': 'token {}'.format(os.getenv('API_KEY'))}

# Retrieve the ID for the release by tag
release = get('{}/releases/tags/nightly'.format(BASE_URL)).json()
time.sleep(1)

# Get all of the assets for that release
assets = get('{}/releases/{}/assets'.format(BASE_URL, release['id'])).json()
time.sleep(1)

# Map each asset to its ID and filter out those with the current date,
# as these should either be kept (so the OSX build doesn't delete the Linux build's asset)
# or overwritten (in the case that cron runs and releases a new asset on the same day)
asset_ids = [asset['id'] for asset in assets if TIMESTAMP not in asset['name']]

# Delete each asset individually by ID
for asset_id in asset_ids:
    delete('{}/releases/assets/{}'.format(BASE_URL, asset_id), headers=AUTH_HEADER)
    time.sleep(1)
