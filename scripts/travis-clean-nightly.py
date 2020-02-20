# Reference:
#     https://developer.github.com/v3/repos/releases/
import os
import sys
import time
from pprint import pprint
from requests import *


BASE_URL = 'https://api.github.com/repos/{}'.format(os.getenv('TRAVIS_REPO_SLUG'))
# Argument passed during the invocation of this script to prevent unwanted overwrites
TIMESTAMP = sys.argv[1]
# Authorization is needed to delete release assets
AUTH_HEADER = {'Authorization': 'token {}'.format(os.getenv('API_KEY'))}
# Max number of retries for API requests before exiting
TIMEOUT = 10

release = {}
assets = {}


def assets_present():
    return len(assets) != 0 and all([a.get('id') is not None and a.get('name') is not None for a in assets])


# Retrieve the ID for the release by tag
# Wrap in a loop to take care of intermittent API failures
i = 0
while release.get('id') is None and i < TIMEOUT:
    release = get('{}/releases/tags/nightly'.format(BASE_URL), headers=AUTH_HEADER).json()
    time.sleep(1)
    i += 1

print('Took {} attempts to fetch the release...'.format(i))
pprint(release)


# Get all of the assets for that release
i = 0
while not assets_present() and i < TIMEOUT:
    assets = get('{}/releases/{}/assets'.format(BASE_URL, release['id']), headers=AUTH_HEADER).json()
    time.sleep(1)
    i += 1

print('Took {} attempts to fetch release assets...'.format(i))
pprint(assets)

# The OSX build may not find any assets if the Linux build had deleted them
if assets:
    # Map each asset to its ID and filter out those with the current date,
    # as these should either be kept (so the OSX build doesn't delete the Linux build's asset)
    # or overwritten (in the case that cron runs and releases a new asset on the same day)
    asset_ids = [asset['id'] for asset in assets if TIMESTAMP not in asset['name']]

    # Delete each asset individually by ID
    for asset_id in asset_ids:
        delete('{}/releases/assets/{}'.format(BASE_URL, asset_id), headers=AUTH_HEADER)
        time.sleep(1)
