# Reference:
#     https://developer.github.com/v3/repos/releases/
import os
from requests import *


BASE_URL = 'https://api.github.com/repos/{}'.format(os.getenv('TRAVIS_REPO_SLUG'))

# Authorization is needed to delete release assets
AUTH_HEADER = {'Authorization': 'token {}'.format(os.getenv('API_KEY'))}

# Retrieve the ID for the release by tag
release = get('{}/releases/tags/nightly'.format(BASE_URL)).json()

# Get all of the assets for that release
assets = get('{}/releases/{}/assets'.format(BASE_URL, release['id'])).json()

# Map each asset to its ID
asset_ids = [asset['id'] for asset in assets]

# Delete each asset individually by ID
for asset_id in asset_ids:
    delete('{}/releases/assets/{}'.format(BASE_URL, asset_id), headers=AUTH_HEADER)
