#!/usr/bin/env python3
#
# Reference:
#     https://developer.github.com/v3/repos/releases/
from requests import *
​
​
# Retrieve the ID for the release by tag.
release = get('https://api.github.com/repos/kind2-mc/kind2/releases/tags/nightly').json()
release_id = release['id']
​
# Get all of the assets for that release.
assets = get('https://api.github.com/repos/kind2-mc/kind2/releases/{}/assets'.format(release_id)).json()
​
# Map each asset to its ID.
asset_ids = [asset['id'] for asset in assets]
​
# Delete each asset individually by ID.
for asset_id in asset_ids:
    delete('https://api.github.com/repos/kind2-mc/kind2/releases/assets/{}'.format(asset_id))
