<!-- DO NOT EDIT, edit content/README.md instead -->
# Kind 2 User Documentation — Hugo + Hextra

## Structure

```
content/
  _index.md              # Homepage
  docs/
    _index.md             # Docs landing page (from home.rst)
    techniques/            # "Techniques" toctree section
    inputs-and-outputs/     # "Inputs and Outputs" toctree section
    advanced-features/       # "Advanced Features" toctree section
    license.md              # "License" toctree section
themes/hextra/            # Hextra theme, Git submodule
hugo.yaml                  # Site configuration
```

Page ordering within each section is controlled by the `weight` field in each
page's front matter, mirroring the original Sphinx `toctree` order.

## Running locally

Requires **Hugo Extended v0.146.0+**.

```bash
hugo server -D
```

Then open http://localhost:1313/.

To build the static site:

```bash
make html
```

Output goes to `public/`.

> **Note:** `make html` or `make vendor-assets` fetches FlexSearch (search) and KaTeX (math
> rendering) using `fetch-vendor-assets.sh` the first time it runs, so it needs
> normal internet access. If you're building in a network-restricted
> environment, set `params.search.enable: false`.

## Deploying

Any static host works (GitHub Pages, Netlify, Vercel, Cloudflare Pages).
`hugo.yaml` sets no `baseURL`, so Hugo defaults to `/`, which is what
`hugo server` and the PDF build want. Hugo bakes the baseURL into every asset
and cross-page link, so set `HUGO_BASEURL` to the URL the site will actually be
served from when building for deployment:

```bash
HUGO_BASEURL=https://example.org/kind2/docs/main/user/ make html
```

The website is published from the `kind2-mc/kind2-mc.github.io` repository,
which does this for you: it publishes this documentation to
<https://kind2-mc.github.io/docs/main/user> on every push to `main`, and a copy
of each release's to `docs/<version>/user` alongside it.
