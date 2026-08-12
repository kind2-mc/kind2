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
themes/hextra/            # Hextra theme, vendored directly (not a Hugo Module)
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
hugo --minify
```

Output goes to `public/`.

> **Note:** `hugo build` fetches FlexSearch (search) and KaTeX (math
> rendering) from `cdn.jsdelivr.net` the first time it runs, so it needs
> normal internet access. If you're building in a network-restricted
> environment, set `params.search.enable: false` and
> `markup.goldmark.extensions.passthrough.enable: false` in `hugo.yaml`.

## Deploying

Any static host works (GitHub Pages, Netlify, Vercel, Cloudflare Pages).
Update `baseURL` in `hugo.yaml` to match your production domain before
building for deployment.
