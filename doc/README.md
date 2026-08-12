# Kind 2 User Documentation

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

## What changed from the Sphinx version

- **Cross-references** (`:ref:`) were resolved and converted to Hugo
  `{{< relref >}}` links.
- **Admonitions** (`.. note::` / `.. warning::`) became Hextra
  `{{< callout >}}` shortcodes.
- **Figures** became standard Markdown images with captions.
- **Math blocks** (`.. math::`) became `$$...$$` blocks, rendered client-side
  via KaTeX.
- **`csv-table` directives** became standard Markdown tables.
- Sidebar navigation is generated automatically from the `content/docs/`
  file tree and each page's `weight`, replacing Sphinx's `toctree`.
- There is no direct equivalent of Sphinx's built-in search; this site uses
  Hextra's FlexSearch integration instead.

## Deploying

Any static host works (GitHub Pages, Netlify, Vercel, Cloudflare Pages).
Update `baseURL` in `hugo.yaml` to match your production domain before
building for deployment.
