# Kind 2 User Documentation — Hugo + Hextra

This is the Kind 2 user documentation, migrated from Sphinx (reStructuredText)
to [Hugo](https://gohugo.io) using the [Hextra](https://github.com/imfing/hextra) theme.

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
themes/hextra/            # Hextra theme — a git submodule, not committed here
assets/vendor/             # KaTeX/FlexSearch — fetched via npm, not committed here
pdf-tools/                 # PDF export (see pdf-tools/README.md)
hugo.yaml                  # Site configuration
```

Page ordering within each section is controlled by the `weight` field in each
page's front matter, mirroring the original Sphinx `toctree` order.

## Requirements

- **Hugo Extended v0.146.0+**
- **Git** (to fetch the Hextra theme, vendored as a submodule — see below)
- **curl or wget** (to fetch KaTeX/FlexSearch assets — see below; both are
  preinstalled on virtually every system already)
- **Python 3** (for PDF export only — `make` sets up a venv automatically)

## Getting the theme

The Hextra theme is **not committed to this repo** — it's a git submodule
pinned to [`v0.12.3`](https://github.com/imfing/hextra/releases), so
contributors always build against a known-good, reviewable version rather
than each pulling whatever the theme's `main` branch currently has.

Clone with the submodule in one step:

```bash
git clone --recurse-submodules <this-repo-url>
```

Or, if you already have a plain clone:

```bash
git submodule update --init --recursive
```

You don't need to remember either of these yourself day-to-day — `make html`
/ `make doc` fetch the submodule automatically if it's missing.

To update to a newer Hextra release later:

```bash
cd themes/hextra
git fetch --tags
git checkout v0.13.0   # or whichever version
cd ../..
git add themes/hextra
git commit -m "Bump Hextra to v0.13.0"
```

## Getting the KaTeX/FlexSearch assets

Hextra's math (KaTeX) and search (FlexSearch) features normally fetch their
JS/CSS from `cdn.jsdelivr.net` at build time. Instead, this repo fetches
pinned versions directly from the npm registry via `curl`/`wget` into
`assets/vendor/` on demand (`fetch-vendor-assets.sh`) rather than depending
on a CDN being reachable at build time, or committing those binary files to
git.

Like the theme, you don't need to run this yourself — `make html` / `make
doc` do it automatically the first time `assets/vendor/` is missing. To
bump the pinned versions, edit `KATEX_VERSION` / `FLEXSEARCH_VERSION` at the
top of `fetch-vendor-assets.sh`, delete `assets/vendor/`, and rebuild.

## Building

```bash
make doc     # static HTML (public/) + PDF (print/kind2-user-documentation.pdf)
make html    # just the static HTML
make pdf     # just the PDF (implies html)
make serve   # local dev server with live reload, http://localhost:1313/
make clean   # remove generated output
```

See `pdf-tools/README.md` for PDF-specific details.

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
  Hextra's FlexSearch integration instead (also fetched via npm, not
  committed — see above).

## Deploying

A GitHub Actions workflow (`.github/workflows/deploy.yml`) builds and
deploys to GitHub Pages on every push to `main` — it checks out the repo
with `submodules: recursive` so the theme is available in CI too. Enable it
under **Settings → Pages → Source → GitHub Actions** in your repo.

Any other static host works as well (Netlify, Vercel, Cloudflare Pages,
etc.) — just make sure the host's build step also fetches submodules.
Update `baseURL` in `hugo.yaml` to match your production domain before
building for deployment.
