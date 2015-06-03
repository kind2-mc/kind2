# Guidelines for user documentation

To generate the user documentation you will need

* `pandoc`,
* `pdflatex`,
* ocaml and
* a GNU version of `sed` (`gsed` for OSX).

Simply run `make` to generate the user documentation. This will create
`doc.pdf` and `target.md`. The first is the actual pdf documentation while the
latter is the markdown file passed to `pandoc`.

## Home and README sync

Ideally `README.md` and `doc/usr/content/Home.md` should be pretty much the same. The only difference is the path to link to other files. To maintain them in sync, run

```
make update
```

in `doc/usr/`. This copies replaces `README.md` by `Home.md` after updating all internal links with the relevant path. This also updates the license file.

Alternatively, you can also run it at the repo's top level with

```
make doc-sync
```

## Pandoc specificities

### Embedded lists

Pandoc requires a difference in indentation of 4 spaces or more to consider a list embedded in another.

```markdown
* a normal (top list) item
* another normal item with an embedded list (4 spaces):
    * embedded item 1
    * embedded item 2
* back to a top item
* following items are still part of the TOP list (not 4 spaces):
  * another top item
   * yet another one (only 3 spaces).
```

## Important files

Folder `rsc/` contains

* `template.latex`, the template used to generate the pdf, and
* `options`, the options passed to pandoc.

The latex template should be straightforwad to edit after taking a look at the
pandoc documentation. File `options` stores the pandoc *variables* and their
value. See [the pandoc readme](http://pandoc.org/README.html#templates) for
more details. Variables and their values can span over several lines, the
restriction is that any line starting with an `[a-z]` character must be
indented, except for the first one. For instance,

```
abstract:"
  This is an abstract
  spanning over several lines.
"
```

## Features

The preprocessor written in ocaml (`src/preprocess.ml`) performs some sanity checks. It

* de-ambiguates the labels of the sections,
* checks that links actually point to something,
* prevents ambiguous links between files,
* prepares everything for pandoc (**e.g.** for pictures).

Because it relies on `sed` and `grep` there are a few restrictions regarding the markdown it can handle.

## Restrictions

Sections headers must be written in the lightweight `#` syntax, not the ugly
`==` one. Also, the headers should not span on several lines. Typically:

```
# My section

## Some subsection
```

Links to sections in a different file (`[<text>](<link)`) of the documentation
must have the `](<link>)` part of the link on a single line. In addition, the
path to the file must start with `./`

```markdown
<!-- This is fine -->
See [this section](./different_file.md#some-section) for more details.
See [
  this section
](./different_file.md#some-section) for more details.

<!-- This will not go through. -->
See [this section](
  ./different_file.md#some-section
) for more details.
```

The same restrictions apply when including pictures with the `![...](...)`
syntax.

There are no restrictions for hyperlinks, since the preprocessor does nothing on them.

If you link to a file in the repo, prefer doing so with a hyperlink with the
full url to said file. Otherwise, simply include the content of the file in a
section and link to that. If you point to the file with a relative path like
`../../test/lustre/whatever.lus`, the link will be removed by pandoc in the pdf
since it does not make sense.
