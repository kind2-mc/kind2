# Guidelines for user documentation

To generate the user documentation you will need `pandoc`, `pdflatex`, ocaml
and a GNU version of `sed` (`gsed` for OSX).

Simply run `make` to generate the user documentation. This will create
`doc.pdf` and `target.md`. The first is the actual pdf documentation while the
latter is the markdown file passed to `pandoc`.

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