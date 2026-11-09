# API documentation

This separate Lake project generates the HTML documentation of the library with
[doc-gen4](https://github.com/leanprover/doc-gen4) (tag `v4.35.0`, matching `lean-toolchain`). It is a
separate project so that the library's own `lake-manifest.json` and pins are unchanged.

From this folder:

```sh
lake update
lake exe cache get
DOCGEN_SRC=github lake build BGW:docs
```

The pages are written to `.lake/build/doc/` (open `index.html`). Documentation is generated for the
whole import closure, including the Mathlib modules the library uses, so the first run takes a while;
`lake build BGW.Tree:docs` builds the pages of one module and its imports. The generated files are
not committed; `lake-manifest.json` pins doc-gen4's own dependencies.

`DOCGEN_SRC=github` links each declaration to its source on GitHub and needs a clone whose `origin` is
the GitHub repository. In a local clone with another remote, use `DOCGEN_SRC=file` (links to local
files) instead.

Tested on 8 November 2026 from a fresh local clone: compiling doc-gen4 and the library's dependencies
took about 25 minutes the first time; `DOCGEN_SRC=file lake build BGW.Tree:docs` then produced 3,266
pages (BGW.Tree and its import closure) in about a minute.
