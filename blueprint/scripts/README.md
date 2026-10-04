# Blueprint declaration checks and source links

Run the following from the Lean project directory after building the project:

```sh
python3 blueprint/scripts/verify_lean_refs.py
```

This script extracts every `\lean{...}` name from `src/content.tex` and the
chapter files, generates a command-only Lean audit, and checks the names in the
compiled `SerreMarkov` environment. It checks the union of their transitive
axiom dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
No mathematical declarations or proofs are added. Compiler declaration metadata
supplies the source module and declaration line used by the HTML links.
The audit log, declaration metadata, input checksums, and generated audit are
saved in `blueprint/verification/`.

Work Mode can use the already documented runtime wrapper:

```sh
SERRE_MARKOV_LEAN_ROOT=/path/to/lean-4.24.0-linux \
SERRE_MARKOV_PROC_SELF_FIX=1 \
python3 blueprint/scripts/verify_lean_refs.py --lean-prefix ./tooling/with_lean.sh
```

After rendering the HTML with plasTeX, run:

```sh
python3 blueprint/scripts/build_lean_links.py --verify-links
python3 blueprint/scripts/postprocess_web.py
```

This writes only `blueprint/web/lean/`: an index resolving the Blueprint
plugin's `lean/find/#doc/DECLARATION` links, declaration JSON and JavaScript,
and line-addressable source HTML for every `SerreMarkov` module. It preserves
the rendered chapter pages and rejects audited source files that changed
since the declaration audit. Source rows retain the original line numbers.
`lean_links.json` records the number of source pages and the validation of
every declaration hyperlink in the generated Blueprint HTML.

The resolver uses a local JavaScript file, so opening its `index.html` does
not depend on JSON fetching, network services, or generated documentation
from another project. The final postprocessing step makes plugin links use
an explicit `index.html`, so they also work when opened as local files.
The whole Blueprint can optionally be served through a static HTTP server:

```sh
python3 -m http.server --directory blueprint/web 8000
```

Then open `http://localhost:8000/`. Re-run source-link generation after any
HTML regeneration that replaces the output directory.
