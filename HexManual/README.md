# HexManual

The Verso reference manual for the `hex` project. Each per-library
reference chapter lives in `Chapters/`. `HexManual.lean` serves as the table of contents

`lake build HexManual` *typechecks* the manual: it checks every
`{docstring}`, `{ref}`, `#eval`/`leanOutput`, and `#guard` in the
chapters as they elaborate. It does not produce a website.

To view the manual, render it to static HTML with the `hexmanual`
executable:

    lake exe hexmanual --output _out
    python3 -m http.server -d _out/html-multi   # then open localhost:8000

CI publishes the rendered manual to GitHub Pages on every push to `main`
(`.github/workflows/pages.yml`). See [PLAN/Releases.md](../PLAN/Releases.md)
for the full render-and-publish process.
