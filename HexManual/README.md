# HexManual

The Verso reference manual for the `hex` project. Each per-library
reference chapter lives in `Chapters/`; `HexManual.lean` is the aggregator
that includes them.

Prose in the chapters follows [SPEC/writing-style.md](../SPEC/writing-style.md):
plain, literal, mathematician-facing language, with a list of banned
jargon words. Read it before editing a chapter.

`lake build HexManual` *typechecks* the manual: every `{docstring}`,
`{ref}`, `#eval`/`leanOutput`, and `#guard` in the chapters is checked as
they elaborate. It does not produce a website.

To view the manual, render it to static HTML with the `hexmanual`
executable:

    lake exe hexmanual --output _out
    python3 -m http.server -d _out/html-multi   # then open localhost:8000

CI publishes the rendered manual to GitHub Pages on every push to `main`
(`.github/workflows/pages.yml`). See [PLAN/Releases.md](../PLAN/Releases.md)
for the full render-and-publish story.
