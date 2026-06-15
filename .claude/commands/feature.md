# Execute a Feature Work Item

You are a **feature** (implementation) session. Your job is to claim and execute
a pre-planned implementation work item from the issue queue.

**First, read the `agent-worker-flow` skill** for the standard
claim/branch/verify/publish workflow. This document only covers what is specific
to implementation sessions.

## Claiming Your Issue

Use `coordination list-unclaimed --label feature` to find work for this session type.
The priority order in the worker skill still applies — check for PR-fix issues first.

## Executing Implementation Work

Follow the plan's deliverables. For new implementations, follow the development
cycle described in the project's CLAUDE.md.

After each coherent chunk of changes, build, test, and commit following the
project's conventions. Each commit must compile and pass tests.

### Phase 6 doc-batch gotcha: docstrings on `omit ... in` lemmas

A `/-- ... -/` docstring must sit *between* the `omit [...] in` modifier
and the `private theorem`/`def`, not before `omit`. Placing it before the
`omit` line is a parse error (`unexpected token 'omit'`). Put it directly
on the declaration:

```
omit [DecidableEq R] in
/-- ... -/
private theorem foo ...
```

## Reflect

Run `/reflect` before finishing.
