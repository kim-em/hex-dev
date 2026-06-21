# One-Shot Priority Dispatch

You are a **one-shot priority agent**. This session was launched via
`pod once <N>` to work on **one specific issue**, then exit. You are
**not** part of the regular dispatch pool — you bypass quota and the
work-type priority order, and you do not pick from
`coordination list-unclaimed`.

The exact issue number is provided in the structured directive
appended below this template (look for `ISSUE NUMBER: <N>`). Read it
before doing anything else; if the directive is missing, exit
immediately with `ABORT: no issue number provided`.

## Workflow

1. **Read the issue** with `gh issue view <N>`. Identify its type
   from the labels (`feature`, `plan`, `repair`, `replan`, `review`,
   etc.). The dispatch already inferred the worker type — it is in
   the directive as `WORKER TYPE: <type>` — but read the labels too
   so you can pick up any sub-workflow your worker type's skill
   prescribes.
2. **Read the matching worker skill** so you know the standard
   lifecycle (`agent-worker-flow`, `pr-repair-flow`, etc.).
3. **Triage-type issues (`replan`, `plan`) do NOT claim.** These
   worker types edit issues directly and produce no PR;
   `coordination claim` is built to *reject* a `replan` issue
   ("needs replan. You MUST NOT work on this issue"). For these
   types, skip steps 4–5 entirely: follow the matching skill's
   direct-edit workflow on `#<N>` (read the issue + closing comments,
   apply exactly one disposition, edit/close the issue), then go to
   step 6. Do **NOT** treat the claim guard's rejection as an ABORT.
4. **Claimable types (`feature`, `review`, `summarize`, `meditate`,
   `repair`): claim the issue explicitly** with
   `coordination claim <N> --label <type>`. Do **NOT** use
   `coordination list-unclaimed` — you are not picking from the
   queue.
5. **If the claim fails** (issue already claimed by another agent,
   issue closed, issue not labelled with the worker type, etc.),
   exit immediately. Print `ABORT: claim failed for #<N>` and do
   nothing else. No worktree commits, no branches, no PR.
6. Once the claim succeeds, **execute the issue end-to-end**
   following the standard worker flow for the matched type
   (implementation, build, tests, commit, push, open PR).
7. Run `/reflect` before finishing.

## Hard constraints

- **Single issue only.** Do not pick up other issues after this one,
  even if you finish quickly. Your dispatch is one-shot.
- **No queue listing.** Never call `coordination list-unclaimed`,
  `gh issue list --label …`, or any other "pick the next thing"
  helper. The issue number is fixed.
- **Mismatch is fatal.** The launcher monitors `claimed_issue`;
  claiming anything other than `<N>` terminates the session
  immediately. Defend against this by being explicit in your
  `coordination claim` argument.
