# Open-issue triage

**Accomplished**

- Enumerated the repository's open GitHub issues and open pull requests.
- Cross-referenced closing PRs so issues already in review are distinguished
  from the unclaimed backlog.
- Checked claim labels, assignees, worktrees, fresh branch commits, and running
  agent processes to identify active work even where the `claimed` label is
  missing.

**Current frontier**

- There are 18 substantive open issues plus the permanent coordination
  sentinel. Three issues have active agents, five have open closing PRs, and
  ten have neither an active claim nor an open closing PR.

**Next step**

- Re-run the triage after the active Resultant/NumberField PR stack and the
  three claimed branches advance, since several statuses are changing quickly.

**Blockers**

- The documented `coordination` helper is unavailable in this checkout's
  environment, so active-agent status was reconstructed from GitHub metadata,
  worktrees, recent commits, and live processes.
