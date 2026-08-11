# Announcement links on the aggregate README

## Accomplished

The aggregate README now lists where each library was announced, generated
from the manifest like everything else it contains.

- `released.yml` entries take an optional `announcements:` map from venue
  (`blog`, `zulip`, `linkedin`) to https URL. Filled in for `hex-lll` and
  `hex-berlekamp-zassenhaus`.
- `aggregate_readme.render_announcements` renders one line per library that
  has any, naming the component and linking the library, into a new
  marker region in `scripts/release/hex-README.md`. Venue order is fixed by
  `VENUES`, not by the manifest's key order, so the output is stable.
- `check_released_manifest.py` rejects announcements on a non-aggregated
  entry, an empty map, an unknown venue, and a non-https URL. Each rejection
  was exercised by hand against a mutated manifest.

Deliberately a section rather than a fourth table column: only a couple of
libraries are ever announced, so a column would be empty for 17 of 19 rows
and would get worse as the table grows.

## Current frontier

`feat/announcement-links`. A `--dry-run --only hex` sync reports `M
README.md` and nothing else.

## Next step

LinkedIn URLs for both libraries are not recorded yet; the field is
optional, so they drop in as a one-line manifest edit each.

## Blockers

None.
