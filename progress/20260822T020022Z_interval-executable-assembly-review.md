# Executable assembly review repair

## Accomplished

- Guarded the sealed `HexInterval.Executable` ordinary-import boundary against
  `import all` in both conformance and bench paths, with unit coverage.
- Made program dimension checks precede full validation in assembly and
  extension, capped scoped-binding arrays before semantic callbacks, and used
  bounded list-prefix checks for program and registration ports.
- Corrected local registration capacity to `maxArity + 1` and enforced initial
  effort limits.
- Renamed the raw encoding declaration to `ReplayFormat` and added exact
  undeclared-role, undeclared-schema, invalid-body, scoped acceptance/default
  refusal, application lookup, program rejection, extension, and resource
  boundary guards.
- Clarified that assembly owns operation/node correspondence while controller
  snapshots own program version and generation side tables.

## Current frontier

The repaired executable assembly remains a standalone checked callback layer;
the supported controller does not yet own it or correlate raw quotations with
proof events.

## Next step

Obtain fresh exact-head review and CI, then connect autonomous offer generation
to the sealed assembly without weakening the raw-quotation trust boundary.

## Blockers

None in this repair.
