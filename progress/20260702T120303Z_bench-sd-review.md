**Accomplished**
- Reviewed the `bench-sd-families` branch changes around the Swinnerton-Dyer
  benchmark families, the SD figure generators, committed bench exports, and
  the headline report section.
- Checked the `scheduled-hardware` tag path through `hexbz_bench verify` and
  CI's bench verify invocation.
- Verified the report's listed SHA-256 values against the committed SD JSON
  exports.

**Current frontier**
- The main review findings are packaging/traceability issues in the report and
  figure scripts, plus one low-risk maintainability issue in the Lean prep
  fallbacks.

**Next step**
- Fix the report/figure traceability issues before merging; the Lean
  registrations and CI filter look structurally sound.

**Blockers**
- None.
