"""Source manifest for the F4 verification code, fixtures and project gates."""
from scripts.bench.sweep_freshness import Family

CHECKS = Family(
    name="hexgroebner-checks",
    include=("conformance/HexGroebner/", "conformance-fixtures/HexGroebner/",
             "HexGroebnerTheory/", "HexGroebnerTheory.lean",
             "scripts/ci/check_groebner_*", "scripts/ci/run_oracles.sh",
             "scripts/ci/test_oracle_build.py", "scripts/oracle/groebner_*",
             "scripts/oracle/test_groebner_*", "scripts/oracle/common.py",
             "scripts/bench/groebner_checks.py", "scripts/bench/groebner_capsule.py",
             "scripts/bench/test_groebner_capsule.py",
             "scripts/bench/groebner_corpus.py", "scripts/bench/groebner_corpus_report.py",
             "scripts/bench/test_groebner_corpus.py",
             "scripts/bench/test_groebner_cli_measure.py",
             "reports/bench-results/raw/f4-fixed-corpus-v2.tar.xz",
             "reports/bench-results/hexgroebner-corpus.md",
             "scripts/check_dag.py", "scripts/check_phase4.py",
             "scripts/release/check_released_manifest.py", "scripts/release/released.yml",
             "scripts/check_copyright_headers.py", "scripts/check_file_line_counts.py",
             "scripts/ci/check_bench_verify_budget.sh", "libraries.yml",
             ".github/workflows/ci.yml"),
    exclude=(),
)


def source_identity():
    """Require a clean, committed runtime/test tree and identify both manifests."""
    import hashlib
    import subprocess
    from scripts.bench.groebner_measure import FAMILY
    from scripts.bench.sweep_freshness import fingerprint, index_listing, tree_listing

    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', 'diff', '--name-only'], text=True).splitlines()
    dirty += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], text=True).splitlines()
    if any(FAMILY.matches(path) or CHECKS.matches(path) for path in dirty):
        raise ValueError('verification requires committed runtime and test sources')
    runtime, checks = tree_listing(FAMILY, commit), tree_listing(CHECKS, commit)
    if index_listing(FAMILY) != runtime or index_listing(CHECKS) != checks:
        raise ValueError('staged verification sources differ from HEAD')
    return dict(source_commit=commit, source_fingerprint=fingerprint(runtime),
                source_manifest_sha256=hashlib.sha256(runtime.encode()).hexdigest(),
                checks_fingerprint=fingerprint(checks),
                checks_manifest_sha256=hashlib.sha256(checks.encode()).hexdigest())
