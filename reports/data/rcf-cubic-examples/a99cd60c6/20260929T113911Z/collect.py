import datetime, hashlib, json, os, platform, resource, subprocess, sys, time
from pathlib import Path
root = Path.cwd()
sys.path.insert(0, str(root / "scripts/bench"))
from cpu_lease import cpu_lease

def git(*args):
    return subprocess.check_output(["git", *args], text=True).strip()
head = git("rev-parse", "HEAD")
assert git("status", "--porcelain") == "", "commit source before measuring"
stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
out = root / "reports/data/rcf-cubic-examples" / head[:9] / stamp
out.mkdir(parents=True, exist_ok=False)
paths = ["conformance/HexRCF/RealCoefficientTactic.lean", "HexRCF/Tactic.lean", "lake-manifest.json", "lean-toolchain"]
sources = {}
for name in paths:
    data = (root / name).read_bytes()
    dest = out / "source" / name
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    sources[name] = hashlib.sha256(data).hexdigest()
(out / "source.patch").write_bytes(subprocess.check_output(["git", "diff", "HEAD^", "HEAD"]))
(out / "source.commit").write_bytes(subprocess.check_output(["git", "cat-file", "commit", "HEAD"]))
module = root / ".lake/build/lib/lean/HexRCF/RealCoefficientTactic.olean"
assert module.exists(), "validate module before measuring"
module.unlink()
cpu, lease = cpu_lease()
cmd = ["taskset", "-c", str(cpu), "lake", "build", "HexRCF.RealCoefficientTactic"]
load_before = os.getloadavg()
usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
start = time.monotonic_ns()
with (out / "build.log").open("wb") as log:
    result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT)
elapsed = (time.monotonic_ns() - start) / 1e9
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
record = {"schema": "hex-rcf-user-example-observation-v1", "source_commit": head,
          "source_parent": git("rev-parse", "HEAD^"), "source_tree": git("rev-parse", "HEAD^{tree}"),
          "source_sha256": sources, "command": cmd, "started_utc": stamp,
          "host": platform.node(), "kernel": platform.release(), "cpu": cpu,
          "load_before": load_before, "load_after": os.getloadavg(), "exit_code": result.returncode,
          "wall_seconds": elapsed, "user_seconds": usage.ru_utime - usage_before.ru_utime,
          "system_seconds": usage.ru_stime - usage_before.ru_stime,
          "largest_child_peak_rss_kib": usage.ru_maxrss, "allocated_bytes": None,
          "scope": "one fresh complete conformance-module build after dependencies were built; includes existing and three new rcf examples, axiom guards, imports, elaboration, search, kernel checks and artifact writing; not an isolated theorem timer, scaling result or Phase-4 pass"}
assert git("rev-parse", "HEAD") == head
assert all(hashlib.sha256((root/name).read_bytes()).hexdigest() == digest for name,digest in sources.items())
(out / "sample.json").write_text(json.dumps(record, indent=2) + "\n")
lease.close()
print(json.dumps({"output": str(out), **record}))
sys.exit(result.returncode)
