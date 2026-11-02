from pathlib import Path
import importlib.util,json,os,subprocess
repo=Path("/home/kim/worktrees/hex-dev/hex-dev-issue-10358")
spec=importlib.util.spec_from_file_location("cpu_lease",repo/"scripts/bench/cpu_lease.py")
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
cpu,lease=module.cpu_lease()
try:
 os.sched_setaffinity(0,{cpu})
 context=dict(cpu=cpu,affinity=sorted(os.sched_getaffinity(0)),host_load=os.getloadavg(),schedule=["AB","BA"],repetitions=10,depth=128,roots=8,scope="build-only admission traversal, not a source proof or whole tactic comparison")
 Path("/home/kim/.codex/tasks/hex-10358/axiom-forest-cost-context.json").write_text(json.dumps(context,indent=2)+"\n")
 raise SystemExit(subprocess.run(["lake","build","AxiomForestCost"]).returncode)
finally:lease.close()
