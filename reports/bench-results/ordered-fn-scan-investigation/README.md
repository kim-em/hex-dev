# OrderedFn shared-zero scan investigation

The source change at `5e71a30d949e8cab05bb69ee1d20241f30994d5e` replaces
only the compiled `Infinitesimal.lowestIndex` implementation. It uses Lean's
existing safe `withPtrEq` shortcut and the original structural-equality fallback.
A kernel-proved compiler-simplification equality preserves the public function
for every zero and equality dictionary. Core, semantic/conformance/native builds
pass, and its axiom guard contains only `propext` and `Quot.sound`.

The generated native loop compares the coefficient address with a cached zero
address before calling structural equality. The generated C initializer takes
that address from exactly the zero object passed to `lean_mk_array` by the
third-level fixture's preparation. This establishes a meaningful code difference
for that fixture; it is not a measured speedup or a universal sharing guarantee.

The [decision](decision.json) declares one matched-parent source-change probe
against clean parent `446b7f29910d2e2d4bbc0fa8c195b5cae830a9e7` and its retained
native executable. The probe was pinned to one automatically selected CPU, with
three fixed trial-major adjacent AB/BA blocks at four named parameters. Raw
filenames include workload, parameter, trial and arm and use exclusive creation.

**The comparison failed operationally.** The variant binary was copied with
`shutil.copyfile`, which did not preserve execute permission. Its mode was `0644`.
All 12 candidate process launches failed with permission denied before execution;
all 12 baseline commands completed. The driver journal retains every failure,
all parsed baseline observations and every stdout/stderr file. No candidate
sample or ratio exists. Do not report a performance verdict, expand this attempt,
repeat it unchanged, or replace its failed evidence. No historical regression,
phase counter or publication requirement is discharged.

[probe-summary.json](probe-summary.json) lists the exact failures. The
[manifest](manifest.json) binds retained data, source/build identities and local
native inputs. Executable bytes and generated C remain under
`/home/kim/.codex/tasks/hex-10575/orderedfn-scan-investigation`. The original
public implementation and experimental replacement remain in the frozen source
commit; this experimental change is not accepted for integration.
