# Precompiling HexPermGroup

`perm_group` calls `Kernel.certify`, and so `Group.ofGenerators`, while it
elaborates a goal. Lean runs that code natively only when the library sets
`precompileModules` and the build loads its shared libraries (`lake build` and
`lake lean` do). Otherwise it runs in the interpreter.

Measured on 2026-10-05, one process at a time, total elaboration time of a
single `perm_group` goal of the form `Nat.card (closure S) = N`:

| goal | interpreted | precompiled |
|---|---|---|
| Rubik's cube, three face turns (U, R, F) as a subgroup of `S₅₄` | 65 s | 1.4 s |
| Janko group `J₁` on 266 points | exceeds default `maxHeartbeats` | 28 s |

Each downstream user compiles and links HexPermGroup's native code once, on
their first build. In exchange, `perm_group` goals that need more than a few
seconds of Schreier-Sims become feasible under default heartbeats.
