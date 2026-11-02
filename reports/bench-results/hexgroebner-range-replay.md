# Kernel replay of range loops across module boundaries

[leanprover/lean4#16169](https://github.com/leanprover/lean4/issues/16169)
tracks a logical-body visibility limitation affecting kernel reduction of
range loops imported through the module system. A two-iteration sum proved
with `decide +kernel` fails after `import Init.Data.Range.Basic` and succeeds
after `import all Init.Data.Range.Basic`.

The attached minimal Lake project reproduces this on the pinned
`leanprover/lean4:v4.35.0-rc3`, `v4.36.0-rc2`, and
`nightly-2026-10-30`. All failing and successful build logs are retained.
The respective public-import/control build durations are 0.668/0.429,
1.929/1.128, and 2.536/0.731 seconds. These are operational reproduction
records, not runtime benchmark results or evidence that faster F4 is
impossible in Lean.

`HexGroebner.MatrixStateReplay` uses the explicit logical-body import in its
test module. The production continuation requires no such import and does
not wait for an upstream fix. Its replay rewrites the native primitive to
its Lean model before kernel checking; this proves that concrete model
execution, rather than checking C machine code. The example's axiom audit
contains only `propext` and `Quot.sound`.

[Reproduction capsule](raw/range-loop-replay-16169.tar.gz), 27 verified
payload digests, SHA256
`2c2e65a24b7366845a78662e30583331adf2e58334ff9497932057f64621eb47`.
