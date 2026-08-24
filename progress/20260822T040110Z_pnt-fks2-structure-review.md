# PNT FKS2 structural review repair

## Accomplished

- Replaced the Nat Boolean-equality proof conversion with the explicit
  `beq_iff_eq` bridge.
- Split the structural checker into cap, nonempty, chain, and final-coordinate
  predicates and added guards whose negative inputs isolate each conjunct.
- Replaced line-only failures with typed certificate/source-file/role
  coordinates, including distinct same-line Corollary 24 certificates.
- Pinned the certificate-to-source-file table in the inventory matcher and
  documented that prefix lengths are audited literals rather than values
  derived from upstream syntax.
- Reverified focused modules, aggregate conformance, the full repository,
  pinned-source inventory, static checks, trust surface, and freshness gates.

## Current frontier

- The structural family still covers exactly 21 native sites; 45 native sites,
  eight imports, and four interfaces remain pending.

## Next step

- Let automatic PR CI validate the repaired edge.

## Blockers

- None.
