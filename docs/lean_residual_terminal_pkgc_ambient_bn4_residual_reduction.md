# Finite PkgC ambient BN4 residual reduction

This milestone strengthens the exact ambient-ledger embedding into an
executable reduction theorem. The generated PkgC cancellation ledger is not
only balanced in signed mass: removing it preserves the actual BN4 residual
cell returned at every key and therefore preserves the complete residual
ledger over the ambient canonical key universe.

## Formal boundary

`ResidualTerminalPkgCAmbientBN4ResidualReduction` works over arbitrary finite
explicit ledgers and arbitrary carrier types. It proves:

- adding the same natural mass to both sides of one BN4 key preserves its
  executable residual cell;
- an exact ambient PkgC embedding therefore has the same residual cell as its
  explicit remainder at every complete key;
- concatenating those residual cells over any shared finite key universe
  preserves the complete residual ledger;
- every key occurring in the remainder occurs in the ambient canonical key
  universe;
- cancelling the ambient ledger over that universe is exactly cancelling the
  remainder over the same universe;
- if the explicit remainder is empty, the complete ambient residual ledger is
  empty.

The fail-closed classifier reuses the canonical generated-then-remainder
binding. On success it mechanically returns both the exact embedding and its
kernel-checked residual reduction; on failure it returns the serialization
inequality. It accepts no caller-provided success bit, embedding proof, or
residual equality. The candidate-derived bridge similarly constructs its
proof-bearing reduction only from the existing exact embedding.

## Deliberate non-claims

The ambient ledger, typed restoration operation, exact embedding, and explicit
remainder remain proof-bearing inputs. This milestone does not derive those
inputs from an arbitrary terminal candidate and does not prove that a
candidate-derived remainder is empty or route-producing. It does not establish
restoration semantic adequacy or complete global route silence, reconstruct
the full historical PkgC/BN6/Packet path, prove polynomial generation or
runtime, establish ZeroSlack or PCCMin, put SAT in P, remove a project
assumption, or prove P = NP.

## Evidence

The finite regression uses an explicit four-atom consumer system only as a
test fixture; the theorem source has no fixed carrier. Its ambient examples
cover canonical and reordered exact embeddings, duplicate remainder keys,
positive and negative surviving residuals, key-universe completeness, an
empty remainder, accepted and rejected fail-closed classifications, and the
generic candidate-derived constructor.

The hostile audit pins all 13 declarations and eight reviewed theorem types.
It rejects weakened balanced-mass arithmetic, altered per-key decomposition,
noncanonical ledger assembly, removed empty-remainder premises, weakened
mismatch evidence, caller-supplied computed reductions, new assumptions, and
fixed carriers.

The generated theorem inventory records every declaration, source-closure
module, axiom dependency, and reviewed milestone candidate. The generated
publication map contributes eight reviewed theorem types for this milestone.
Their current coordinates, counts, source-closure identity, and publication
identity are read directly from the canonical status and report artifacts
rather than duplicated here. Those artifacts remain fail-closed with all four
disclosed project assumptions, all five blockers, unset activation
fingerprints, and absent `PNP.Main.p_eq_np`.

```bash
lake build PNP.ResidualTerminalPkgCAmbientBN4ResidualReduction
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCAmbientBN4ResidualReductionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCAmbientBN4ResidualReduction.lean
node --test audits/lean-residual-terminal-pkgc-ambient-bn4-residual-reduction0.test.mjs
```
