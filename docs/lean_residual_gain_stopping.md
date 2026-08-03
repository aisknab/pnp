# Global strict-gain stopping specification

`lean/PNP/ResidualGainStopping.lean` formalizes the semantic stopping edge for
the residual-gain process. For every finite direct-wire implementation, it
proves that positive residual slack exists exactly when some strictly smaller
semantically equivalent implementation exists. It also proves that zero slack,
semantic minimality, and global absence of any strict equivalent gain are
equivalent descriptions of the same endpoint condition.

This is a stopping specification, not a stopping algorithm.

## Legacy anchor

The intended route is the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at the annotated tag
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

Report §16 describes the `PCCMin` loop as repeatedly taking a verified strict
equivalent gain until its terminal reasoning establishes that no further gain
is possible. The prior Lean milestone reconstructed the separate descent and
iteration-count edge. This milestone reconstructs the semantic meaning of the
stopping condition over the entire finite direct-wire implementation space.

The manuscript's route generator, finite certificate system, and polynomial
runtime remain separate obligations. In particular, this module does not
claim that failure to find a gain in a finite candidate list establishes the
global absence premise.

## Lean interface

The exhaustive reference search already supplies
`referenceMinimumImplementation current`. The new module proves that this
implementation:

- has gate count exactly `referenceMinimum current`;
- is semantically equivalent to `current`;
- is semantically minimum; and
- has residual slack zero.

When `current` has positive residual slack, that same reference-minimum
implementation is a strict equivalent gain. This witness closes both directions
of

```text
0 < residualSlack current
  ↔ ∃ next, StrictEquivalentGain current next.
```

The complementary stopping statements are

```text
residualSlack current = 0
  ↔ ∀ next, ¬ StrictEquivalentGain current next

IsSemanticallyMinimum current
  ↔ ∀ next, ¬ StrictEquivalentGain current next.
```

Every quantifier ranges over all finite direct-wire implementations with the
same input and output widths. It is not restricted to a finite candidate list.

For a proof-bearing `StrictGainChain`, separately supplied global absence at
the endpoint proves endpoint slack zero and packages an `ExactMinimumResult`
equivalent to the starting implementation. The executable
`strictGainChainBool` form has matching zero-slack and exact-result interfaces.
The Boolean checker validates only the disclosed chain; it does not prove its
global no-gain premise.

## Trust and audit boundary

The module exposes exactly 12 public declarations: ten theorems and two
proof-producing definitions. The complete `#print axioms` transcript reports
an empty axiom closure for all 12. The hostile audit rejects altered global
quantification, weakened strictness, removal of the reference-minimum witness,
endpoint premises that no longer range over all implementations, finite-list
stopping injection, transcript drift, private or unaudited declarations,
project axioms, `Classical.choice`, `sorry`, `admit`, native evaluation,
host-side lookup, opaque caller certificates, and theorem overclaims.

Run the focused checks after building the root target:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualGainStoppingAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualGainStopping.lean
node --test audits/lean-residual-gain-stopping0.test.mjs
```

## Exact non-claims

The existence witness comes from the exhaustive semantic reference search,
which has no polynomial runtime claim. The theorem does not enumerate a
polynomial candidate family, generate the next gain, prove route completeness,
promote finite candidate-list failure to global absence, or construct the
manuscript's `ZeroSlack` certificate. It does not prove PCCMin exactness or
runtime, residual-band minimization, `CNFSAT ∈ P`, discharge any of the four
project assumptions, or prove `P = NP`.
