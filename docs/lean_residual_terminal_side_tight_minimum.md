# Side-tight four-corner minimum arithmetic

`lean/PNP/ResidualTerminalSideTightMinimum.lean` reconstructs the bounded
arithmetic and no-overclaim part of legacy report §11.1,
`BN2-CoherentOptimum`. It formalizes the equation used by
`tightBasisValueEqualsDelta` and the numerical gate required by
`sideTightOnlyNoOverclaim`.

The legacy argument assigns four gate counts to a meet, left side, right side,
and join. Their value is signed:

```text
left + right - meet - join
```

For exact minima `m` and represented sizes `X`, every component has a natural
slack `epsilon = X - m`. The new Lean theorem proves the signed identity

```text
value(X) = delta + epsilon_left + epsilon_right
                   - epsilon_meet - epsilon_join.
```

Using `Int` is necessary. The constant-cut regression has full delta `-1`, so
natural subtraction would erase a valid negative result.

## What is now kernel checked

`TerminalFourCornerSizes` names all four corners explicitly. It provides:

- a signed incidence value;
- a componentwise lower-bound relation;
- the four componentwise slacks;
- exact numerical side-tightness;
- an executable Boolean recognizer; and
- `tightValue?`, which returns `none` unless all four corners are exact.

`TerminalFullFourCornerBasis` contains one
`TerminalFullCarrierRealization` for each corner.
`TerminalQuotientFourCornerBasis` contains one
`TerminalQuotientComparison` for each corner. For both modes, Lean proves that
the represented sizes lie above the existing exhaustive minima and that the
signed value equals the corresponding full or quotient delta plus the signed
slack expression.

The canonical full and quotient bases use the existing independently attained
minimum realization at each corner. Lean proves that both are numerically
side-tight and that their fail-closed values are exactly `fullDelta` and
`quotientDelta`. The combined public boundary is:

```text
PNP.DirectWire.TerminalProjectionFourCorners.
  canonical_numericallySideTight_values
```

These statements quantify every finite `TerminalProjectionFourCorners`; they
are not a list of fixed circuit or coordinate instances.

## Why the extractor is fail-closed

A raw signed value is not enough to establish side-tightness. Positive left
and meet slacks can cancel, leaving the same incidence value as the minimum
vector. The regression suite includes that exact case. `tightValue?` rejects
it because the recognizer checks meet, left, right, and join separately before
returning any value.

This is the formal no-overclaim boundary: equality of an arithmetic total does
not manufacture four exact corner witnesses.

## Proof and hostile checks

The dedicated transcript audits all 35 public declarations and eight reused
minimum and delta interfaces. Its permitted closure is limited to Lean's
`propext` and `Quot.sound`; it rejects `Classical.choice`, project axioms,
`sorry`, `admit`, native or SAT shortcuts, host lookup, and caller-supplied
certificates.

The regression covers all-zero sizes, a negative full delta, zero quotient
delta, unequal and swapped sides, keep-all projection, canonical full and
quotient bases, the exact slack identity, loose side, loose meet, loose join,
and canceling-slack rejection.

The hostile audit removes corners, changes incidence signs, replaces signed
integers with naturals, reverses a slack, substitutes arbitrary minima, accepts
non-tight values, changes canonical witnesses, and injects forbidden proof
shortcuts or overclaims. Each mutation must fail closed.

The focused commands are:

```bash
lake build PNP.ResidualTerminalSideTightMinimum
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSideTightMinimumAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSideTightMinimum.lean
node --test audits/lean-residual-terminal-side-tight-minimum0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-07-109` records
24,583 declarations, 13,218 theorem-kind declarations, 6,971 assumption-free
theorems, 14,595 excluded private declarations, 225 source-closure modules,
and 2,299 reviewed milestone candidates. Its 15,014,491 canonical bytes have
SHA-256
`d1743c46154588f40b4f04f5f1a0e02fdd043aa1b62c7f01e5c667d408357212`;
the exact Lean source closure has SHA-256
`c13bb497e99007317cf71871ac88dc94c21645caa70c82770690833f05a2494d`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-07-109`
contains 89 milestones: 86 earned and three deliberately unearned. Its
744,575 bytes pin 2,299 exact kernel theorem types and have canonical-object
SHA-256
`8f78366b3ecfcf756eddf9445028dac0bc5563eca062e222e4c29f8612ae4406`
and file SHA-256
`b628ea8684a56e748da90d753b054cce50428af9d213ff8928d0492b82f9cd1f`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-109`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-07-RESIDUAL-TERMINAL-SIDE-TIGHT-MINIMUM-108`,
has byte-identical 1,849,193-byte status mirrors with SHA-256
`a29d10e7bc211b2c919910624557941898dc1f2888eb5cd6fc10ba00a6e89abb`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-07-109` has a
194,451-byte TeX source with SHA-256
`2c4421043189beee57aaf5d2bc6e14aa27584904739dadedbdb40fda4c88555c`
and a deterministic 76-page, 435,428-byte A4 PDF with SHA-256
`3495459a678fdf52d06553ffe2bff603438f037e282b8c257711eb855a0760b3`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.

## Boundary still open

The four canonical minima are independently attained. This module does not
prove that they form one coherent four-corner basis, construct the coherent
completion required by the manuscript, maximize over a finite tight family,
or establish BN2 square legitimacy. It also does not prove SaturatePositive,
BCELReady, complete obstruction routing, ZeroSlack, PCCMin, polynomial runtime,
SAT in P, removal of a project assumption, or P = NP.

Those are separate downstream obligations. This milestone closes one named
dependency edge without treating the remaining coherence theorem as already
available.
