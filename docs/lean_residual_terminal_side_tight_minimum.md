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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-111` records
24,758 declarations, 13,298 theorem-kind declarations, 6,989 assumption-free
theorems, 14,645 excluded private declarations, 227 source-closure modules,
and 2,341 reviewed milestone candidates. Its 15,645,082 canonical bytes have
SHA-256
`ea373cfe65d8c99fab5c3896b7d594f96724a8eab2b3d2b7ddf0abdfee81aabe`;
the exact Lean source closure has SHA-256
`55b94c1f15c1003306e4efcf83469416817e29530e7eae8a25aa4948efa9d370`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-111`
contains 91 milestones: 88 earned and three deliberately unearned. Its
757,472 bytes pin 2,341 exact kernel theorem types and have canonical-object
SHA-256
`8c208bb3815b2513a3a167dd72adf77903c5a1f1d5c75e590e8064448a309737`
and file SHA-256
`8efcfb683a0aeb7f2b6884bf6374493b3e69c20f6bb5617d2e63252646b384d6`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-111`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-OPTIMUM-COMPATIBILITY-110`,
has byte-identical 1,887,604-byte status mirrors with SHA-256
`72d754abc757743f41696680d14a795d973fe86285fd93aa61ef322d65062a5f`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-111` has a
196,791-byte TeX source with SHA-256
`55ffa6aa19ba0c1c3143265d21ac3e481b05556a38f2d9b62591245078b0e492`
and a deterministic 77-page, 436,878-byte A4 PDF with SHA-256
`121978e29f6f37caf842fe8ad76c6ce7e8812bc1bbb7c018f068d5247e23e431`.

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
