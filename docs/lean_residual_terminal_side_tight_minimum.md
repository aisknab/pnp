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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-112` records
24,934 declarations, 13,352 theorem-kind declarations, 7,015 assumption-free
theorems, 14,691 excluded private declarations, 228 source-closure modules,
and 2,352 reviewed milestone candidates. Its 15,824,195 canonical bytes have
SHA-256
`10ca3467d9c899300ac9c76c84ce62f87c8157e73fc39f8af82b203a4be9a8eb`;
the exact Lean source closure has SHA-256
`3161b45bbf5468a66e86fac1cf8dd6bef3ea19b1d472c536a620695085e589d1`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-112`
contains 92 milestones: 89 earned and three deliberately unearned. Its
761,711 bytes pin 2,352 exact kernel theorem types and have canonical-object
SHA-256
`2bab8fea8dbd56ee8594ceb2c5335efa7f8dd935fb11ff00f944c4c252b239c2`
and file SHA-256
`8404f2c2b178d87c42f4501b4490286c90da593281dad2708297c22b0fbfa9df`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-112`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-OPTIMUM-COHERENCE-111`,
has byte-identical 1,901,511-byte status mirrors with SHA-256
`e0515fe3af9c24f155165f172f2f00c1bbcff21822b5479141183262cf34b8d5`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-112` has a
197,818-byte TeX source with SHA-256
`550fa4769b476b52cae5df3efa912a925b9e4c6d1460fe6a601d060e4a810f72`
and a deterministic 77-page, 437,284-byte A4 PDF with SHA-256
`0e30911e395f6054e968b2ac0de1a27cf9bb2e77a182e6744ac37407dd1de058`.

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
