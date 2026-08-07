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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-07-110` records
24,675 declarations, 13,260 theorem-kind declarations, 6,984 assumption-free
theorems, 14,607 excluded private declarations, 226 source-closure modules,
and 2,316 reviewed milestone candidates. Its 15,168,239 canonical bytes have
SHA-256
`2e585d493c1b5364f0bf340b7d141bbb231bef97d609056909f19481c77e45c9`;
the exact Lean source closure has SHA-256
`77155b9e3cd7ba5c931ccd20f587cb5aa0567e1b016b37845d904eec4205426d`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-07-110`
contains 90 milestones: 87 earned and three deliberately unearned. Its
750,275 bytes pin 2,316 exact kernel theorem types and have canonical-object
SHA-256
`94f46541a5e524e9b4989cf28331c74456c52d41098b5a2634c8cf2a8c11fc17`
and file SHA-256
`20d29d0d85e4edd2ee0ab1cfbe41f403e17b2655ea82651ffeb089c0fe88372b`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-110`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-07-RESIDUAL-TERMINAL-FOUR-CORNER-CARRIER-109`,
has byte-identical 1,867,836-byte status mirrors with SHA-256
`a411b2dae18d3869cea0ba236628604e9041f06010553d1e0cfc8b2434cef805`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-07-110` has a
195,614-byte TeX source with SHA-256
`51e174f1cbff5030a905ce6e791741a0f69facb1500acfad3b6b1c72ccdea641`
and a deterministic 77-page, 436,374-byte A4 PDF with SHA-256
`ed75cd52e1a5bb6a143838fa7a86f0d9a88ad66e9f1d039413fab5dc671690ad`.

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
