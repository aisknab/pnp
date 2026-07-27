# Lean locked-NAND global candidate assembly

`lean/PNP/LockedNANDGlobalCandidates.lean` reconstructs the next bounded
dependency from Section 17 of the pinned legacy manuscript. For every
nonempty, finite, topologically typed NAND circuit, it assembles the complete
exposed baseline candidate and appends the displayed four-gate final
conjunction. The Lean kernel checks the construction for arbitrary circuit
size; this is not a repetition of a fixed small example.

## What is now constructed

Let `B = lockedBaselineCount circuit.program`. The module constructs:

| Candidate | Gates | Outputs | Meaning |
| --- | ---: | ---: | --- |
| `baselineCandidate circuit` | `B` | `B` | Every macro and prefix gate is exposed in construction order. |
| `fullCandidate circuit` | `B + 4` | `B + 1` | The same `B` baseline outputs followed by the one new final output. |

The construction starts from the exact carrier
`X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}` supplied by the preceding carrier/trace
milestone. `flattenCarrier` and `unflattenCarrier` are proved mutual inverses,
so the direct-wire input has exactly the intended typed interpretation.

For each source occurrence, the source constructor selects the corresponding
legacy macro:

- an input or earlier-gate equality uses 10 gates;
- constant zero uses 3 gates;
- constant one uses 2 gates; and
- every trace equation uses 18 gates.

`macroGateCount_report_formula` proves that the resulting macro count is
exactly the source-derived count already used by the report. The three
distinguished checks per circuit gate are then folded by a uniform nonempty
prefix candidate using exactly two gates after the first check. Lean proves
that its output is precisely the conjunction of the generated checks and that
the complete raw count equals `lockedBaselineCount`.

## Exact semantics

Every baseline output is an exposed program gate. Appending the final block
does not alter any of those outputs:

```text
full[baselineOutputEmbedding i] = baseline[i]
```

The added coordinate is proved equal to the legacy four-gate expression:

```text
full[final] = finalConjunction4 z TraceChecks T_out
            = z ∧ TraceChecks ∧ T_out
```

For a structured carrier valuation, `TraceChecks` is exactly
`tracePredicate circuit.program valuation`, and `T_out` is the declared trace
value at the circuit output gate.

Both candidates have constant-free internal NAND syntax. The construction
also proves structurally that changing only the fresh final-lock input `z`
cannot change any baseline output. This establishes the retained advanced
coordinate needed by the later branch-law proof. The same module now also
contains the following `BaselineDistinct` milestone; its separate proof and
audit boundary are documented in
[`lean_locked_nand_global_baseline_distinct.md`](./lean_locked_nand_global_baseline_distinct.md).

## What remains conditional

The preceding conditional threshold theorem asks for six fields. Candidate
assembly constructs `baselineCandidate`, `fullCandidate`, and
`initialOutputsPreserved`. The following global-distinctness milestone
constructs `baselineConditions`. At that boundary, the remaining missing
instantiations were exactly:

1. `unsatisfiableFinalZero`; and
2. `satisfiableFinalConditions`.

The later unsatisfiable-final-zero milestone discharges the first branch law,
and the
[`global semantic threshold`](./lean_locked_nand_global_semantic_threshold.md)
milestone discharges the second, packages all six fields, and derives the
typed threshold and residual bound. This candidate module alone does not
prove those later results. The encoded answer-independent polynomial builder,
report-level language link, `CNFSAT ∈ P`, NP-completeness, and `P = NP`
remain absent.

The legacy manuscript remains the reconstruction specification. If a later
Lean obligation exposes a concrete inconsistency or missing premise, that
kernel-checked conflict is the point at which an alternative construction
should be designed and documented; no axiom, `sorry`, caller certificate, or
weakened theorem is used to force the manuscript route through.

## Audit and regression boundary

The complete module transcript covers all 64 public declarations exactly
once. Three declarations have empty axiom closure, two use only `propext`,
and 59
use only `propext` plus `Quot.sound`. None uses `Classical.choice`, a project
axiom, `sorry`, `admit`, native/SAT shortcuts, host-side lookup, or a caller
certificate.

The regression includes input and earlier-gate equality sources, constant
zero and one sources, one- and two-gate circuits, exact macro/prefix/baseline
counts, the `B/B` and `B+4/B+1` dimensions, preservation of every baseline
output, both final truth branches, constant-free internal syntax, and
baseline independence from `z`.

## Generated publication artifacts at the candidate-assembly milestone

The compiled environment records inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-07-26-85`: 12,233 declarations, 7,146
theorems, 3,669 assumption-free theorems, 4,738 excluded private
declarations, 105 source-closure modules, and 1,963 reviewed milestone
candidates. Its 11,164,112 canonical bytes have SHA-256
`72261ed03643251129b75a87b8248c861d96a0d9badfd9d8783f90de7221fca9`;
the Lean source-closure SHA-256 is
`d2cf588681499eef5328b85fba8965097fae5dbacdd0d4efe766c7b5d48277e9`.

Publication map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-07-26-85` has
65 milestones, of which 62 are earned and the same three global milestones
remain unearned, plus 1,963 exact kernel-type fingerprints. Its canonical
reviewed-object fingerprint is
`6315b731e1271fdf8e62e5bcc45a0bb3b856d14a7f004df9e79803971203d30f`.
Its 643,074 file bytes have SHA-256
`63022a0afe898f61545175159f82d1deadd504b5d620ccb6d3c83bdc4e5b9d50`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-26-85` has
1,573,868 bytes and SHA-256
`a1bb49bb850ec6032b1e6ccff8aee14e040acb69ccb911f7f4db24407b4300aa`.
The generated report coordinate is
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-07-26-85`; its 150,935-byte
TeX has SHA-256
`aab2c1f23f08dbc2a5cd2073e45c9755abdc27f49d9578394bbedd1a1569b6ea`,
and its 62-page, 402,202-byte PDF has SHA-256
`3e1e2a6ed161f4d886abb3957bf69b6bcf8ec2aba96731903e0950f1fcb7afd2`.

All five activation fingerprints remain unset, all four project assumptions
and six blockers remain, `PNP.Main.p_eq_np` remains absent, and the concrete
publication gate remains false.
