# Proof-bearing Budget ZeroSlack sidecar

`lean/PNP/ResidualTerminalBudgetZeroSlackSidecar.lean` replaces the three
uninterpreted strings formerly stored in `BudgetSidecarCertificate` with one
checked terminal-derived `NoBudget` boundary.

The certificate carries arbitrary natural input, gate, output, and profile
widths; one finite direct-wire candidate; its candidate-derived saturation
model; and supplied natural gate and saturated-record caps. Its
`noBudgetSidecar` field is an equation showing that the existing exhaustive
`findTerminalBudgetFeasibleSupport` search returned `none`. It is not a free
Boolean or a caller-supplied family. The existing reflection theorem therefore
excludes the recomputed budget predicate for every member of the complete
canonical terminal support-seed universe.

The former exact- and gain-soundness strings are also gone. For any explicit
seed, `BudgetSidecarCertificate.exact_route_sound` derives semantic minimality
from actual zero residual slack, and `gain_route_sound` derives a genuine
`StrictEquivalentGain` witness from actual positive residual slack. The named
endpoint, `PNP.budget_zeroslack_sidecar_checked_complete`, exposes exhaustive
budget exclusion, absence of every feasible governed support, and both route
semantics in one proposition.

## Verification

```sh
lake build PNP.ResidualTerminalBudgetZeroSlackSidecar
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPResidualTerminalBudgetZeroSlackSidecarAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPResidualTerminalBudgetZeroSlackSidecar.lean
node --test \
  audits/lean-residual-terminal-budget-zeroslack-sidecar0.test.mjs
```

The six-declaration axiom transcript uses only `propext` and `Quot.sound`. It
contains no `Classical.choice`, `sorryAx`, or project-specific axiom.

The regression instantiates a two-gate candidate with a zero-gate budget. The
exhaustive search proves that no canonical support fits. Separate exact and
gain seeds exercise the semantic route theorems non-vacuously, so those
theorems are not renamed handles hidden behind the accepted negative branch.

## Boundary

The resource caps remain supplied, and exhaustive support enumeration,
saturation, and reference minimization may be exponential. This is not the
manuscript BUD grammar, B0--B4 sidecar semantics, a polynomial budget-envelope
dynamic program, full BudgetResolve, the complete no-lower ledger,
unconditional ZeroSlack, polynomial PCCMin, SAT in P, or `P = NP`.
