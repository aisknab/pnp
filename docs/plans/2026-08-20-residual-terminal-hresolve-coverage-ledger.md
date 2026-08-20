# Checked finite HResolve coverage ledger milestone

## Objective

Replace the legacy string-only HResolve sidecar boundary with an executable,
proof-reflected finite-family coverage ledger. Classify every supplied
candidate as exact, gain, blocked, or unresolved; generate one row per supplied
candidate; and accept a NoHereditary sidecar only when the candidate list is
duplicate-free and every candidate has a positive blocker after both
constructive routes fail.

## Legacy anchor and dependency edge

The pinned manuscript's Section 22 `HResolve.GlobalHereditaryResolver` row is
described as returning an exact minimum, a strict gain, or a strong
`NoHereditary` sidecar. The current Lean `HResolveSidecarCertificate` contains
only string handles, while the historical direct-binding checker explicitly
keeps `directCheckerBindingComplete = false`. The formal dependency order is:

```text
HN leaf semantics -> HResolve -> BudgetResolve -> remaining no-lower ledger
```

M168 closed the Packet branch of the no-lower ledger. The next highest-value
bounded step is therefore the missing HResolve coverage boundary, before
BudgetResolve or global ledger composition.

## Unbounded abstraction

For an arbitrary candidate type with decidable equality, an arbitrary finite
candidate list, and arbitrary decidable exact, gain, and blocker predicates:

- compute each route in exact, gain, blocked, unresolved priority order;
- generate the route ledger mechanically by mapping over the supplied list;
- recompute `List.Nodup` rather than trust a uniqueness flag;
- scan every supplied candidate for a blocked route; and
- fail closed on any exact, gain, unresolved, or duplicate row.

There is no fixed family size, candidate fixture, rank bound, caller-supplied
route tag, or caller-supplied sidecar-success bit.

## Exact theorem interface

The route-reflection theorems characterize all four classifier outcomes. The
primary sidecar reflection theorem is:

```lean
theorem TerminalHResolveFamily.checkNoHereditarySidecar_eq_true_iff
    ... :
    family.checkNoHereditarySidecar exact gain blocked = true ↔
      family.NoHereditarySidecarAccepted exact gain blocked
```

The main bounded endpoint is:

```lean
theorem terminal_hresolve_checked_sidecar_excludes_constructive_routes
    ...
    (accepted :
      family.checkNoHereditarySidecar exact gain blocked = true) :
    ∀ candidate, candidate ∈ family.candidates →
      ¬exact candidate ∧ ¬gain candidate
```

Companion theorems prove route-ledger soundness and completeness and separate
exact-route and gain-route exclusion.

## Regression and hostile evidence

- Exercise exact, gain, blocked, and unresolved classification.
- Accept a duplicate-free all-blocked family.
- Reject exact, gain, unresolved, and duplicate families independently.
- Prove Boolean/proposition reflection and the named exclusion endpoint.
- Derive the axiom transcript from every public declaration in source order.
- Reject route-priority deletion, blocker fabrication, list-scan deletion,
  uniqueness deletion, caller-controlled tags or success flags, fixed carrier
  bounds, project axioms, `sorry`, and claim widening.

## Conservative claim boundary

The candidate family and all three decidable predicates remain supplied. The
result proves complete route coverage only for that explicit finite list and
only relative to those predicates. It does not show those inputs implement the
manuscript's governed hereditary universe, HN grammar, BWL exactness,
H-disjointness, exact-minimum semantics, strict-gain semantics, or blocker
dependency semantics.

This milestone does not discharge the full historical HResolve theorem or
flip its legacy direct-binding completion flag. It does not implement
BudgetResolve, normalization, the complete no-lower ledger, saturation, replay,
unconditional HB closure, ZeroSlack, PCCMin, encoded-size or polynomial-runtime
bounds; remove a project assumption; prove SAT in P; or prove P = NP.

## Downstream blockers

`Formal.ZeroSlack` still requires terminal construction of the governed HN
family and route predicates, semantic HResolve soundness and completeness,
BudgetResolve, every remaining no-lower row, unconditional HN/BUD closure, the
positive-residual-to-BCEL bridge, complete selector adequacy, and the final
global contradiction. `Formal.ResidualBandMinimizer`,
`Formal.PolynomialRuntimeAndCertificateBounds`, `Formal.ConcreteSAT`, and
`Formal.RootTheoremAndAxiomAudit` remain downstream and unchanged.

## Release gates

Run source-shape checks and the focused capped Atlast target first, followed by
the regression, axiom transcript, hostile Node audit, generated inventory and
publication checks, one complete capped remote verification, and one exact-head
clean reproduction. Publish through a focused draft PR, require every normal
check, merge manually, and reproduce the exact merge before performing the full
non-Lean PNPLabs publication-surface synchronization and production gates.
