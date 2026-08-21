# Proof-bearing HResolve ZeroSlack sidecar

`lean/PNP/ResidualTerminalHResolveZeroSlackSidecar.lean` replaces the three
uninterpreted strings formerly stored in `HResolveSidecarCertificate` with a
checked finite-family proposition and semantic route proofs.

The certificate carries an arbitrary candidate type, duplicate-checking and
route-predicate decision procedures, a finite `TerminalHResolveFamily`, an
implementation map, and exact, gain, and blocker predicates.  Its
`noHereditarySidecar` field is an equation showing that the existing
`checkNoHereditarySidecar` computation returned `true`; it is not a free
Boolean.  The checker therefore recomputes candidate uniqueness and requires
every governed candidate to be blocked after both constructive predicates
fail.

The remaining two former string fields are now theorems.  An exact predicate
must imply `IsSemanticallyMinimum` for the mapped implementation, and a gain
predicate must produce an actual `StrictEquivalentGain` witness.  The named
endpoint, `PNP.hresolve_zeroslack_sidecar_checked_complete`, exposes unique
coverage, exact/gain exclusion, positive blocking, and both semantic route
bindings in one proposition.

## Verification

```sh
lake build PNP.ResidualTerminalHResolveZeroSlackSidecar
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPResidualTerminalHResolveZeroSlackSidecarAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPResidualTerminalHResolveZeroSlackSidecar.lean
node --test \
  audits/lean-residual-terminal-hresolve-zeroslack-sidecar0.test.mjs
```

The eight-declaration axiom transcript contains three empty closures and five
closures using only `propext` and `Quot.sound`.  It contains no
`Classical.choice`, `sorryAx`, or project-specific axiom.

The regression instantiates a checked two-candidate blocked family.  It also
exercises a real zero-gate semantic minimum and a real strict equivalent gain
outside that accepted family, showing that the certificate's route predicates
are semantically bound rather than renamed strings.  Duplicate, exact, gain,
and unresolved candidate rows all make the underlying NoHereditary checker
reject.

## Boundary

The family, implementation map, exact/gain/blocker predicates, and blocker
semantics remain supplied inputs.  This is a proof-bearing HResolve-to-
ZeroSlack interface, not terminal candidate derivation, the HN grammar, BWL,
ParseOrExit, leaf tightness, the H0--H4 sidecar semantics, full or polynomial
HResolve, the complete no-lower ledger, unconditional ZeroSlack, polynomial
PCCMin, concrete SAT in P, or `P = NP`.
