# Residual terminal HB selector-silence closure milestone

## Legacy anchor

The pinned manuscript's Section 15 Selector-silence induction follows
`HB.NegativeClosure`.  At the least rank of a faithful selector, a typed
realizer result can be only a verified gain, an active HN blocker, an active
budget blocker, or a faithful strictly lower-rank selector.  Global gain
exclusion removes the first branch, checked HB active-dependency closure
removes the next two, and the last branch contradicts least-rank induction.
This milestone reconstructs that rank induction over the existing checked
finite tables.

## Unbounded abstraction

The result ranges over every direct-wire input and output arity, every
arbitrary finite grouped BN6 family, every positive or empty finite rank
carrier admitted by the selector type, every supplied rank and faithfulness
table, every supplied typed-realizer claim table, and every supplied total
HN/BUD dependency table.  Fixed three-rank examples are regression fixtures
only; no fixed rank, selector, packet, or circuit coordinate occurs in the
theorem interface.

## Objective

Assume semantic exclusion of every `StrictEquivalentGain` from the current
implementation.  Combine an accepted exhaustive faithful-row realizer table
with the accepted checked HB active-dependency closure.  Use strong induction
on the supplied finite selector rank to prove that every canonical selector's
faithfulness bit is false.  Also expose a bridge from the existing explicit
Packet gain-coverage certificate and exhaustive source-cell no-gain evidence
to the same all-selector conclusion.

## Exact theorem boundary

The central conclusion is:

```text
(forall next, not StrictEquivalentGain current next)
-> realizerTable.checkFaithful = true
-> dependencyTable.checkNoOutcomeActiveClosure
     realizerTable.environment = true
-> forall handle,
     realizerTable.environment.faithful handle = false
```

The canonical contract retains the checked dependency-table validity,
all-node HN/BUD inactivity, and well-founded dependency relation alongside
the all-handle selector-silence conclusion.  A second theorem derives the
global no-gain premise only from the already-defined explicit gain-coverage
certificate plus exact source-cell no-gain evidence.

## Regression and hostile evidence

- Exercise the theorem over an arbitrary canonical family interface, without
  fixing its rank count or payload coordinates.
- Verify that a valid gain branch contradicts the semantic no-gain premise.
- Verify that HN and budget branches are eliminated only through the checked
  active-dependency closure.
- Verify that a lower-seed branch invokes strong induction at its strictly
  smaller finite rank and cannot be replaced by global list silence.
- Exercise the gain-coverage bridge and the complete canonical contract.
- Audit every public declaration and reject omitted global gain exclusion,
  weakened strict rank descent, non-exhaustive handle coverage, retained
  faithful branches, assumptions, fixed ranks, shortcuts, and theorem-name
  overclaims.

## Conservative claim boundary

The global no-gain proposition is an explicit proof-bearing premise.  Its
gain-coverage specialization still consumes the existing explicit global
coverage certificate and supplied source-cell no-gain evidence.  The grouped
family, selector ranks, faithfulness bits, typed claims, activity bits,
dependency rows, and finite-to-exact rank map remain supplied inputs.  The
result does not construct selectors or claims from terminal data, prove
selector faithfulness or compatibility, derive gain exclusion from ordinary
family-local silence, establish blocker semantics or semantic dependency
completeness, or derive the activity/dependency tables from sidecars.

Consequently this milestone proves rank-complete silence only for the supplied
checked finite interface under explicit semantic gain exclusion.  It does not
yet prove the unconditional manuscript `HB.NegativeClosure`, complete route
silence, unconditional ZeroSlack, polynomial PCCMin, encoded-size or runtime
bounds, SAT in P, project-assumption removal, or P = NP.

## Release gates

Run the focused Lean build, axiom transcript, regression, and hostile Node
audit first.  Then reconcile the compiled inventory, publication map, formal
status, canonical report, durable workflow, and all derived expectations.
Require the full capped remote suite, a focused draft PR, every normal check,
manual merge, and fresh exact-merge reproduction before the corresponding
full-site PNPLabs publication and production gates.
