# Checked residual-terminal HB active-dependency closure

`lean/PNP/ResidualTerminalHBActiveDependencyClosure.lean` supplies the local
induction premise deliberately left open by the preceding total-table HB
milestone.  It checks a precise no-outcome condition over the supplied finite
tables and derives HN/BUD inactivity by the already proved exact-rank
well-foundedness.

The result is still conditional on explicit data.  It does not claim that the
activity bits or dependency rows have been constructed with the manuscript's
terminal-candidate semantics.

## Data-only activity projection

For either closed HB node,
`TerminalPacketTypedRealizerEnvironment.hbActive` reads the corresponding
existing table entry:

```text
hn(rank)     -> environment.hnActive(rank)
budget(rank) -> environment.budgetActive(rank)
```

There is no second activity table and no activity proof inside a node.

## Checked local premise

`ActiveDependencyClosed` says exactly:

```text
for every node,
  if node is active,
  then some dependency in that node's total row is active
```

`checkActiveDependencyClosed` enumerates every HN and budget node, reads the
activity bit, and scans the exact row returned by the total dependency
function.  `checkActiveDependencyClosed_eq_true_iff` proves that this Boolean
scan recognizes the proposition exactly.

The combined `checkNoOutcomeActiveClosure` also runs the earlier table checker.
Consequently, every dependency used by the local premise has already been
proved to descend the exact ten-coordinate terminal residual rank.

## Active-chain contradiction

`noActive_of_noOutcomeActiveClosure` applies the existing well-founded
dependency induction with the motive that the current node is inactive.  If a
node were active, accepted local closure would provide an active lower
dependency.  The induction hypothesis says that dependency is inactive, a
contradiction.  Therefore:

```text
forall node, environment.hbActive node = false
```

`hnActive_eq_false` and `budgetActive_eq_false` expose the two specialized
consequences.

The regression keeps the two checks independent.  A supplied active cycle can
satisfy the local active-to-active scan, but its nondecreasing edge causes the
exact-rank table checker and the combined checker to reject.

## Typed-realizer composition

`TerminalPacketTypedRealizerEvidence.hbActiveClosureSound` preserves a checked
strict gain and a faithful strictly lower-rank seed.  Its HN and budget cases
contradict the derived corresponding inactivity theorem, so those branches
cannot survive combined acceptance.

`terminalBN6_packet_typed_realizer_hb_active_dependency_closure_contract`
applies this result to every faithful canonical handle in an accepted grouped
BN6 typed-realizer table.  It returns the restricted gain-or-lower-seed result,
the exact combined validity proposition, all-node HN/BUD inactivity, and
well-foundedness of the supplied dependency relation.

## Audit surface

The source has 13 public declarations.  The source-derived axiom transcript
prints every one.  Six definitions have empty axiom closure; the seven theorem
declarations reach only Lean's standard `propext` and `Quot.sound` principles.
No audited declaration reaches `Classical.choice`, `sorryAx`, or a
project-specific axiom.

Run the focused checks with:

```text
lake build PNP.ResidualTerminalHBActiveDependencyClosure
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHBActiveDependencyClosureAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHBActiveDependencyClosure.lean
node --test audits/lean-residual-terminal-hb-active-dependency-closure0.test.mjs
```

## Boundary

The theorem establishes blocker silence only for the supplied activity and
dependency tables after their local closure and rank conditions have passed.
It does not derive blocker activity or dependency semantics from terminal
data, prove semantic dependency completeness, or construct the rank map,
selector family, faithfulness table, or realizer claims.

The accepted typed-realizer result may still be a verified gain or a faithful
strictly lower-rank seed.  Consequently this milestone does not establish
gain exclusion, lower-seed rank closure, rank-complete selector silence, the
full `HB.NegativeClosure`, unconditional ZeroSlack, PCCMin, encoded-size or
polynomial-runtime bounds, SAT in P, project-assumption removal, or P = NP.
