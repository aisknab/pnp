/-
Copyright (c) 2026 PNP Labs.

Reuse the internally derived cut's protected formula and selected lists.
Only three register copies initialize dense construction. No intermediate
packet is serialized or reparsed and no matching phase is repeated.
-/
import PNP.Concrete.NormalizerPreparedState

namespace PNP.Concrete.NormalizerBlocks.PreparedDriver
open BitRegister

def setupDense : Block 36 :=
  .seq (.action (.copy 10 35)) (.seq (.action (.copy 13 30)) (.action (.copy 14 34)))
def setupResult (r : CutDriver.State) : CutDriver.State :=
  withDense r {denseView r with core := {(denseView r).core with variables := r.variables}, formula := r.core.formula, remaining := r.clauses}
theorem setupDense_exec (r : CutDriver.State) :
    Exec setupDense r.store 3 (setupResult r).store := by
  dsimp only [setupDense, setupResult, withDense, denseView, graphDense, denseGraph,
    CutDriver.State.withSelection, CutDriver.State.selection, CutDriver.State.store,
    CutDriver.State.frame, MatchingDriver.State.store, MatchingDriver.State.frame,
    Search.State.store, Search.State.frame, Search.State.parent,
    Exploration.State.store, Exploration.State.frame, Extraction.State.store,
    Extraction.State.frame, Extraction.State.parent, Eligibility.State.store,
    Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame,
    EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store,
    ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join]
  exact .seq (.action _ _) (.seq (.action _ _) (.action _ _))
theorem setup_fields (r : CutDriver.State) :
    (denseView (setupResult r)).core.variables = r.variables ∧
    (denseView (setupResult r)).formula = r.core.formula ∧
    (denseView (setupResult r)).remaining = r.clauses := ⟨rfl,rfl,rfl⟩
theorem setup_frame (r : CutDriver.State) :
    (setupResult r).core.width = r.core.width ∧
    (setupResult r).core.formula = r.core.formula ∧
    (setupResult r).core.table = r.core.table ∧
    (setupResult r).trace = r.trace ∧
    (setupResult r).clauses = r.clauses ∧
    (setupResult r).variables = r.variables :=
  withDense_frame r _

def derive : Block 36 := .seq setupDense (liftDense DenseClauses.call)
def derived (r : CutDriver.State) : CutDriver.State :=
  withDense (setupResult r) (DenseClauses.called (denseView (setupResult r)))
def deriveSteps (r : CutDriver.State) : Nat :=
  3 + DenseClauses.callSteps (denseView (setupResult r))
theorem derive_exec (r : CutDriver.State) :
    Exec derive r.store (deriveSteps r) (derived r).store :=
  Exec.seq (setupDense_exec r)
    (liftDense_exec _ (setupResult r) _ _ (DenseClauses.call_exec _))
theorem derived_frame (r : CutDriver.State) :
    (derived r).core.width = r.core.width ∧
    (derived r).core.formula = r.core.formula ∧
    (derived r).core.table = r.core.table ∧
    (derived r).trace = r.trace ∧
    (derived r).clauses = r.clauses ∧
    (derived r).variables = r.variables := by
  have before := setup_frame r
  have after := withDense_frame (setupResult r) (DenseClauses.called (denseView (setupResult r)))
  exact ⟨after.1.trans before.1, after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1, after.2.2.2.1.trans before.2.2.2.1,
    after.2.2.2.2.1.trans before.2.2.2.2.1, after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_output (r : CutDriver.State) (formula : List (List CNFLiteral))
    (vertices selected : List CNFLiteral)
    (formulaRead : r.core.formula = GraphQuery.clauseData formula)
    (variablesRead : r.variables = SearchVertices.encodeVertices vertices)
    (clausesRead : r.clauses = SearchVertices.encodeVertices selected) :
    (derived r).registers.output = GraphQuery.clauseData (DenseClauses.value formula vertices selected) := by
  rw [derived, withDense_registers]
  exact DenseClauses.called_canonical formula vertices selected (denseView (setupResult r))
    ((setup_fields r).2.2.trans clausesRead) ((setup_fields r).1.trans variablesRead)
    ((setup_fields r).2.1.trans formulaRead)

attribute [local irreducible] CutDriver.State.store

def deriveBound : NatPolynomial :=
  .add (.constant 3) (DenseClauses.callBound.substitute (.linear 1 3))
theorem deriveBound_eval (bound : Nat) :
    deriveBound.eval bound = 3 + DenseClauses.callBound.eval (bound + 3) := by
  change 3 + (DenseClauses.callBound.substitute (.linear 1 3)).eval bound = _
  rw [NatPolynomial.eval_substitute]
  change 3 + DenseClauses.callBound.eval (1 * bound + 3) = _
  rw [Nat.one_mul]
theorem deriveSteps_bound (r : CutDriver.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    deriveSteps r ≤ deriveBound.eval bound := by
  have prepared := (setupDense_exec r).bounded bound bounded
  have scratch := denseView_bounded (setupResult r) (bound + 3) prepared
  have complete := DenseClauses.callSteps_bound (denseView (setupResult r)) (bound + 3) scratch
  rw [deriveBound_eval]
  exact Nat.add_le_add_left complete 3

end PNP.Concrete.NormalizerBlocks.PreparedDriver
