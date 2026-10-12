/-
Copyright (c) 2026 PNP Labs.

Derive both selected ranges from the retained original data and terminal
trace. Each phase preserves the other cut fields. The all-state bounds
include count derivation, selection and saving, not only membership tests.
-/
import PNP.Concrete.NormalizerCutCalls

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister

theorem State.get_formula (r : State) : r.store.get (30 : Fin 36) = r.core.formula := by
  dsimp only [State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join, Store.get, Store.indexCases]

-- Keep the deep framed store opaque during bound unification.
attribute [local irreducible] State.store

private theorem clause_size_arithmetic (b : Nat) : b + (6 * b + 4) = 7 * b + 4 := by omega
private theorem clause_budget_arithmetic (b cost : Nat) :
    (6 * b + 4) + (cost + 1) = 6 * b + 5 + cost := by omega
private theorem variable_budget_arithmetic (cost : Nat) : 2 + (cost + 1) = 3 + cost := by omega

def deriveClauses : Block 36 := .seq prepareClauses (.seq (select true) saveClauses)
def clausesResult (r : State) : State := clausesSaved (selected true (clauseReady r))
def clausesSteps (r : State) : Nat := clausePrepSteps r + (selectSteps true (clauseReady r) + 1)
theorem deriveClauses_exec (r : State) :
    Exec deriveClauses r.store (clausesSteps r) (clausesResult r).store :=
  Exec.seq (prepareClauses_exec r) <|
    Exec.seq (select_exec true (clauseReady r)) (saveClauses_exec _)

theorem clausesResult_frame (r : State) :
    (clausesResult r).core.width = r.core.width ∧
    (clausesResult r).core.formula = r.core.formula ∧
    (clausesResult r).core.table = r.core.table ∧
    (clausesResult r).trace = r.trace ∧ (clausesResult r).variables = r.variables := by
  have before := clauseReady_frame r
  have after := selected_frame true (clauseReady r)
  exact ⟨after.1.trans before.1, after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1, after.2.2.2.1.trans before.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩

theorem clausesResult_canonical (r : State) (clauses : List (List CNFLiteral))
    (trace : List TraceData.Row) (formulaRead : r.core.formula = GraphQuery.clauseData clauses)
    (traceRead : r.trace = TraceData.encode trace) :
    (clausesResult r).clauses =
      SearchVertices.encodeVertices (CutSelection.selected true trace clauses.length 0) := by
  change (selected true (clauseReady r)).registers.output = _
  apply selected_output
  · rw [clauseReady_target, formulaRead, ClauseCount.count_formula]
  · exact (clauseReady_input r).trans traceRead

def clausesBound : NatPolynomial :=
  .add (.linear 6 5) (CutSelection.callBound.substitute (.linear 7 4))
theorem clausesBound_eval (bound : Nat) :
    clausesBound.eval bound = 6 * bound + 5 + CutSelection.callBound.eval (7 * bound + 4) := by
  change 6 * bound + 5 + (CutSelection.callBound.substitute (.linear 7 4)).eval bound = _
  rw [NatPolynomial.eval_substitute]
  rfl
theorem clausesSteps_bound (r : State) (bound : Nat) (h : r.store.Bounded bound) :
    clausesSteps r ≤ clausesBound.eval bound := by
  have formulaSize := Store.get_length_le r.store (30 : Fin 36) (bound := bound) h
  rw [State.get_formula] at formulaSize
  have prep : clausePrepSteps r ≤ 6 * bound + 4 :=
    Nat.le_trans (clausePrepSteps_bound r) (Nat.add_le_add_right (Nat.mul_le_mul_left 6 formulaSize) 4)
  have ready := (prepareClauses_exec r).bounded bound h
  have size : bound + clausePrepSteps r ≤ 7 * bound + 4 := by
    rw [← clause_size_arithmetic]
    exact Nat.add_le_add_left prep bound
  have readyBound := Store.bounded_mono (store := (clauseReady r).store) ready size
  have chosen := selectSteps_bound true (clauseReady r) (7 * bound + 4) readyBound
  calc
    clausesSteps r ≤ (6 * bound + 4) + (CutSelection.callBound.eval (7 * bound + 4) + 1) :=
      Nat.add_le_add prep (Nat.add_le_add_right chosen 1)
    _ = clausesBound.eval bound := by
      rw [clause_budget_arithmetic, clausesBound_eval]

def deriveVariables : Block 36 := .seq prepareVariables (.seq (select false) saveVariables)
def variablesResult (r : State) : State := variablesSaved (selected false (variableReady r))
def variablesSteps (r : State) : Nat := 2 + (selectSteps false (variableReady r) + 1)
theorem deriveVariables_exec (r : State) :
    Exec deriveVariables r.store (variablesSteps r) (variablesResult r).store :=
  Exec.seq (prepareVariables_exec r) <|
    Exec.seq (select_exec false (variableReady r)) (saveVariables_exec _)
theorem variablesResult_frame (r : State) :
    (variablesResult r).core.width = r.core.width ∧
    (variablesResult r).core.formula = r.core.formula ∧
    (variablesResult r).core.table = r.core.table ∧
    (variablesResult r).trace = r.trace ∧ (variablesResult r).clauses = r.clauses := by
  have before := variableReady_frame r
  have after := selected_frame false (variableReady r)
  exact ⟨after.1.trans before.1, after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1, after.2.2.2.1.trans before.2.2.2.1,
    after.2.2.2.2.1.trans before.2.2.2.2.1⟩

theorem variablesResult_canonical (r : State) (variables : Nat)
    (trace : List TraceData.Row) (widthRead : r.core.width = List.replicate variables true)
    (traceRead : r.trace = TraceData.encode trace) :
    (variablesResult r).variables =
      SearchVertices.encodeVertices (CutSelection.selected false trace variables 0) := by
  change (selected false (variableReady r)).registers.output = _
  exact selected_output false (variableReady r) variables trace
    ((variableReady_fields r).2.trans widthRead) ((variableReady_fields r).1.trans traceRead)

def variablesBound : NatPolynomial :=
  .add (.constant 3) (CutSelection.callBound.substitute (.linear 1 2))
theorem variablesBound_eval (bound : Nat) :
    variablesBound.eval bound = 3 + CutSelection.callBound.eval (bound + 2) := by
  change 3 + (CutSelection.callBound.substitute (.linear 1 2)).eval bound = _
  rw [NatPolynomial.eval_substitute]
  change 3 + CutSelection.callBound.eval (1 * bound + 2) = _
  rw [Nat.one_mul]
theorem variablesSteps_bound (r : State) (bound : Nat) (h : r.store.Bounded bound) :
    variablesSteps r ≤ variablesBound.eval bound := by
  have ready := (prepareVariables_exec r).bounded bound h
  have chosen := selectSteps_bound false (variableReady r) (bound + 2) ready
  calc
    variablesSteps r ≤ 2 + (CutSelection.callBound.eval (bound + 2) + 1) :=
      Nat.add_le_add_left (Nat.add_le_add_right chosen 1) 2
    _ = variablesBound.eval bound := by
      rw [variable_budget_arithmetic, variablesBound_eval]

end PNP.Concrete.NormalizerBlocks.CutDriver
