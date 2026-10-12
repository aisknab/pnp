/-
Copyright (c) 2026 PNP Labs.

Owner-cache construction uses only the existing input-derived prepared
state. Dense literals are saved before scratch reuse; matching and selected
families remain protected. Matching and preparation are never rerun here.
-/
import PNP.Concrete.NormalizerCacheOwnerFold
import PNP.Concrete.NormalizerPreparedPolynomial

namespace PNP.Concrete.NormalizerBlocks.OwnerCacheDriver
open BitRegister
abbrev State := CutDriver.State

def literals (r : State) : BitString := r.core.core.original
def stash : Block 36 := .action (.copy 28 8)
def stashed (r : State) : State :=
  {r with core := {r.core with core := {r.core.core with original := r.registers.output}}}
theorem stash_exec (r : State) : Exec stash r.store 1 (stashed r).store := by
  dsimp only [stash, stashed, CutDriver.State.store, CutDriver.State.frame, CutDriver.State.registers,
    MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers,
    Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent,
    Exploration.State.store, Exploration.State.frame, Exploration.State.registers,
    Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers,
    Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame,
    ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame,
    ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join]
  exact .action _ _
theorem stashed_literals (r : State) : literals (stashed r) = r.registers.output := rfl
theorem withDense_literals (r : State) (after : DenseClauses.State) :
    literals (PreparedDriver.withDense r after) = literals r := rfl

def loadData : Block 36 :=
  .seq (.action (.copy 10 34)) (.seq (.action (.copy 13 31)) (.action (.copy 14 35)))
def loaded (r : State) : State :=
  PreparedDriver.withDense r {PreparedDriver.denseView r with core := {(PreparedDriver.denseView r).core with variables := r.clauses}, formula := r.core.table, remaining := r.variables}
theorem loadData_exec (r : State) : Exec loadData r.store 3 (loaded r).store := by
  dsimp only [loadData, loaded, PreparedDriver.withDense, PreparedDriver.denseView,
    PreparedDriver.graphDense, PreparedDriver.denseGraph,
    CutDriver.State.withSelection, CutDriver.State.selection, CutDriver.State.store,
    CutDriver.State.frame, MatchingDriver.State.store, MatchingDriver.State.frame,
    Search.State.store, Search.State.frame, Search.State.parent,
    Exploration.State.store, Exploration.State.frame, Extraction.State.store,
    Extraction.State.frame, Extraction.State.parent, Eligibility.State.store,
    Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame,
    EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store,
    ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join]
  exact .seq (.action _ _) (.seq (.action _ _) (.action _ _))
def setup : Block 36 := .seq stash loadData
def ready (r : State) : State := loaded (stashed r)
theorem setup_exec (r : State) : Exec setup r.store 4 (ready r).store :=
  Exec.seq (stash_exec r) (loadData_exec (stashed r))
theorem ready_fields (r : State) :
    (PreparedDriver.denseView (ready r)).formula = r.core.table ∧
    (PreparedDriver.denseView (ready r)).core.variables = r.clauses ∧
    (PreparedDriver.denseView (ready r)).remaining = r.variables := ⟨rfl,rfl,rfl⟩
theorem ready_literals (r : State) : literals (ready r) = r.registers.output := rfl
theorem ready_frame (r : State) :
    (ready r).core.width = r.core.width ∧ (ready r).core.formula = r.core.formula ∧
    (ready r).core.table = r.core.table ∧ (ready r).trace = r.trace ∧
    (ready r).clauses = r.clauses ∧ (ready r).variables = r.variables :=
  PreparedDriver.withDense_frame (stashed r) _

def derive : Block 36 := .seq setup (PreparedDriver.liftDense CacheOwner.call)
def derived (r : State) : State :=
  PreparedDriver.withDense (ready r) (CacheOwner.called (PreparedDriver.denseView (ready r)))
def deriveSteps (r : State) : Nat := 4 + CacheOwner.callSteps (PreparedDriver.denseView (ready r))
theorem derive_exec (r : State) : Exec derive r.store (deriveSteps r) (derived r).store :=
  Exec.seq (setup_exec r)
    (PreparedDriver.liftDense_exec _ (ready r) _ _ (CacheOwner.call_exec _))
theorem derived_literals (r : State) : literals (derived r) = r.registers.output :=
  (withDense_literals (ready r) _).trans (ready_literals r)
theorem derived_frame (r : State) :
    (derived r).core.width = r.core.width ∧ (derived r).core.formula = r.core.formula ∧
    (derived r).core.table = r.core.table ∧ (derived r).trace = r.trace ∧
    (derived r).clauses = r.clauses ∧ (derived r).variables = r.variables := by
  have before := ready_frame r
  have after := PreparedDriver.withDense_frame (ready r) (CacheOwner.called (PreparedDriver.denseView (ready r)))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1,after.2.2.2.1.trans before.2.2.2.1,
    after.2.2.2.2.1.trans before.2.2.2.2.1,after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_output (r : State) (table : MatchingTable.Entries) (clauses variables : List CNFLiteral)
    (matching : r.core.table = MatchingTable.encode table)
    (selectedClauses : r.clauses = SearchVertices.encodeVertices clauses)
    (selectedVariables : r.variables = SearchVertices.encodeVertices variables) :
    (derived r).registers.output = MatchingTable.encode (CacheOwner.values table clauses variables) := by
  rw [derived, PreparedDriver.withDense_registers]
  exact CacheOwner.called_canonical (PreparedDriver.denseView (ready r)) table clauses variables
    ((ready_fields r).1.trans matching) ((ready_fields r).2.1.trans selectedClauses)
    ((ready_fields r).2.2.trans selectedVariables)

attribute [local irreducible] CutDriver.State.store

def deriveBound : NatPolynomial := .add (.constant 4) (CacheOwner.callBound.substitute (.linear 1 4))
theorem deriveBound_eval (bound : Nat) :
    deriveBound.eval bound = 4 + CacheOwner.callBound.eval (bound + 4) := by
  change 4 + (CacheOwner.callBound.substitute (.linear 1 4)).eval bound = _
  rw [NatPolynomial.eval_substitute]
  change 4 + CacheOwner.callBound.eval (1 * bound + 4) = _
  rw [Nat.one_mul]
theorem deriveSteps_bound (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    deriveSteps r ≤ deriveBound.eval bound := by
  have prepared := (setup_exec r).bounded bound bounded
  have scratch := PreparedDriver.denseView_bounded (ready r) (bound + 4) prepared
  have complete := CacheOwner.callSteps_bound (PreparedDriver.denseView (ready r)) (bound + 4) scratch
  rw [deriveBound_eval]
  exact Nat.add_le_add_left complete 4

end PNP.Concrete.NormalizerBlocks.OwnerCacheDriver
