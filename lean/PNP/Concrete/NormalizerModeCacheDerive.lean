/-
Copyright (c) 2026 PNP Labs.

Compose the complete mode cache after owner construction. Save the owner
output, then reuse retained dense clauses, original matching and both
selected lists. No matching, clause compaction or selection is recomputed.
-/
import PNP.Concrete.NormalizerModeCacheState

namespace PNP.Concrete.NormalizerBlocks.ModeCacheDriver
open BitRegister

def stash : Block 36 := .action (.copy 27 8)
def stashed (r : State) : State :=
  {r with core := {r.core with core := {r.core.core with core :=
    {r.core.core.core with remaining := r.registers.output}}}}
theorem stash_exec (r : State) : Exec stash r.store 1 (stashed r).store := by
  dsimp only [stash,stashed,CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.parent,Extraction.State.registers,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact .action _ _
def loadData : Block 36 :=
  .seq (.action (.copy 10 35)) <| .seq (.action (.copy 13 28)) <|
    .seq (.action (.copy 14 34)) (.action (.copy 16 31))
def loaded (r : State) : State :=
  withMode r {modeView r with core := {(modeView r).core with
    core := {(modeView r).core.core with variables := r.variables},
    formula := literals r, remaining := r.clauses}, matching := r.core.table}
theorem loadData_exec (r : State) : Exec loadData r.store 4 (loaded r).store := by
  dsimp only [loadData,loaded,withMode,modeView,literals,OwnerCacheDriver.literals,
    PreparedDriver.graphDense,PreparedDriver.denseGraph,
    CutDriver.State.withSelection,CutDriver.State.selection,CutDriver.State.store,
    CutDriver.State.frame,MatchingDriver.State.store,MatchingDriver.State.frame,
    Search.State.store,Search.State.frame,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Extraction.State.store,
    Extraction.State.frame,Extraction.State.parent,Eligibility.State.store,
    Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    EdgeKinds.State.store,EdgeKinds.State.frame,ForwardEdge.State.store,
    ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact .seq (.action _ _) (.seq (.action _ _) (.seq (.action _ _) (.action _ _)))
def setup : Block 36 := .seq stash loadData
def ready (r : State) : State := loaded (stashed r)
theorem setup_exec (r : State) : Exec setup r.store 5 (ready r).store :=
  Exec.seq (stash_exec r) (loadData_exec (stashed r))
theorem ready_fields (r : State) :
    (modeView (ready r)).core.formula = literals r ∧
    (modeView (ready r)).core.core.variables = r.variables ∧
    (modeView (ready r)).core.remaining = r.clauses ∧
    (modeView (ready r)).matching = r.core.table := ⟨rfl,rfl,rfl,rfl⟩
theorem ready_cache (r : State) :
    owners (ready r) = r.registers.output ∧ literals (ready r) = literals r := ⟨rfl,rfl⟩
theorem ready_frame (r : State) :
    (ready r).core.width = r.core.width ∧ (ready r).core.formula = r.core.formula ∧
    (ready r).core.table = r.core.table ∧ (ready r).trace = r.trace ∧
    (ready r).clauses = r.clauses ∧ (ready r).variables = r.variables := withMode_frame (stashed r) _

def derive : Block 36 := .seq setup (liftMode CacheMode.call)
def derived (r : State) : State := withMode (ready r) (CacheMode.called (modeView (ready r)))
def deriveSteps (r : State) : Nat := 5 + CacheMode.callSteps (modeView (ready r))
theorem derive_exec (r : State) : Exec derive r.store (deriveSteps r) (derived r).store :=
  Exec.seq (setup_exec r) (liftMode_exec _ (ready r) _ _ (CacheMode.call_exec _))
theorem derived_cache (r : State) :
    owners (derived r) = r.registers.output ∧ literals (derived r) = literals r := by
  have after := withMode_cache (ready r) (CacheMode.called (modeView (ready r)))
  exact ⟨after.1.trans (ready_cache r).1,after.2.trans (ready_cache r).2⟩
theorem derived_frame (r : State) :
    (derived r).core.width = r.core.width ∧ (derived r).core.formula = r.core.formula ∧
    (derived r).core.table = r.core.table ∧ (derived r).trace = r.trace ∧
    (derived r).clauses = r.clauses ∧ (derived r).variables = r.variables := by
  have before := ready_frame r
  have after := withMode_frame (ready r) (CacheMode.called (modeView (ready r)))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,
    after.2.2.1.trans before.2.2.1,after.2.2.2.1.trans before.2.2.2.1,
    after.2.2.2.2.1.trans before.2.2.2.2.1,after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_output (r : State) (table : MatchingTable.Entries) (clauses variables : List CNFLiteral)
    (formula : List (List CNFLiteral))
    (matching : r.core.table = MatchingTable.encode table)
    (selectedClauses : r.clauses = SearchVertices.encodeVertices clauses)
    (selectedVariables : r.variables = SearchVertices.encodeVertices variables)
    (dense : literals r = GraphQuery.clauseData formula) :
    (derived r).registers.output = MatchingTable.encode (CacheMode.values table variables formula clauses 0) := by
  rw [derived,withMode_registers]
  exact CacheMode.called_canonical table variables clauses formula (modeView (ready r))
    ((ready_fields r).2.2.1.trans selectedClauses) ((ready_fields r).2.2.2.trans matching)
    ((ready_fields r).2.1.trans selectedVariables) ((ready_fields r).1.trans dense)

attribute [local irreducible] CutDriver.State.store

def deriveBound : NatPolynomial := .add (.constant 5) (CacheMode.callBound.substitute (.linear 1 5))
theorem deriveBound_eval (n : Nat) : deriveBound.eval n = 5 + CacheMode.callBound.eval (n + 5) := by
  change 5 + (CacheMode.callBound.substitute (.linear 1 5)).eval n = _
  rw [NatPolynomial.eval_substitute]
  change 5 + CacheMode.callBound.eval (1 * n + 5) = _
  rw [Nat.one_mul]
theorem deriveSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    deriveSteps r ≤ deriveBound.eval n := by
  have prepared := (setup_exec r).bounded n bounded
  have scratch := modeView_bounded (ready r) (n + 5) prepared
  have complete := CacheMode.callSteps_bound (modeView (ready r)) (n + 5) scratch
  rw [deriveBound_eval]
  exact Nat.add_le_add_left complete 5

end PNP.Concrete.NormalizerBlocks.ModeCacheDriver
