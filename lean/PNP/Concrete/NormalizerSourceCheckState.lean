/-
Copyright (c) 2026 PNP Labs.

Protect the computed candidate before using scratch registers for clause
search. The search leaves dimensions, all source-cache tables and original
cut data intact for both output branches.
-/
import PNP.Concrete.NormalizerFirstFailureCall
import PNP.Concrete.NormalizerSourceCandidatePolynomial

namespace PNP.Concrete.NormalizerBlocks.SourceCheck
open BitRegister
open SourceCandidate (bitsView withBits bitsView_bounded liftBits liftBits_exec)
abbrev State := CutDriver.State
attribute [local irreducible] FirstFailure.called
def candidate (r : State) : BitString := r.selection.remaining
def save : Block 36 := .action (.copy 22 8)
def saved (r : State) : State := r.withSelection {r.selection with remaining := r.registers.output}
theorem save_exec (r : State) : Exec save r.store 1 (saved r).store := by
  rw [saved,CutDriver.State.withSelection_store,CutDriver.State.selection_store]
  dsimp only [CutSelection.State.store,CutSelection.State.frame,ParentQuery.State.store,
    ParentQuery.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact .action _ _
theorem saved_frame (r : State) :
    (saved r).core.width = r.core.width ∧ (saved r).core.formula = r.core.formula ∧
    (saved r).core.table = r.core.table ∧ (saved r).trace = r.trace ∧
    (saved r).clauses = r.clauses ∧ (saved r).variables = r.variables :=
  CutDriver.withSelection_frame r _

def loadData : Block 36 :=
  .seq (.action (.copy 13 28)) (.seq (.action (.copy 16 22)) (.action (.copy 19 24)))
def readyBits (r : State) : FirstFailure.State :=
  ⟨⟨{(bitsView r).core.core with formula := SourceCacheDriver.literals r},
    candidate r,(bitsView r).core.counter,(bitsView r).core.target⟩,
    SourceCacheDriver.rows r,(bitsView r).counter,(bitsView r).buffer⟩
def ready (r : State) : State := withBits r (readyBits r)
theorem loadData_exec (r : State) : Exec loadData r.store 3 (ready r).store := by
  dsimp only [loadData,ready,readyBits,bitsView,withBits,candidate,ModeCacheDriver.modeView,
    SourceCacheDriver.literals,SourceCacheDriver.rows,ModeCacheDriver.literals,OwnerCacheDriver.literals,
    PreparedDriver.graphDense,PreparedDriver.denseGraph,CutDriver.State.withSelection,
    CutDriver.State.selection,CutDriver.State.store,CutDriver.State.frame,
    MatchingDriver.State.store,MatchingDriver.State.frame,Search.State.store,Search.State.frame,
    Search.State.parent,Exploration.State.store,Exploration.State.frame,Extraction.State.store,
    Extraction.State.frame,Extraction.State.parent,Eligibility.State.store,Eligibility.State.frame,
    ParentQuery.State.store,ParentQuery.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def prepare : Block 36 := .seq save loadData
def prepared (r : State) : State := ready (saved r)
theorem prepare_exec (r : State) : Exec prepare r.store 4 (prepared r).store :=
  Exec.seq (save_exec r) (loadData_exec (saved r))
theorem prepared_fields (r : State) :
    (bitsView (prepared r)).core.core.formula = SourceCacheDriver.literals r ∧
    (bitsView (prepared r)).core.matching = r.registers.output ∧
    (bitsView (prepared r)).remaining = SourceCacheDriver.rows r ∧
    candidate (prepared r) = r.registers.output := ⟨rfl,rfl,rfl,rfl⟩
theorem prepared_frame (r : State) :
    (prepared r).core.width = r.core.width ∧ (prepared r).core.formula = r.core.formula ∧
    (prepared r).core.table = r.core.table ∧ (prepared r).trace = r.trace ∧
    (prepared r).clauses = r.clauses ∧ (prepared r).variables = r.variables := by
  have before := saved_frame r
  have after := SourceCandidate.withBits_frame (saved r) (readyBits (saved r))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,after.2.2.1.trans before.2.2.1,
    after.2.2.2.1.trans before.2.2.2.1,after.2.2.2.2.1.trans before.2.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem prepared_cache (r : State) :
    SourceCacheDriver.columns (prepared r) = SourceCacheDriver.columns r ∧
    SourceCacheDriver.rows (prepared r) = SourceCacheDriver.rows r ∧
    SourceCacheDriver.slots (prepared r) = SourceCacheDriver.slots r ∧
    SourceCacheDriver.modes (prepared r) = SourceCacheDriver.modes r ∧
    SourceCacheDriver.owners (prepared r) = SourceCacheDriver.owners r ∧
    SourceCacheDriver.literals (prepared r) = SourceCacheDriver.literals r :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def derive : Block 36 := .seq prepare (liftBits FirstFailure.call)
def derived (r : State) : State := withBits (prepared r) (FirstFailure.called (bitsView (prepared r)))
def deriveSteps (r : State) : Nat := 4 + FirstFailure.callSteps (bitsView (prepared r))
theorem derive_exec (r : State) : Exec derive r.store (deriveSteps r) (derived r).store :=
  Exec.seq (prepare_exec r) (liftBits_exec _ (prepared r) _ _ (FirstFailure.call_exec _))
theorem derived_frame (r : State) :
    (derived r).core.width = r.core.width ∧ (derived r).core.formula = r.core.formula ∧
    (derived r).core.table = r.core.table ∧ (derived r).trace = r.trace ∧
    (derived r).clauses = r.clauses ∧ (derived r).variables = r.variables := by
  have before := prepared_frame r
  have after := SourceCandidate.withBits_frame (prepared r) (FirstFailure.called (bitsView (prepared r)))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,after.2.2.1.trans before.2.2.1,
    after.2.2.2.1.trans before.2.2.2.1,after.2.2.2.2.1.trans before.2.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_cache (r : State) :
    SourceCacheDriver.columns (derived r) = SourceCacheDriver.columns r ∧
    SourceCacheDriver.rows (derived r) = SourceCacheDriver.rows r ∧
    SourceCacheDriver.slots (derived r) = SourceCacheDriver.slots r ∧
    SourceCacheDriver.modes (derived r) = SourceCacheDriver.modes r ∧
    SourceCacheDriver.owners (derived r) = SourceCacheDriver.owners r ∧
    SourceCacheDriver.literals (derived r) = SourceCacheDriver.literals r := by
  have before := prepared_cache r
  have after := SourceCandidate.withBits_cache (prepared r) (FirstFailure.called (bitsView (prepared r)))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,after.2.2.1.trans before.2.2.1,
    after.2.2.2.1.trans before.2.2.2.1,after.2.2.2.2.1.trans before.2.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_candidate (r : State) : candidate (derived r) = r.registers.output := rfl
theorem derived_canonical (r : State) (count : Nat) (test : Nat → Bool)
    (dimensions : (SourceCacheDriver.rows r).length = count)
    (correct : FirstFailure.ReaderCorrect (SourceCacheDriver.literals r) r.registers.output count test) :
    (derived r).registers.output = TableOwner.answer (FirstFailure.find test 0 count) :=
  FirstFailure.called_canonical (bitsView (prepared r)) _ _ count test correct dimensions rfl rfl

attribute [local irreducible] CutDriver.State.store
def deriveBound : NatPolynomial := .add (.constant 4) (FirstFailure.callBound.substitute (.linear 1 4))
theorem deriveBound_eval (n : Nat) : deriveBound.eval n = 4 + FirstFailure.callBound.eval (n+4) := by
  change 4 + (FirstFailure.callBound.substitute (.linear 1 4)).eval n = _
  rw [NatPolynomial.eval_substitute]
  change 4 + FirstFailure.callBound.eval (1 * n + 4) = _
  rw [Nat.one_mul]
theorem deriveSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    deriveSteps r ≤ deriveBound.eval n := by
  have loaded := (prepare_exec r).bounded n bounded
  have view := bitsView_bounded (prepared r) (n+4) loaded
  have cost := FirstFailure.callSteps_bound (bitsView (prepared r)) (n+4) view
  rw [deriveBound_eval]
  exact Nat.add_le_add_left cost 4

end PNP.Concrete.NormalizerBlocks.SourceCheck
