/-
Copyright (c) 2026 PNP Labs.

Install the complete candidate enumerator in protected cache state.
The scratch prefix ends before runtime dimensions and all four cache
tables. Original cut fields remain available for model recovery.
-/
import PNP.Concrete.NormalizerCandidateBitsCall
import PNP.Concrete.NormalizerSourceCachePolynomial

namespace PNP.Concrete.NormalizerBlocks.SourceCandidate
open BitRegister
abbrev State := CutDriver.State
def bitsView (r : State) : CandidateBits.State :=
  ⟨ModeCacheDriver.modeView r,r.selection.core.output,r.selection.core.currentIndex,r.selection.trace⟩
def bitsFrame (r : State) : Store 14 :=
  .cons r.selection.remaining (.cons r.selection.buffer r.selectionFrame)
def withBits (r : State) (after : CandidateBits.State) : State :=
  r.withSelection {r.selection with core := {r.selection.core with
    graph := PreparedDriver.denseGraph after.core.core,pending := after.core.matching,
    targetIndex := after.core.counter,targetTag := after.core.target,
    output := after.remaining,currentIndex := after.counter},trace := after.buffer}
theorem bitsView_store (r : State) :
    r.store = Frame.join (bitsView r).store (bitsFrame r) := by
  rw [CutDriver.State.selection_store]
  dsimp only [bitsView,bitsFrame,CandidateBits.State.store,CandidateBits.State.frame,
    ModeCacheDriver.modeView,CacheMode.State.store,CacheMode.State.frame,
    CutSelection.State.store,ParentQuery.State.store,PreparedDriver.graphDense,
    DenseClauses.State.store,DenseClauses.State.frame,DenseClauses.State.registers,
    CompactClause.State.store,CompactClause.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join,
    ParentQuery.State.frame,CutSelection.State.frame]
theorem withBits_store (r : State) (after : CandidateBits.State) :
    (withBits r after).store = Frame.join after.store (bitsFrame r) := by
  rw [withBits,CutDriver.State.withSelection_store]
  dsimp only [bitsFrame,CandidateBits.State.store,CandidateBits.State.frame,
    CacheMode.State.store,CacheMode.State.frame,CutSelection.State.store,
    ParentQuery.State.store,PreparedDriver.denseGraph,DenseClauses.State.store,
    DenseClauses.State.frame,DenseClauses.State.registers,CompactClause.State.store,
    CompactClause.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,ForwardEdge.State.store,
    ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join,ParentQuery.State.frame,
    CutSelection.State.frame]
theorem bitsView_withBits (r : State) (after : CandidateBits.State) :
    bitsView (withBits r after) = after := rfl
theorem withBits_registers (r : State) (after : CandidateBits.State) :
    (withBits r after).registers = after.registers := rfl
theorem withBits_frame (r : State) (after : CandidateBits.State) :
    (withBits r after).core.width = r.core.width ∧
    (withBits r after).core.formula = r.core.formula ∧
    (withBits r after).core.table = r.core.table ∧
    (withBits r after).trace = r.trace ∧
    (withBits r after).clauses = r.clauses ∧
    (withBits r after).variables = r.variables := CutDriver.withSelection_frame r _
theorem withBits_cache (r : State) (after : CandidateBits.State) :
    SourceCacheDriver.columns (withBits r after) = SourceCacheDriver.columns r ∧
    SourceCacheDriver.rows (withBits r after) = SourceCacheDriver.rows r ∧
    SourceCacheDriver.slots (withBits r after) = SourceCacheDriver.slots r ∧
    SourceCacheDriver.modes (withBits r after) = SourceCacheDriver.modes r ∧
    SourceCacheDriver.owners (withBits r after) = SourceCacheDriver.owners r ∧
    SourceCacheDriver.literals (withBits r after) = SourceCacheDriver.literals r :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
def liftBits (body : Block 22) : Block 36 := Frame.block 14 body
theorem liftBits_exec (body : Block 22) (r : State) (fuel : Nat) (after : CandidateBits.State)
    (checked : Exec body (bitsView r).store fuel after.store) :
    Exec (liftBits body) r.store fuel (withBits r after).store := by
  rw [bitsView_store,withBits_store]
  exact Frame.execution checked (bitsFrame r)
theorem bitsView_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (bitsView r).store.Bounded n := by
  rw [bitsView_store] at bounded
  exact Frame.core_bounded _ _ bounded

def loadData : Block 36 :=
  .seq (.action (.copy 13 28)) (.seq (.action (.copy 16 27))
    (.seq (.action (.copy 17 25)) (.action (.copy 19 23))))
def readyBits (r : State) : CandidateBits.State :=
  ⟨⟨{(bitsView r).core.core with formula := SourceCacheDriver.literals r},
    SourceCacheDriver.owners r,SourceCacheDriver.slots r,(bitsView r).core.target⟩,
    SourceCacheDriver.columns r,(bitsView r).counter,(bitsView r).buffer⟩
def ready (r : State) : State := withBits r (readyBits r)
theorem loadData_exec (r : State) : Exec loadData r.store 4 (ready r).store := by
  dsimp only [loadData,ready,readyBits,bitsView,withBits,ModeCacheDriver.modeView,
    SourceCacheDriver.literals,SourceCacheDriver.owners,SourceCacheDriver.slots,
    SourceCacheDriver.columns,ModeCacheDriver.literals,ModeCacheDriver.owners,OwnerCacheDriver.literals,
    PreparedDriver.graphDense,PreparedDriver.denseGraph,CutDriver.State.withSelection,
    CutDriver.State.selection,CutDriver.State.store,CutDriver.State.frame,
    MatchingDriver.State.store,MatchingDriver.State.frame,Search.State.store,Search.State.frame,
    Search.State.parent,Exploration.State.store,Exploration.State.frame,Extraction.State.store,
    Extraction.State.frame,Extraction.State.parent,Eligibility.State.store,Eligibility.State.frame,
    ParentQuery.State.store,ParentQuery.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact .seq (.action _ _) (.seq (.action _ _) (.seq (.action _ _) (.action _ _)))
theorem ready_fields (r : State) :
    (bitsView (ready r)).core.core.formula = SourceCacheDriver.literals r ∧
    (bitsView (ready r)).core.matching = SourceCacheDriver.owners r ∧
    (bitsView (ready r)).core.counter = SourceCacheDriver.slots r ∧
    (bitsView (ready r)).remaining = SourceCacheDriver.columns r := ⟨rfl,rfl,rfl,rfl⟩
def derive : Block 36 := .seq loadData (liftBits CandidateBits.call)
def derived (r : State) : State := withBits (ready r) (CandidateBits.called (bitsView (ready r)))
def deriveSteps (r : State) : Nat := 4 + CandidateBits.callSteps (bitsView (ready r))
theorem derive_exec (r : State) : Exec derive r.store (deriveSteps r) (derived r).store :=
  Exec.seq (loadData_exec r) (liftBits_exec _ (ready r) _ _ (CandidateBits.call_exec _))
theorem derived_frame (r : State) :
    (derived r).core.width = r.core.width ∧ (derived r).core.formula = r.core.formula ∧
    (derived r).core.table = r.core.table ∧ (derived r).trace = r.trace ∧
    (derived r).clauses = r.clauses ∧ (derived r).variables = r.variables := by
  have before := withBits_frame r (readyBits r)
  have after := withBits_frame (ready r) (CandidateBits.called (bitsView (ready r)))
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
  have before := withBits_cache r (readyBits r)
  have after := withBits_cache (ready r) (CandidateBits.called (bitsView (ready r)))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,after.2.2.1.trans before.2.2.1,
    after.2.2.2.1.trans before.2.2.2.1,after.2.2.2.2.1.trans before.2.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem derived_output_length (r : State) :
    (derived r).registers.output.length = (SourceCacheDriver.columns r).length :=
  CandidateBits.called_output_length (bitsView (ready r))
theorem derived_canonical (r : State) (count : Nat) (sigma : Nat → Bool)
    (dimensions : (SourceCacheDriver.columns r).length = count)
    (correct : CandidateBits.ReaderCorrect (SourceCacheDriver.literals r)
      (SourceCacheDriver.owners r) (SourceCacheDriver.slots r) count sigma) :
    (derived r).registers.output = List.ofFn (fun i : Fin count => sigma i.val) :=
  CandidateBits.called_canonical (bitsView (ready r)) _ _ _ count sigma correct dimensions rfl rfl rfl

attribute [local irreducible] CutDriver.State.store
def deriveBound : NatPolynomial := .add (.constant 4) (CandidateBits.callBound.substitute (.linear 1 4))
theorem deriveBound_eval (n : Nat) : deriveBound.eval n = 4 + CandidateBits.callBound.eval (n + 4) := by
  change 4 + (CandidateBits.callBound.substitute (.linear 1 4)).eval n = _
  rw [NatPolynomial.eval_substitute]
  change 4 + CandidateBits.callBound.eval (1 * n + 4) = _
  rw [Nat.one_mul]
theorem deriveSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    deriveSteps r ≤ deriveBound.eval n := by
  have loaded := (loadData_exec r).bounded n bounded
  have view := bitsView_bounded (ready r) (n + 4) loaded
  have cost := CandidateBits.callSteps_bound (bitsView (ready r)) (n + 4) view
  rw [deriveBound_eval]
  exact Nat.add_le_add_left cost 4

end PNP.Concrete.NormalizerBlocks.SourceCandidate
