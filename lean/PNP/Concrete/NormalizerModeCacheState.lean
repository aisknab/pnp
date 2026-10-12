/-
Copyright (c) 2026 PNP Labs.

Nineteen-register mode scratch inside the established cut controller.
The completed owner table, dense literals and all original cut fields are
outside this scratch region and remain available to cache completion.
-/
import PNP.Concrete.NormalizerCacheModeCall
import PNP.Concrete.NormalizerOwnerCachePolynomial

namespace PNP.Concrete.NormalizerBlocks.ModeCacheDriver
open BitRegister
abbrev State := CutDriver.State

def modeView (r : State) : CacheMode.State :=
  ⟨PreparedDriver.graphDense r.selection.core.graph,r.selection.core.pending,
    r.selection.core.targetIndex,r.selection.core.targetTag⟩
def modeFrame (r : State) : Store 17 :=
  .cons r.selection.core.output (.cons r.selection.core.currentIndex
    (Frame.join r.selection.frame r.selectionFrame))
def withMode (r : State) (after : CacheMode.State) : State :=
  r.withSelection {r.selection with core := {r.selection.core with
    graph := PreparedDriver.denseGraph after.core, pending := after.matching,
    targetIndex := after.counter, targetTag := after.target}}
theorem modeView_store (r : State) :
    r.store = Frame.join (modeView r).store (modeFrame r) := by
  rw [CutDriver.State.selection_store]
  dsimp only [modeView,modeFrame,CacheMode.State.store,CacheMode.State.frame,
    CutSelection.State.store,ParentQuery.State.store,PreparedDriver.graphDense,
    DenseClauses.State.store,DenseClauses.State.frame,DenseClauses.State.registers,
    CompactClause.State.store,CompactClause.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join,
    ParentQuery.State.frame,CutSelection.State.frame]
theorem withMode_store (r : State) (after : CacheMode.State) :
    (withMode r after).store = Frame.join after.store (modeFrame r) := by
  rw [withMode,CutDriver.State.withSelection_store]
  dsimp only [modeFrame,CacheMode.State.store,CacheMode.State.frame,
    CutSelection.State.store,ParentQuery.State.store,PreparedDriver.denseGraph,
    DenseClauses.State.store,DenseClauses.State.frame,DenseClauses.State.registers,
    CompactClause.State.store,CompactClause.State.frame,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join,
    ParentQuery.State.frame,CutSelection.State.frame]
theorem modeView_withMode (r : State) (after : CacheMode.State) :
    modeView (withMode r after) = after := rfl
theorem withMode_registers (r : State) (after : CacheMode.State) :
    (withMode r after).registers = after.registers := rfl
theorem withMode_frame (r : State) (after : CacheMode.State) :
    (withMode r after).core.width = r.core.width ∧
    (withMode r after).core.formula = r.core.formula ∧
    (withMode r after).core.table = r.core.table ∧
    (withMode r after).trace = r.trace ∧
    (withMode r after).clauses = r.clauses ∧
    (withMode r after).variables = r.variables :=
  CutDriver.withSelection_frame r _
def owners (r : State) : BitString := r.core.core.core.remaining
def literals (r : State) : BitString := OwnerCacheDriver.literals r
theorem withMode_cache (r : State) (after : CacheMode.State) :
    owners (withMode r after) = owners r ∧ literals (withMode r after) = literals r := ⟨rfl,rfl⟩

def liftMode (body : Block 19) : Block 36 := Frame.block 17 body
theorem liftMode_exec (body : Block 19) (r : State) (fuel : Nat)
    (after : CacheMode.State) (checked : Exec body (modeView r).store fuel after.store) :
    Exec (liftMode body) r.store fuel (withMode r after).store := by
  rw [modeView_store,withMode_store]
  exact Frame.execution checked (modeFrame r)
theorem modeView_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (modeView r).store.Bounded n := by
  rw [modeView_store] at bounded
  exact Frame.core_bounded _ _ bounded

end PNP.Concrete.NormalizerBlocks.ModeCacheDriver
