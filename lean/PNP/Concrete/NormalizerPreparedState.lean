/-
Copyright (c) 2026 PNP Labs.

Protected scratch reuse for complete prepared-context construction. Dense
clause work occupies the first sixteen registers. The original width,
formula, matching, terminal trace and both internally selected lists remain
protected in the established thirty-six-register cut state.
-/
import PNP.Concrete.NormalizerDenseCall
import PNP.Concrete.NormalizerCutPolynomial

namespace PNP.Concrete.NormalizerBlocks.PreparedDriver
open BitRegister Occurrence

def graphDense (r : EdgeKinds.State) : DenseClauses.State :=
  ⟨⟨r.core.core,r.core.target,r.core.index,r.core.formula,r.core.matching⟩,
    r.core.mark,r.first,r.second⟩
def denseGraph (r : DenseClauses.State) : EdgeKinds.State :=
  ⟨⟨r.registers,r.core.pending,r.core.variables,r.core.buffer,r.core.positive,r.formula⟩,
    r.remaining,r.index⟩
theorem graphDense_store (r : EdgeKinds.State) :
    (graphDense r).store = r.store := by
  dsimp only [graphDense, DenseClauses.State.store, DenseClauses.State.frame, DenseClauses.State.registers, CompactClause.State.store, CompactClause.State.frame, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
theorem denseGraph_store (r : DenseClauses.State) :
    (denseGraph r).store = r.store := by
  dsimp only [denseGraph, DenseClauses.State.store, DenseClauses.State.frame, DenseClauses.State.registers, CompactClause.State.store, CompactClause.State.frame, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
theorem graphDense_inverse (r : DenseClauses.State) : graphDense (denseGraph r) = r := rfl

def denseView (r : CutDriver.State) : DenseClauses.State := graphDense r.selection.core.graph
def denseFrame (r : CutDriver.State) : Store 20 :=
  Frame.join r.selection.core.frame (Frame.join r.selection.frame r.selectionFrame)
def withDense (r : CutDriver.State) (after : DenseClauses.State) : CutDriver.State :=
  r.withSelection {r.selection with core := {r.selection.core with graph := denseGraph after}}
theorem denseView_store (r : CutDriver.State) :
    r.store = Frame.join (denseView r).store (denseFrame r) := by
  rw [CutDriver.State.selection_store]
  dsimp only [denseView, denseFrame, CutSelection.State.store, ParentQuery.State.store,
    graphDense, DenseClauses.State.store, DenseClauses.State.frame, DenseClauses.State.registers, CompactClause.State.store, CompactClause.State.frame, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, ParentQuery.State.frame, CutSelection.State.frame]
theorem withDense_store (r : CutDriver.State) (after : DenseClauses.State) :
    (withDense r after).store = Frame.join after.store (denseFrame r) := by
  rw [withDense, CutDriver.State.withSelection_store]
  dsimp only [denseFrame, CutSelection.State.store, ParentQuery.State.store,
    denseGraph, DenseClauses.State.store, DenseClauses.State.frame, DenseClauses.State.registers, CompactClause.State.store, CompactClause.State.frame, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, ParentQuery.State.frame, CutSelection.State.frame]
theorem denseView_withDense (r : CutDriver.State) (after : DenseClauses.State) :
    denseView (withDense r after) = after := rfl
theorem withDense_registers (r : CutDriver.State) (after : DenseClauses.State) :
    (withDense r after).registers = after.registers := rfl
theorem withDense_frame (r : CutDriver.State) (after : DenseClauses.State) :
    (withDense r after).core.width = r.core.width ∧
    (withDense r after).core.formula = r.core.formula ∧
    (withDense r after).core.table = r.core.table ∧
    (withDense r after).trace = r.trace ∧
    (withDense r after).clauses = r.clauses ∧
    (withDense r after).variables = r.variables :=
  CutDriver.withSelection_frame r _

def liftDense (body : Block 16) : Block 36 := Frame.block 20 body
theorem liftDense_exec (body : Block 16) (r : CutDriver.State) (fuel : Nat)
    (after : DenseClauses.State) (checked : Exec body (denseView r).store fuel after.store) :
    Exec (liftDense body) r.store fuel (withDense r after).store := by
  rw [denseView_store, withDense_store]
  exact Frame.execution checked (denseFrame r)
theorem denseView_bounded (r : CutDriver.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    (denseView r).store.Bounded bound := by
  rw [denseView_store] at bounded
  exact Frame.core_bounded _ _ bounded

end PNP.Concrete.NormalizerBlocks.PreparedDriver
