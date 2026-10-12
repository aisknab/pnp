/-
Copyright (c) 2026 PNP Labs.

Reuse the protected source-check state for recovery. The source words are
copied from retained input-derived data. The requested width is an ordinary
runtime word; the full-width call reads it from the retained input width.
-/
import PNP.Concrete.NormalizerRecoveryCall
import PNP.Concrete.NormalizerSourceCheckPolynomial

namespace PNP.Concrete.NormalizerBlocks.SourceRecovery
open BitRegister Occurrence
abbrev State := CutDriver.State

def ofDense (r : DenseClauses.State) : Recovery.State :=
  ⟨r.registers,r.core.pending,r.core.variables,r.core.buffer,r.core.positive,r.formula,r.remaining,r.index⟩
def toDense (r : Recovery.State) : DenseClauses.State :=
  ⟨⟨r.core,r.formula,r.matching,r.variables,r.assignment⟩,r.remaining,r.counter,r.buffer⟩
theorem ofDense_store (r : DenseClauses.State) : (ofDense r).store = r.store := by
  dsimp only [ofDense,Recovery.State.store,Recovery.State.frame,DenseClauses.State.store,
    DenseClauses.State.frame,DenseClauses.State.registers,CompactClause.State.store,
    CompactClause.State.frame,Registers.store,Frame.join]
theorem toDense_store (r : Recovery.State) : (toDense r).store = r.store := by
  dsimp only [toDense,Recovery.State.store,Recovery.State.frame,DenseClauses.State.store,
    DenseClauses.State.frame,DenseClauses.State.registers,CompactClause.State.store,
    CompactClause.State.frame,Registers.store,Frame.join]
theorem ofDense_inverse (r : Recovery.State) : ofDense (toDense r) = r := rfl
def view (r : State) : Recovery.State := ofDense (PreparedDriver.denseView r)
def withRecovery (r : State) (after : Recovery.State) : State :=
  PreparedDriver.withDense r (toDense after)
theorem view_withRecovery (r : State) (after : Recovery.State) :
    view (withRecovery r after) = after := rfl
theorem withRecovery_registers (r : State) (after : Recovery.State) :
    (withRecovery r after).registers = after.core := rfl
def lift (body : Block 16) : Block 36 := PreparedDriver.liftDense body
theorem lift_exec (body : Block 16) (r : State) (fuel : Nat) (after : Recovery.State)
    (checked : Exec body (view r).store fuel after.store) :
    Exec (lift body) r.store fuel (withRecovery r after).store := by
  have before : (view r).store = (PreparedDriver.denseView r).store := ofDense_store _
  rw [before,← toDense_store after] at checked
  exact PreparedDriver.liftDense_exec body r fuel (toDense after) checked
theorem view_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (view r).store.Bounded n := by
  rw [show (view r).store = (PreparedDriver.denseView r).store from ofDense_store _]
  exact PreparedDriver.denseView_bounded r n bounded

def loadSources : Block 36 :=
  .seq (.action (.copy 9 30)) <| .seq (.action (.copy 10 31)) <|
  .seq (.action (.copy 11 35)) (.action (.copy 12 22))
def sourceView (r : State) : Recovery.State :=
  {view r with
    formula := r.core.formula,matching := r.core.table,
    variables := r.variables,assignment := SourceCheck.candidate r}
def sourcesLoaded (r : State) : State := withRecovery r (sourceView r)
theorem loadSources_exec (r : State) : Exec loadSources r.store 4 (sourcesLoaded r).store := by
  dsimp only [loadSources,sourcesLoaded,sourceView,withRecovery,view,ofDense,toDense,DenseClauses.State.registers,
    SourceCheck.candidate,PreparedDriver.denseView,PreparedDriver.withDense,
    PreparedDriver.graphDense,PreparedDriver.denseGraph,CutDriver.State.withSelection,
    CutDriver.State.selection,CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Registers.store,Frame.join]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
theorem sourcesLoaded_view (r : State) : view (sourcesLoaded r) = sourceView r := rfl
def call : Block 36 := .seq loadSources (lift Recovery.call)
def called (r : State) : State :=
  withRecovery (sourcesLoaded r) (Recovery.called (sourceView r))
def callSteps (r : State) : Nat := 4+Recovery.callSteps (sourceView r)
theorem call_exec (r : State) : Exec call r.store (callSteps r) (called r).store :=
  Exec.seq (loadSources_exec r)
    (lift_exec _ (sourcesLoaded r) _ _ (Recovery.call_exec (sourceView r)))
theorem called_output (r : State) : (called r).registers.output =
    (Recovery.called (sourceView r)).core.output := rfl
theorem called_output_length (r : State) :
    (called r).registers.output.length = (view r).remaining.length :=
  Recovery.called_output_length (sourceView r)
theorem called_original_fields (r : State) :
    (called r).core.width = r.core.width ∧ (called r).core.formula = r.core.formula ∧
    (called r).core.table = r.core.table ∧ (called r).trace = r.trace ∧
    (called r).clauses = r.clauses ∧ (called r).variables = r.variables :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def loadWidth : Block 36 := .action (.copy 13 29)
def widthLoaded (r : State) : State := withRecovery r {view r with remaining := r.core.width}
theorem loadWidth_exec (r : State) : Exec loadWidth r.store 1 (widthLoaded r).store := by
  dsimp only [loadWidth,widthLoaded,withRecovery,view,ofDense,toDense,DenseClauses.State.registers,
    PreparedDriver.denseView,PreparedDriver.withDense,PreparedDriver.graphDense,PreparedDriver.denseGraph,
    CutDriver.State.withSelection,CutDriver.State.selection,CutDriver.State.store,CutDriver.State.frame,
    CutDriver.State.registers,MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,Extraction.State.store,
    Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,Eligibility.State.store,
    Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,ParentQuery.State.registers,
    EdgeKinds.State.store,EdgeKinds.State.frame,ForwardEdge.State.store,ForwardEdge.State.frame,
    Registers.store,Frame.join]
  exact .action _ _
def fullWidth : Block 36 := .seq loadWidth call
def fullWidthResult (r : State) : State := called (widthLoaded r)
def fullWidthSteps (r : State) : Nat := 1+callSteps (widthLoaded r)
theorem fullWidth_exec (r : State) :
    Exec fullWidth r.store (fullWidthSteps r) (fullWidthResult r).store :=
  Exec.seq (loadWidth_exec r) (call_exec (widthLoaded r))
theorem fullWidth_output_length (r : State) :
    (fullWidthResult r).registers.output.length = r.core.width.length :=
  called_output_length (widthLoaded r)

attribute [local irreducible] CutDriver.State.store Recovery.State.store
def callBound : NatPolynomial := .add (.constant 4) (Recovery.callBound.substitute (.linear 1 4))
theorem callSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    callSteps r ≤ callBound.eval n := by
  have loaded := (loadSources_exec r).bounded n bounded
  have view := view_bounded (sourcesLoaded r) (n+4) loaded
  have cost := Recovery.callSteps_bound (sourceView r) (n+4) view
  change 4+Recovery.callSteps (sourceView r) ≤ 4+(Recovery.callBound.substitute (.linear 1 4)).eval n
  have input : (NatPolynomial.linear 1 4).eval n = n+4 := by
    change 1*n+4 = n+4
    rw [Nat.one_mul]
  rw [NatPolynomial.eval_substitute,input]
  exact Nat.add_le_add_left cost 4
def fullWidthBound : NatPolynomial := .add (.constant 1) (callBound.substitute (.linear 1 1))
theorem fullWidthSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    fullWidthSteps r ≤ fullWidthBound.eval n := by
  have loaded := (loadWidth_exec r).bounded n bounded
  have cost := callSteps_bound (widthLoaded r) (n+1) loaded
  change 1+callSteps (widthLoaded r) ≤ 1+(callBound.substitute (.linear 1 1)).eval n
  have input : (NatPolynomial.linear 1 1).eval n = n+1 := by
    change 1*n+1 = n+1
    rw [Nat.one_mul]
  rw [NatPolynomial.eval_substitute,input]
  exact Nat.add_le_add_left cost 1

end PNP.Concrete.NormalizerBlocks.SourceRecovery
