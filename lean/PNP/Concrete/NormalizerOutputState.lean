/-
Copyright (c) 2026 PNP Labs.

Retain original decoded width in a packet register while the checker runs.
The success branch installs that runtime word as the recovery limit. The
failure branch may reuse the same packet register after branch selection.
-/
import PNP.Concrete.NormalizerSourceRecoveryState
import PNP.Concrete.NormalizerSourceAssemblyDispatch

namespace PNP.Concrete.NormalizerBlocks.OutputBranches
open BitRegister Occurrence
abbrev State := SystemAssembly.State

def saved (width : BitString) : Store 2 := .cons width (.cons [] .nil)
def extend (r : CutDriver.State) (width : BitString) : State :=
  {SourceAssembly.extended r with b := width}
theorem extend_store (r : CutDriver.State) (width : BitString) :
    (extend r width).store = Frame.join r.store (saved width) := by
  dsimp only [extend,saved,SourceAssembly.extended,SourceAssembly.rowsView,
    SourceAssembly.coefficientView,SourceAssembly.word,SourceAssembly.recovery,
    SystemAssembly.State.store,SystemAssembly.State.frame,SystemRows.State.store,SystemRows.State.frame,
    Coefficient.State.store,Coefficient.State.frame,CacheMode.State.store,CacheMode.State.frame,
    DenseClauses.State.store,DenseClauses.State.frame,CompactClause.State.store,CompactClause.State.frame,
    CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Registers.store,Frame.join,Store.get,Store.indexCases]
theorem extend_registers (r : CutDriver.State) (width : BitString) :
    (extend r width).registers = r.registers := rfl
attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store in
theorem extend_bounded (r : CutDriver.State) (width : BitString) (n : Nat)
    (bounded : r.store.Bounded n) (size : width.length ≤ n) : (extend r width).store.Bounded n := by
  rw [extend_store]
  exact Frame.join_bounded _ _ bounded ⟨size,Nat.zero_le n,True.intro⟩
def liftCheck (body : Block 36) : Block 38 := Frame.block 2 body
theorem liftCheck_exec (body : Block 36) (before after : CutDriver.State) (width : BitString) (fuel : Nat)
    (checked : Exec body before.store fuel after.store) :
    Exec (liftCheck body) (extend before width).store fuel (extend after width).store := by
  rw [extend_store,extend_store]
  exact Frame.execution checked (saved width)

def requested (r : CutDriver.State) (width : BitString) : CutDriver.State :=
  SourceRecovery.withRecovery r {SourceRecovery.view r with remaining := width}
theorem requested_store (r : CutDriver.State) (width : BitString) :
    r.store.set 13 width = (requested r width).store := by
  dsimp only [requested,SourceRecovery.withRecovery,SourceRecovery.view,SourceRecovery.ofDense,
    SourceRecovery.toDense,DenseClauses.State.registers,
    PreparedDriver.denseView,PreparedDriver.withDense,PreparedDriver.graphDense,PreparedDriver.denseGraph,
    CutDriver.State.withSelection,CutDriver.State.selection,CutDriver.State.store,CutDriver.State.frame,
    CutDriver.State.registers,MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Registers.store,Frame.join,Store.set,Store.indexCases]
theorem requested_frame (r : CutDriver.State) (width : BitString) :
    (requested r width).core.width = r.core.width ∧
    (requested r width).core.formula = r.core.formula ∧
    (requested r width).core.table = r.core.table ∧
    (requested r width).variables = r.variables ∧
    SourceCheck.candidate (requested r width) = SourceCheck.candidate r := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem requested_count (r : CutDriver.State) (width : BitString) :
    (SourceRecovery.view (requested r width)).remaining = width := rfl
attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store
def loadWidth : Block 38 := .action (.copy 13 36)
theorem loadWidth_exec (r : CutDriver.State) (width : BitString) :
    Exec loadWidth (extend r width).store 1 (extend (requested r width) width).store := by
  rw [extend_store,extend_store]
  have read : (Frame.join r.store (saved width)).get (36 : Fin 38) = width :=
    Frame.get_frame r.store (saved width) (0 : Fin 2)
  have write : (Frame.join r.store (saved width)).set (13 : Fin 38) width =
      Frame.join (requested r width).store (saved width) := by
    rw [show (13 : Fin 38) = Frame.index 2 (13 : Fin 36) from rfl,Frame.set_core,requested_store]
  have work := Exec.action (.copy (13 : Fin 38) 36) (Frame.join r.store (saved width))
  change Exec loadWidth (Frame.join r.store (saved width)) 1
    ((Frame.join r.store (saved width)).set 13 ((Frame.join r.store (saved width)).get 36)) at work
  rw [read,write] at work
  exact work

def recover : Block 38 := .seq loadWidth (liftCheck SourceRecovery.call)
def recovered (r : CutDriver.State) (width : BitString) : State :=
  extend (SourceRecovery.called (requested r width)) width
def recoveryFuel (r : CutDriver.State) (width : BitString) : Nat :=
  1+SourceRecovery.callSteps (requested r width)
theorem recover_exec (r : CutDriver.State) (width : BitString) :
    Exec recover (extend r width).store (recoveryFuel r width) (recovered r width).store :=
  Exec.seq (loadWidth_exec r width)
    (liftCheck_exec _ _ _ width _ (SourceRecovery.call_exec (requested r width)))
theorem recovered_output (r : CutDriver.State) (width : BitString) :
    (recovered r width).registers.output = (SourceRecovery.called (requested r width)).registers.output := rfl
theorem recovered_length (r : CutDriver.State) (width : BitString) :
    (recovered r width).registers.output.length = width.length := by
  rw [recovered_output,SourceRecovery.called_output_length,requested_count]
def recoveryBound : NatPolynomial := .add (.constant 1) (SourceRecovery.callBound.substitute (.linear 1 1))
theorem recoveryFuel_bound (r : CutDriver.State) (width : BitString) (n : Nat)
    (bounded : (extend r width).store.Bounded n) :
    recoveryFuel r width ≤ recoveryBound.eval n := by
  have loaded := (loadWidth_exec r width).bounded n bounded
  rw [extend_store] at loaded
  have core := Frame.core_bounded (requested r width).store (saved width) loaded
  have work := SourceRecovery.callSteps_bound (requested r width) (n+1) core
  change 1+SourceRecovery.callSteps (requested r width) ≤
    1+(SourceRecovery.callBound.substitute (.linear 1 1)).eval n
  have input : (NatPolynomial.linear 1 1).eval n = n+1 := by change 1*n+1=n+1; rw [Nat.one_mul]
  rw [NatPolynomial.eval_substitute,input]
  exact Nat.add_le_add_left work 1

end PNP.Concrete.NormalizerBlocks.OutputBranches
