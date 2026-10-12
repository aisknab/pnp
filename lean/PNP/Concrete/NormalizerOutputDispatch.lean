/-
Copyright (c) 2026 PNP Labs.

Select exact final packets from the computed check result. Presence is
tested before the failure payload is stripped, so failure at row zero is
not confused with success. Original width is retained until branch choice.
-/
import PNP.Concrete.NormalizerOutputPackets

namespace PNP.Concrete.NormalizerBlocks.OutputBranches
open BitRegister Occurrence
attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store

theorem extend_outputWord (r : CutDriver.State) (width : BitString) :
    (extend r width).store.get (8 : Fin 38) = r.registers.output := by
  rw [extend_store]
  exact (Frame.get_core r.store (saved width) (8 : Fin 36)).trans (CutDriver.State.get_output r)
def hasFailure (r : CutDriver.State) : Bool := r.registers.output.headD false
def dispatch : Block 38 := .branch 8 success success equation.block
def dispatched (r : CutDriver.State) (width : BitString) : State :=
  if hasFailure r then equation.result (extend r width) else succeeded r width
def dispatchFuel (r : CutDriver.State) (width : BitString) : Nat :=
  1+if hasFailure r then equation.fuel (extend r width) else successFuel r width
def dispatchBound : NatPolynomial := .add (.add equation.bound successBound) (.constant 1)
theorem dispatch_exec (r : CutDriver.State) (width : BitString) :
    Exec dispatch (extend r width).store (dispatchFuel r width) (dispatched r width).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 38) (extend r width).store success equation.block
    (successFuel r width) (equation.fuel (extend r width)) (succeeded r width).store
    (equation.result (extend r width)).store (success_exec r width) (equation.exec (extend r width))
  rw [extend_outputWord] at checked
  change Exec dispatch (extend r width).store
    (1+if hasFailure r then equation.fuel (extend r width) else successFuel r width)
    (if hasFailure r then (equation.result (extend r width)).store else (succeeded r width).store) at checked
  cases h : hasFailure r <;>
    simpa only [dispatched,dispatchFuel,h,Bool.false_eq_true,ite_false,ite_true] using checked
theorem dispatchFuel_bound (r : CutDriver.State) (width : BitString) (n : Nat)
    (bounded : (extend r width).store.Bounded n) :
    dispatchFuel r width ≤ dispatchBound.eval n := by
  have first := successFuel_bound r width n bounded
  have second := equation.cost (extend r width) n bounded
  change 1+(if hasFailure r then equation.fuel (extend r width) else successFuel r width) ≤
    equation.bound.eval n+successBound.eval n+1
  cases hasFailure r <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
theorem dispatched_bounded (r : CutDriver.State) (width : BitString) (n : Nat)
    (bounded : (extend r width).store.Bounded n) :
    (dispatched r width).store.Bounded (n+dispatchBound.eval n) :=
  Store.bounded_mono ((dispatch_exec r width).bounded n bounded)
    (Nat.add_le_add_left (dispatchFuel_bound r width n bounded) n)
theorem dispatched_none (r : CutDriver.State) (width : BitString)
    (answer : r.registers.output = TableOwner.answer none) :
    dispatched r width = succeeded r width := by
  unfold dispatched hasFailure
  rw [answer,SourceAssembly.answer_presence]
  rfl
theorem dispatched_some (r : CutDriver.State) (width : BitString) (index : Nat)
    (answer : r.registers.output = TableOwner.answer (some index)) :
    dispatched r width = equation.result (extend r width) := by
  unfold dispatched hasFailure
  rw [answer,SourceAssembly.answer_presence]
  rfl
theorem dispatched_model_output (r : CutDriver.State) (width : BitString)
    (answer : r.registers.output = TableOwner.answer none) :
    (dispatched r width).registers.output =
      [false,false,true] ++ BitString.frame (SourceRecovery.called (requested r width)).registers.output := by
  rw [dispatched_none r width answer,success_output]
theorem dispatched_system_output (r : CutDriver.State) (width : BitString) (index : Nat)
    (answer : r.registers.output = TableOwner.answer (some index)) :
    (dispatched r width).registers.output = [false,true,false] ++
      (List.replicate (SourceCacheDriver.rows r).length true ++
        false::(SourceAssembly.failureResult (extend r width)).registers.output) := by
  rw [dispatched_some r width index answer,equation_output]
  have rows : (extend r width).core.rows = SourceCacheDriver.rows r :=
    (SourceAssembly.extended_inputs r).2.2.2.2.2
  rw [rows]

end PNP.Concrete.NormalizerBlocks.OutputBranches
