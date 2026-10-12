/-
Copyright (c) 2026 PNP Labs.

Test an optional unary ordinal using existing finite counter comparison.
The requested ordinal is a fixed program parameter; every runtime word
is processed with a proved length-dependent bound.
-/
import PNP.Concrete.NormalizerTraceCount

namespace PNP.Concrete.NormalizerBlocks.OrdinalTest
open BitRegister Occurrence
def fill : Nat → Block 9
  | 0 => .action (.clear 2)
  | n+1 => .seq (fill n) (.action (.push 2 true))
def filled (n : Nat) (r : Registers) : Registers := {r with remaining := List.replicate n true}
theorem fill_exec (n : Nat) (r : Registers) :
    Exec (fill n) r.store (n+1) (filled n r).store := by
  induction n with
  | zero => exact .action _ _
  | succ n ih =>
      exact Exec.seq ih
        (show Exec (.action (.push 2 true)) (filled n r).store 1 (filled (n+1) r).store from .action _ _)
def copyIndex : Block 9 := .seq (.action (.copy 1 8)) (.action (.pop 1))
def indexCopied (r : Registers) : Registers := {r with target := r.output.tail}
theorem copyIndex_exec (r : Registers) : Exec copyIndex r.store 2 (indexCopied r).store := by
  cases r
  exact Exec.seq (.action _ _) (.action _ _)
def prepare (n : Nat) : Block 9 := .seq copyIndex (.seq (fill n) (.action (.clear 3)))
def prepared (n : Nat) (r : Registers) : Registers :=
  {r with target := r.output.tail,remaining := List.replicate n true,excess := []}
theorem prepare_exec (n : Nat) (r : Registers) :
    Exec (prepare n) r.store (n+4) (prepared n r).store := by
  have checked := Exec.seq (copyIndex_exec r)
    (Exec.seq (fill_exec n (indexCopied r))
      (show Exec (.action (.clear 3)) (filled n (indexCopied r)).store 1 (prepared n r).store from .action _ _))
  have cost : 2 + ((n+1)+1) = n+4 := by omega
  rw [cost] at checked
  exact checked
def compare (n : Nat) : Block 9 := .seq (prepare n) TraceCount.block
def compared (n : Nat) (r : Registers) : Registers := TraceCount.result (prepared n r)
def compareFuel (n : Nat) (r : Registers) : Nat := n+4 + TraceCount.fuel (prepared n r)
theorem compare_exec (n : Nat) (r : Registers) :
    Exec (compare n) r.store (compareFuel n r) (compared n r).store :=
  Exec.seq (prepare_exec n r) (TraceCount.block_exec (prepared n r))
theorem compared_output (n : Nat) (r : Registers) :
    (compared n r).output = [r.output.tail.length == n] := by
  have value := TraceCount.result_output (prepared n r) rfl
  change (compared n r).output = [r.output.tail.length == (List.replicate n true).length] at value
  rw [List.length_replicate] at value
  exact value
theorem compareFuel_bound (n : Nat) (r : Registers) :
    compareFuel n r ≤ 4 * r.output.length + n + 9 := by
  have cost := TraceCount.fuel_bound (prepared n r)
  have tail := ParentQuery.input_tail_bound r.output
  change TraceCount.fuel (prepared n r) ≤ 4 * r.output.tail.length + 5 at cost
  unfold compareFuel
  omega

def read (n : Nat) : Block 9 := .branch 8 (TraceCount.emit false) (TraceCount.emit false) (compare n)
def result (n : Nat) (r : Registers) : Registers :=
  if ForwardEdge.present r.output then compared n r else TraceCount.emitted false r
def fuel (n : Nat) (r : Registers) : Nat :=
  1 + if ForwardEdge.present r.output then compareFuel n r else 2
theorem read_exec (n : Nat) (r : Registers) :
    Exec (read n) r.store (fuel n r) (result n r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 9) r.store (TraceCount.emit false) (compare n)
    2 (compareFuel n r) (TraceCount.emitted false r).store (compared n r).store
    (TraceCount.emit_exec false r) (compare_exec n r)
  change Exec (read n) r.store (fuel n r)
    (if ForwardEdge.present r.output then (compared n r).store else (TraceCount.emitted false r).store) at checked
  cases h : ForwardEdge.present r.output <;>
    simpa only [result,h,Bool.false_eq_true,ite_false,ite_true] using checked
theorem result_output (n : Nat) (r : Registers) :
    (result n r).output = [ForwardEdge.present r.output && (r.output.tail.length == n)] := by
  cases h : ForwardEdge.present r.output
  · simp only [result,h,Bool.false_eq_true,ite_false,TraceCount.emitted,Bool.false_and]
  · simp only [result,h,ite_true,compared_output,Bool.true_and]
theorem fuel_bound (n : Nat) (r : Registers) :
    fuel n r ≤ 4 * r.output.length + n + 10 := by
  have cost := compareFuel_bound n r
  unfold fuel
  cases ForwardEdge.present r.output <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
def ordinalMatches (n : Nat) : Option Nat → Bool
  | none => false
  | some value => value == n
theorem canonical (n : Nat) (r : Registers) (cell : Option Nat)
    (answer : r.output = TableOwner.answer cell) :
    (result n r).output = [ordinalMatches n cell] := by
  rw [result_output,answer]
  cases cell <;> simp only [ordinalMatches,TableOwner.answer,ForwardEdge.present,List.headD_cons,
    List.tail_cons,List.length_replicate,Bool.false_and,Bool.true_and]

end PNP.Concrete.NormalizerBlocks.OrdinalTest
