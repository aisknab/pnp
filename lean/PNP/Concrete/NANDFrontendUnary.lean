/-
Copyright (c) 2026 PNP Labs.

Unbounded unary-index reading by a literal finite register loop. Both canonical
and malformed strings have checked execution and linear source-step bounds.
-/

import PNP.Concrete.NANDFrontendRead

namespace PNP.Concrete.NANDFrontend

open BitRegister

def Operand.write : Operand → Registers → BitString → Registers
  | .left, r, word => {r with left := word}
  | .right, r, word => {r with right := word}
  | .gate, r, word => {r with gate := word}

theorem Operand.value_write (operand : Operand) (r : Registers) (word : BitString) :
    operand.value (operand.write r word) = word := by cases operand <;> rfl

theorem Operand.write_value (operand : Operand) (r : Registers) :
    operand.write r (operand.value r) = r := by cases operand <;> rfl

theorem Operand.write_write (operand : Operand) (r : Registers) (first second : BitString) :
    operand.write (operand.write r first) second = operand.write r second := by
  cases operand <;> rfl

theorem Operand.write_input (operand : Operand) (r : Registers) (word input : BitString) :
    operand.write {r with input := input} word = {operand.write r word with input := input} := by
  cases operand <;> rfl

theorem Operand.value_input (operand : Operand) (r : Registers) (input : BitString) :
    operand.value {r with input := input} = operand.value r := by cases operand <;> rfl

def unaryTree (base next failure : Nat) : ReadTree :=
  tokenTree failure (base + 45) next failure failure failure failure failure
    failure failure failure failure failure failure failure failure

def unaryCode (base : Nat) (operand : Operand) (next failure : Nat) : List (Instruction 9) :=
  (unaryTree base next failure).code base failure ++ [.push operand.slot true base]

theorem unaryCode_length (base : Nat) (operand : Operand) (next failure : Nat) :
    (unaryCode base operand next failure).length = 46 := rfl

structure UnaryResult where
  fuel : Nat
  rest : BitString
  added : Nat
  valid : Bool
deriving Repr

def unaryScan : BitString → UnaryResult
  | false :: false :: false :: true :: rest =>
      let result := unaryScan rest
      {result with fuel := 9 + result.fuel, added := result.added + 1}
  | false :: false :: true :: false :: rest => ⟨8, rest, 0, true⟩
  | _ :: _ :: _ :: _ :: rest => ⟨8, rest, 0, false⟩
  | input => ⟨2 * input.length + 1, [], 0, false⟩

def readerExit (valid : Bool) (next failure : Nat) : Nat :=
  match valid with
  | false => failure
  | true => next

def unaryResultRegisters (operand : Operand) (r : Registers) (result : UnaryResult) : Registers :=
  operand.write {r with input := result.rest}
    (List.replicate result.added true ++ operand.value r)

theorem unaryCode_tree (program : Program 9) (base : Nat) (operand : Operand)
    (next failure : Nat) (placed : Segment program base (unaryCode base operand next failure)) :
    Segment program base ((unaryTree base next failure).code base failure) :=
  Segment.head _ _ placed

theorem unary_unit (program : Program 9) (base : Nat) (operand : Operand)
    (next failure : Nat) (r : Registers) (rest : BitString)
    (placed : Segment program base (unaryCode base operand next failure)) :
    BitRegister.run program 9
        (({r with input := false :: false :: false :: true :: rest}).state base) =
      (operand.write {r with input := rest} (true :: operand.value r)).state base := by
  have treeRun := ReadTree.run program (unaryTree base next failure) base failure r
    (false :: false :: false :: true :: rest) (unaryCode_tree program base operand next failure placed)
  have firstSteps : BitRegister.run program 8
      (({r with input := false :: false :: false :: true :: rest}).state base) =
        ({r with input := rest}).state (base + 45) := by
    simpa only [unaryTree, tokenTree, ReadTree.scan, ReadTree.entry,
      Bool.false_eq_true, ↓reduceIte] using treeRun
  have hp : BitRegister.lookup program.code (base + 45) =
      some (.push operand.slot true base) := by
    have cut := Segment.tail ((unaryTree base next failure).code base failure)
      [.push operand.slot true base] placed
    rw [ReadTree.code_length] at cut
    have h := cut 0 (by change 0 < 1; decide)
    simpa only [unaryTree, tokenTree_size, Nat.add_zero, BitRegister.lookup] using h
  change BitRegister.run program (8 + 1) _ = _
  rw [BitRegister.run_add, firstSteps]
  cases operand <;>
    simp only [BitRegister.run, BitRegister.step, Registers.state, hp,
      Instruction.execute, Instruction.nextControl, Instruction.update,
      Registers.store, Store.get, Store.set, Store.indexCases, Operand.slot,
      Operand.write, Operand.value]

private theorem unary_word_cons (count : Nat) (tail : BitString) :
    List.replicate count true ++ true :: tail = List.replicate (count + 1) true ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

theorem unary_run (program : Program 9) (base : Nat) (operand : Operand)
    (next failure : Nat) (r : Registers) (input : BitString)
    (placed : Segment program base (unaryCode base operand next failure)) :
    BitRegister.run program (unaryScan input).fuel (({r with input := input}).state base) =
      (unaryResultRegisters operand r (unaryScan input)).state
        (readerExit (unaryScan input).valid next failure) := by
  have treeRun := ReadTree.run program (unaryTree base next failure) base failure r input
    (unaryCode_tree program base operand next failure placed)
  match input with
  | [] =>
      simpa only [unaryTree, tokenTree, ReadTree.scan, ReadTree.entry, unaryScan,
        unaryResultRegisters, List.replicate_zero, List.nil_append, Operand.value_input, Operand.write_input,
        Operand.write_value, readerExit, Bool.false_eq_true, ↓reduceIte, List.length_nil]
        using treeRun
  | [a] =>
      cases a <;>
        simpa only [unaryTree, tokenTree, ReadTree.scan, ReadTree.entry, unaryScan,
          unaryResultRegisters, List.replicate_zero, List.nil_append, Operand.value_input, Operand.write_input,
          Operand.write_value, readerExit, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
          using treeRun
  | [a, b] =>
      cases a <;> cases b <;>
        simpa only [unaryTree, tokenTree, ReadTree.scan, ReadTree.entry, unaryScan,
          unaryResultRegisters, List.replicate_zero, List.nil_append, Operand.value_input, Operand.write_input,
          Operand.write_value, readerExit, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
          using treeRun
  | [a, b, c] =>
      cases a <;> cases b <;> cases c <;>
        simpa only [unaryTree, tokenTree, ReadTree.scan, ReadTree.entry, unaryScan,
          unaryResultRegisters, List.replicate_zero, List.nil_append, Operand.value_input, Operand.write_input,
          Operand.write_value, readerExit, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
          using treeRun
  | a :: b :: c :: d :: rest =>
      cases a <;> cases b <;> cases c <;> cases d
      all_goals first
        | solve
          | simpa only [unaryTree, tokenTree, ReadTree.scan, ReadTree.entry, unaryScan,
              unaryResultRegisters, List.replicate_zero, List.nil_append, Operand.value_input, Operand.write_input,
              Operand.write_value, readerExit, Bool.false_eq_true, ↓reduceIte] using treeRun
        | skip
      simp only [unaryScan]
      rw [BitRegister.run_add, unary_unit program base operand next failure r rest placed]
      have ih := unary_run program base operand next failure
        (operand.write r (true :: operand.value r)) rest placed
      simpa only [unaryResultRegisters, Operand.value_write, Operand.write_input,
        Operand.write_write, unary_word_cons] using ih
termination_by input.length

theorem unaryScan_bounds (input : BitString) :
    (unaryScan input).fuel ≤ 3 * input.length + 1 ∧
      (unaryScan input).rest.length + 4 * (unaryScan input).added ≤ input.length := by
  match input with
  | [] => decide
  | [a] => cases a <;> decide
  | [a, b] => cases a <;> cases b <;> decide
  | [a, b, c] => cases a <;> cases b <;> cases c <;> decide
  | a :: b :: c :: d :: rest =>
      have ih := unaryScan_bounds rest
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp only [unaryScan, List.length_cons] <;> constructor <;> omega
termination_by input.length
decreasing_by all_goals simp only [List.length_cons]; omega

theorem unaryScan_success_consumes (input : BitString) (valid : (unaryScan input).valid = true) :
    (unaryScan input).rest.length < input.length := by
  match input with
  | [] => cases valid
  | [a] => cases a <;> cases valid
  | [a, b] => cases a <;> cases b <;> cases valid
  | [a, b, c] => cases a <;> cases b <;> cases c <;> cases valid
  | a :: b :: c :: d :: rest =>
      have ih := (unaryScan_bounds rest).2
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp only [unaryScan, List.length_cons] at valid ⊢ <;> first
          | omega
          | cases valid

theorem unaryScan_canonical (count : Nat) (suffix : BitString) :
    unaryScan (LockedNAND.encodeTokens (LockedNAND.encodeNatTokens count) ++ suffix) =
      ⟨9 * count + 8, suffix, count, true⟩ := by
  induction count with
  | zero =>
      simp only [LockedNAND.encodeNatTokens, LockedNAND.encodeTokens,
        LockedNAND.Token.bits, List.cons_append, List.nil_append, unaryScan]
  | succ count ih =>
      simp only [LockedNAND.encodeNatTokens, LockedNAND.encodeTokens,
        LockedNAND.Token.bits, List.cons_append, List.nil_append, unaryScan, ih]
      congr 1
      omega

end PNP.Concrete.NANDFrontend
