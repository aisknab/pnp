/-
Copyright (c) 2026 PNP Labs.

Literal bit-emission execution inside the actual finite frontend instruction
table. Arbitrary operand lengths are handled by a terminating scratch loop.
-/

import PNP.Concrete.NANDFrontendProgram

namespace PNP.Concrete.NANDFrontend

open BitRegister

theorem pair_run (program : Program 9) (base next : Nat) (first second : Bool) (r : Registers)
    (placed : Segment program base (pairCode base first second next)) :
    BitRegister.run program 2 (r.state base) =
      ({r with reversed := second :: first :: r.reversed}).state next := by
  have h0 : BitRegister.lookup program.code base = some (.push 7 first (base + 1)) := by
    simpa only [Nat.add_zero, pairCode, BitRegister.lookup] using placed 0 (by rw [pairCode_length]; decide)
  have h1 : BitRegister.lookup program.code (base + 1) = some (.push 7 second next) :=
    placed 1 (by rw [pairCode_length]; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1,
    Instruction.execute, Instruction.nextControl, Instruction.update]
  rfl

theorem literal_start (program : Program 9) (base next : Nat) (operand : Operand)
    (positive : Bool) (r : Registers)
    (placed : Segment program base (literalCode base operand positive next)) :
    BitRegister.run program 3 (r.state base) =
      ({r with temp := operand.value r, reversed := positive :: positive :: r.reversed}).state (base + 3) := by
  have h0 : BitRegister.lookup program.code base = some (.push 7 positive (base + 1)) := by
    simpa only [Nat.add_zero, literalCode, BitRegister.lookup] using placed 0 (by rw [literalCode_length]; decide)
  have h1 : BitRegister.lookup program.code (base + 1) = some (.push 7 positive (base + 2)) :=
    placed 1 (by rw [literalCode_length]; decide)
  have h2 : BitRegister.lookup program.code (base + 2) = some (.copy 6 operand.slot (base + 3)) :=
    placed 2 (by rw [literalCode_length]; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1, h2,
    Instruction.execute, Instruction.nextControl, Instruction.update]
  cases operand <;> rfl

theorem literal_loop_empty (program : Program 9) (base next : Nat) (operand : Operand)
    (positive : Bool) (r : Registers) (reversed : BitString)
    (placed : Segment program base (literalCode base operand positive next)) :
    BitRegister.run program 3 (({r with temp := [], reversed := reversed}).state (base + 3)) =
      ({r with temp := [], reversed := false :: false :: reversed}).state next := by
  have h3 : BitRegister.lookup program.code (base + 3) =
      some (.branch 6 (base + 7) (base + 4) (base + 4)) := placed 3 (by rw [literalCode_length]; decide)
  have h7 : BitRegister.lookup program.code (base + 7) = some (.push 7 false (base + 8)) :=
    placed 7 (by rw [literalCode_length]; decide)
  have h8 : BitRegister.lookup program.code (base + 8) = some (.push 7 false next) :=
    placed 8 (by rw [literalCode_length]; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h3, h7, h8,
    Instruction.execute, Instruction.nextControl, Instruction.update, Registers.store,
    Store.get, Store.set, Store.indexCases]

theorem literal_loop_cons (program : Program 9) (base next : Nat) (operand : Operand)
    (positive : Bool) (r : Registers) (bit : Bool) (rest reversed : BitString)
    (placed : Segment program base (literalCode base operand positive next)) :
    BitRegister.run program 4 (({r with temp := bit :: rest, reversed := reversed}).state (base + 3)) =
      ({r with temp := rest, reversed := true :: true :: reversed}).state (base + 3) := by
  have h3 : BitRegister.lookup program.code (base + 3) =
      some (.branch 6 (base + 7) (base + 4) (base + 4)) := placed 3 (by rw [literalCode_length]; decide)
  have h4 : BitRegister.lookup program.code (base + 4) = some (.pop 6 (base + 5)) :=
    placed 4 (by rw [literalCode_length]; decide)
  have h5 : BitRegister.lookup program.code (base + 5) = some (.push 7 true (base + 6)) :=
    placed 5 (by rw [literalCode_length]; decide)
  have h6 : BitRegister.lookup program.code (base + 6) = some (.push 7 true (base + 3)) :=
    placed 6 (by rw [literalCode_length]; decide)
  cases bit <;>
    simp only [BitRegister.run, BitRegister.step, Registers.state, h3, h4, h5, h6,
      Instruction.execute, Instruction.nextControl, Instruction.update, Registers.store,
      Store.get, Store.set, Store.indexCases] <;> rfl

private theorem unary_push_commute (count : Nat) (tail : BitString) :
    List.replicate count true ++ true :: tail = true :: (List.replicate count true ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons true) ih

theorem literal_loop (program : Program 9) (base next : Nat) (operand : Operand)
    (positive : Bool) (r : Registers) (word reversed : BitString)
    (placed : Segment program base (literalCode base operand positive next)) :
    BitRegister.run program (4 * word.length + 3)
        (({r with temp := word, reversed := reversed}).state (base + 3)) =
      ({r with temp := [], reversed := false :: false ::
        (List.replicate (2 * word.length) true ++ reversed)}).state next := by
  induction word generalizing reversed with
  | nil => exact literal_loop_empty program base next operand positive r reversed placed
  | cons bit rest ih =>
      have fuel : 4 * (bit :: rest).length + 3 = 4 + (4 * rest.length + 3) := by
        simp only [List.length_cons]
        omega
      rw [fuel, BitRegister.run_add, literal_loop_cons program base next operand positive r bit rest reversed placed,
        ih]
      simp only [List.length_cons, twiceUnary_succ, List.cons_append, unary_push_commute]

theorem literal_run (program : Program 9) (base next : Nat) (operand : Operand)
    (positive : Bool) (r : Registers)
    (placed : Segment program base (literalCode base operand positive next)) :
    BitRegister.run program (4 * (operand.value r).length + 6) (r.state base) =
      ({r with temp := [], reversed := (literalBits positive (operand.value r).length).reverse ++ r.reversed}).state next := by
  have fuel : 4 * (operand.value r).length + 6 = 3 + (4 * (operand.value r).length + 3) := by omega
  rw [fuel, BitRegister.run_add, literal_start program base next operand positive r placed,
    literal_loop program base next operand positive r (operand.value r) (positive :: positive :: r.reversed) placed]
  rw [literalBits_reverse]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

end PNP.Concrete.NANDFrontend
