/-
Copyright (c) 2026 PNP Labs.

Exact output packing for the finite frontend. The original input width and
enlarged formula width occupy distinct unary fields. Every reversal and prefix
loop is executed by literal finite register instructions.
-/

import PNP.Concrete.NANDFrontendLoopResult

namespace PNP.Concrete.NANDFrontend

open BitRegister

def packReverseCode (base next : Nat) : List (Instruction 9) :=
  [.branch 7 next (base + 1) (base + 3),
   .pop 7 (base + 2), .push 8 false base,
   .pop 7 (base + 4), .push 8 true base]

theorem packReverseCode_length (base next : Nat) : (packReverseCode base next).length = 5 := rfl

theorem packReverse_empty (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (packReverseCode base next)) :
    BitRegister.run program 1 (({r with reversed := []}).state base) =
      ({r with reversed := []}).state next := by
  have h0 : BitRegister.lookup program.code base = some (.branch 7 next (base + 1) (base + 3)) := by
    simpa only [Nat.add_zero, packReverseCode, BitRegister.lookup] using placed 0 (by change 0 < 5; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.indexCases]

theorem packReverse_cons (program : Program 9) (base next : Nat) (r : Registers)
    (bit : Bool) (rest : BitString)
    (placed : Segment program base (packReverseCode base next)) :
    BitRegister.run program 3 (({r with reversed := bit :: rest}).state base) =
      ({r with reversed := rest, output := bit :: r.output}).state base := by
  have h0 : BitRegister.lookup program.code base = some (.branch 7 next (base + 1) (base + 3)) := by
    simpa only [Nat.add_zero, packReverseCode, BitRegister.lookup] using placed 0 (by change 0 < 5; decide)
  have h1 : BitRegister.lookup program.code (base + 1) = some (.pop 7 (base + 2)) := by
    simpa only [Nat.add_zero, packReverseCode, BitRegister.lookup] using placed 1 (by change 1 < 5; decide)
  have h2 : BitRegister.lookup program.code (base + 2) = some (.push 8 false base) := by
    simpa only [Nat.add_zero, packReverseCode, BitRegister.lookup] using placed 2 (by change 2 < 5; decide)
  have h3 : BitRegister.lookup program.code (base + 3) = some (.pop 7 (base + 4)) := by
    simpa only [Nat.add_zero, packReverseCode, BitRegister.lookup] using placed 3 (by change 3 < 5; decide)
  have h4 : BitRegister.lookup program.code (base + 4) = some (.push 8 true base) := by
    simpa only [Nat.add_zero, packReverseCode, BitRegister.lookup] using placed 4 (by change 4 < 5; decide)
  cases bit <;> simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1, h2, h3, h4,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.set, Store.indexCases] <;> rfl

theorem packReverse_run (program : Program 9) (base next : Nat) (r : Registers)
    (word : BitString)
    (placed : Segment program base (packReverseCode base next)) :
    BitRegister.run program (3 * word.length + 1) (({r with reversed := word}).state base) =
      ({r with reversed := [], output := word.reverse ++ r.output}).state next := by
  induction word generalizing r with
  | nil => exact packReverse_empty program base next r placed
  | cons bit rest ih =>
      have fuel : 3 * (bit :: rest).length + 1 = 3 + (3 * rest.length + 1) := by
        simp only [List.length_cons]
        omega
      rw [fuel, BitRegister.run_add, packReverse_cons program base next r bit rest placed]
      have h := ih {r with output := bit :: r.output}
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using h

inductive WidthKind where
  | original | frontend
deriving Repr

def WidthKind.slot : WidthKind → Fin 9
  | .original => 1
  | .frontend => 2

def WidthKind.value : WidthKind → Registers → BitString
  | .original, r => r.inputs
  | .frontend, r => r.width

def widthPrefixCode (base : Nat) (kind : WidthKind) (next : Nat) : List (Instruction 9) :=
  [.push 8 false (base + 1), .copy 6 kind.slot (base + 2),
   .branch 6 next (base + 3) (base + 3), .pop 6 (base + 4), .push 8 true (base + 2)]

theorem widthPrefixCode_length (base : Nat) (kind : WidthKind) (next : Nat) :
    (widthPrefixCode base kind next).length = 5 := rfl

theorem widthPrefix_start (program : Program 9) (base next : Nat) (kind : WidthKind) (r : Registers)
    (placed : Segment program base (widthPrefixCode base kind next)) :
    BitRegister.run program 2 (r.state base) =
      ({r with temp := kind.value r, output := false :: r.output}).state (base + 2) := by
  have h0 : BitRegister.lookup program.code base = some (.push 8 false (base + 1)) := by
    simpa only [Nat.add_zero, widthPrefixCode, BitRegister.lookup] using placed 0 (by change 0 < 5; decide)
  have h1 : BitRegister.lookup program.code (base + 1) = some (.copy 6 kind.slot (base + 2)) :=
    placed 1 (by change 1 < 5; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1,
    Instruction.execute, Instruction.nextControl, Instruction.update]
  cases kind <;> rfl

theorem widthPrefix_loop_empty (program : Program 9) (base next : Nat) (kind : WidthKind) (r : Registers)
    (placed : Segment program base (widthPrefixCode base kind next)) :
    BitRegister.run program 1 (({r with temp := []}).state (base + 2)) =
      ({r with temp := []}).state next := by
  have h2 : BitRegister.lookup program.code (base + 2) =
      some (.branch 6 next (base + 3) (base + 3)) := placed 2 (by change 2 < 5; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h2,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.indexCases]

theorem widthPrefix_loop_cons (program : Program 9) (base next : Nat) (kind : WidthKind)
    (r : Registers) (bit : Bool) (rest : BitString)
    (placed : Segment program base (widthPrefixCode base kind next)) :
    BitRegister.run program 3 (({r with temp := bit :: rest}).state (base + 2)) =
      ({r with temp := rest, output := true :: r.output}).state (base + 2) := by
  have h2 : BitRegister.lookup program.code (base + 2) =
      some (.branch 6 next (base + 3) (base + 3)) := placed 2 (by change 2 < 5; decide)
  have h3 : BitRegister.lookup program.code (base + 3) = some (.pop 6 (base + 4)) :=
    placed 3 (by change 3 < 5; decide)
  have h4 : BitRegister.lookup program.code (base + 4) = some (.push 8 true (base + 2)) :=
    placed 4 (by change 4 < 5; decide)
  cases bit <;> simp only [BitRegister.run, BitRegister.step, Registers.state, h2, h3, h4,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.set, Store.indexCases] <;> rfl

theorem widthPrefix_loop (program : Program 9) (base next : Nat) (kind : WidthKind)
    (r : Registers) (word : BitString)
    (placed : Segment program base (widthPrefixCode base kind next)) :
    BitRegister.run program (3 * word.length + 1) (({r with temp := word}).state (base + 2)) =
      ({r with temp := [], output := List.replicate word.length true ++ r.output}).state next := by
  induction word generalizing r with
  | nil => exact widthPrefix_loop_empty program base next kind r placed
  | cons bit rest ih =>
      have fuel : 3 * (bit :: rest).length + 1 = 3 + (3 * rest.length + 1) := by
        simp only [List.length_cons]
        omega
      rw [fuel, BitRegister.run_add, widthPrefix_loop_cons program base next kind r bit rest placed]
      have h := ih {r with output := true :: r.output}
      have word : List.replicate rest.length true ++ true :: r.output =
          List.replicate (rest.length + 1) true ++ r.output := by
        rw [unaryWord_add, List.append_assoc]
        rfl
      rw [word] at h
      exact h

theorem widthPrefix_run (program : Program 9) (base next : Nat) (kind : WidthKind) (r : Registers)
    (placed : Segment program base (widthPrefixCode base kind next)) :
    BitRegister.run program (3 * (kind.value r).length + 3) (r.state base) =
      ({r with temp := [], output := List.replicate (kind.value r).length true ++ false :: r.output}).state next := by
  have fuel : 3 * (kind.value r).length + 3 = 2 + (3 * (kind.value r).length + 1) := by omega
  rw [fuel, BitRegister.run_add, widthPrefix_start program base next kind r placed]
  exact widthPrefix_loop program base next kind {r with output := false :: r.output} (kind.value r) placed

def packCode (base next : Nat) : List (Instruction 9) :=
  [.clear 8 (base + 1)] ++ packReverseCode (base + 1) (base + 6) ++
    widthPrefixCode (base + 6) .frontend (base + 11) ++
    widthPrefixCode (base + 11) .original (base + 16) ++ [.push 8 true next]

def packFuel (r : Registers) : Nat := 3 * r.reversed.length + 3 * r.width.length + 3 * r.inputs.length + 9

def packed (r : Registers) : Registers :=
  {r with
    temp := []
    reversed := []
    output := true :: (List.replicate r.inputs.length true ++ false ::
      (List.replicate r.width.length true ++ false :: r.reversed.reverse))}

theorem packCode_length (base next : Nat) : (packCode base next).length = 17 := rfl

theorem pack_run (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (packCode base next)) :
    BitRegister.run program (packFuel r) (r.state base) = (packed r).state next := by
  have whole : Segment program base ([.clear 8 (base + 1)] ++
      (packReverseCode (base + 1) (base + 6) ++
        (widthPrefixCode (base + 6) .frontend (base + 11) ++
          (widthPrefixCode (base + 11) .original (base + 16) ++ [.push 8 true next])))) := by
    simpa only [packCode, List.append_assoc] using placed
  have h0 := placed 0 (by rw [packCode_length]; decide)
  simp only [Nat.add_zero, packCode, List.cons_append, BitRegister.lookup] at h0
  have rest1 := Segment.tail _ _ whole
  have rev := Segment.head _ _ rest1
  have rest2 := Segment.tail _ _ rest1
  change Segment program (base + 1 + 5) _ at rest2
  have equal6 : base + 1 + 5 = base + 6 := by omega
  rw [equal6] at rest2
  have fw := Segment.head _ _ rest2
  have rest3 := Segment.tail _ _ rest2
  change Segment program (base + 6 + 5) _ at rest3
  have equal11 : base + 6 + 5 = base + 11 := by omega
  rw [equal11] at rest3
  have ow := Segment.head _ _ rest3
  have ending := Segment.tail _ _ rest3
  change Segment program (base + 11 + 5) _ at ending
  have equal16 : base + 11 + 5 = base + 16 := by omega
  rw [equal16] at ending
  have last := ending 0 (by change 0 < 1; decide)
  simp only [Nat.add_zero, BitRegister.lookup] at last
  have start : BitRegister.run program 1 (r.state base) = ({r with output := []}).state (base + 1) := by
    simp only [BitRegister.run, BitRegister.step, Registers.state, h0,
      Instruction.execute, Instruction.nextControl, Instruction.update]
    rfl
  have fuel : packFuel r = 1 + ((3 * r.reversed.length + 1) +
      ((3 * r.width.length + 3) + ((3 * r.inputs.length + 3) + 1))) := by
    unfold packFuel
    omega
  rw [fuel, BitRegister.run_add, start, BitRegister.run_add,
    packReverse_run program (base + 1) (base + 6) {r with output := []} r.reversed rev]
  simp only [List.append_nil]
  have fwRun := widthPrefix_run program (base + 6) (base + 11) .frontend
    {r with reversed := [], output := r.reversed.reverse} fw
  simp only [WidthKind.value] at fwRun
  rw [BitRegister.run_add, fwRun]
  have owRun := widthPrefix_run program (base + 11) (base + 16) .original
    {r with temp := [], reversed := [], output := List.replicate r.width.length true ++ false :: r.reversed.reverse} ow
  simp only [WidthKind.value] at owRun
  rw [BitRegister.run_add, owRun]
  simp only [BitRegister.run, BitRegister.step, Registers.state, last,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.set, Store.indexCases, packed]

end PNP.Concrete.NANDFrontend
