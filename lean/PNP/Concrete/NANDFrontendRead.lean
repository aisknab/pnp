/-
Copyright (c) 2026 PNP Labs.

Finite decision-tree readers for the circuit frontend. Every branch consumes
one input bit. The execution theorem covers every bitstring, including truncated
inputs, and uses only actual instruction-table placement.
-/

import PNP.Concrete.NANDFrontendClause

namespace PNP.Concrete.NANDFrontend

open BitRegister

inductive ReadTree where
  | leaf (address : Nat)
  | branch (zero one : ReadTree)
deriving Repr

def ReadTree.size : ReadTree → Nat
  | .leaf _ => 0
  | .branch zero one => 3 + zero.size + one.size

def ReadTree.entry : ReadTree → Nat → Nat
  | .leaf address, _ => address
  | .branch _ _, base => base

def ReadTree.code : ReadTree → Nat → Nat → List (Instruction 9)
  | .leaf _, _, _ => []
  | .branch zero one, base, failure =>
      [.branch 0 failure (base + 1) (base + 2),
       .pop 0 (zero.entry (base + 3)),
       .pop 0 (one.entry (base + 3 + zero.size))] ++
        zero.code (base + 3) failure ++ one.code (base + 3 + zero.size) failure

theorem ReadTree.code_length (tree : ReadTree) (base failure : Nat) :
    (tree.code base failure).length = tree.size := by
  induction tree generalizing base with
  | leaf => rfl
  | branch zero one iz io =>
      simp only [ReadTree.code, List.length_append, List.length_cons,
        List.length_nil, iz, io, ReadTree.size]

structure ReadResult where
  fuel : Nat
  rest : BitString
  address : Nat
deriving Repr

def ReadTree.scan : ReadTree → Nat → BitString → ReadResult
  | .leaf address, _, input => ⟨0, input, address⟩
  | .branch _ _, failure, [] => ⟨1, [], failure⟩
  | .branch zero one, failure, bit :: rest =>
      let result := (if bit then one else zero).scan failure rest
      {result with fuel := 2 + result.fuel}

theorem ReadTree.scan_rest_le (tree : ReadTree) (failure : Nat) (input : BitString) :
    (tree.scan failure input).rest.length ≤ input.length := by
  induction tree generalizing input with
  | leaf => simp only [ReadTree.scan]; exact Nat.le_refl _
  | branch zero one iz io =>
      cases input with
      | nil => exact Nat.le_refl _
      | cons bit rest =>
          cases bit
          · exact Nat.le_trans (iz rest) (Nat.le_succ _)
          · exact Nat.le_trans (io rest) (Nat.le_succ _)

def ReadTree.depth : ReadTree → Nat
  | .leaf _ => 0
  | .branch zero one => 1 + max zero.depth one.depth

theorem ReadTree.scan_fuel_le (tree : ReadTree) (failure : Nat) (input : BitString) :
    (tree.scan failure input).fuel ≤ 2 * tree.depth := by
  induction tree generalizing input with
  | leaf => simp only [ReadTree.scan, ReadTree.depth]; exact Nat.le_refl _
  | branch zero one iz io =>
      cases input with
      | nil => simp only [ReadTree.scan, ReadTree.depth]; omega
      | cons bit rest =>
          have hz := iz rest
          have ho := io rest
          cases bit <;> simp only [ReadTree.scan, Bool.false_eq_true, ↓reduceIte,
            ReadTree.depth] <;> omega

theorem ReadTree.run (program : Program 9) (tree : ReadTree) (base failure : Nat)
    (r : Registers) (input : BitString)
    (placed : Segment program base (tree.code base failure)) :
    BitRegister.run program (tree.scan failure input).fuel
        (({r with input := input}).state (tree.entry base)) =
      ({r with input := (tree.scan failure input).rest}).state
        (tree.scan failure input).address := by
  induction tree generalizing base r input with
  | leaf address => simp only [ReadTree.scan, ReadTree.entry, BitRegister.run]
  | branch zero one iz io =>
      have h0 : BitRegister.lookup program.code base =
          some (.branch 0 failure (base + 1) (base + 2)) := by
        simpa only [Nat.add_zero, ReadTree.code, List.cons_append, BitRegister.lookup] using
          placed 0 (by rw [ReadTree.code_length]; simp only [ReadTree.size]; omega)
      have h1 : BitRegister.lookup program.code (base + 1) =
          some (.pop 0 (zero.entry (base + 3))) := by
        simpa only [ReadTree.code, List.cons_append, BitRegister.lookup] using
          placed 1 (by rw [ReadTree.code_length]; simp only [ReadTree.size]; omega)
      have h2 : BitRegister.lookup program.code (base + 2) =
          some (.pop 0 (one.entry (base + 3 + zero.size))) := by
        simpa only [ReadTree.code, List.cons_append, BitRegister.lookup] using
          placed 2 (by rw [ReadTree.code_length]; simp only [ReadTree.size]; omega)
      have pz : Segment program (base + 3) (zero.code (base + 3) failure) := by
        exact Segment.slice _ _ _ placed
      have po : Segment program (base + 3 + zero.size)
          (one.code (base + 3 + zero.size) failure) := by
        have cut := Segment.tail
          ([.branch 0 failure (base + 1) (base + 2),
            .pop 0 (zero.entry (base + 3)),
            .pop 0 (one.entry (base + 3 + zero.size))] ++ zero.code (base + 3) failure)
          (one.code (base + 3 + zero.size) failure) placed
        rw [List.length_append, ReadTree.code_length] at cut
        change Segment program (base + (3 + zero.size)) _ at cut
        simpa only [Nat.add_assoc] using cut
      cases input with
      | nil =>
          simp only [ReadTree.scan, ReadTree.entry, BitRegister.run, BitRegister.step,
            Registers.state, h0, Instruction.execute, Instruction.nextControl,
            Instruction.update, Registers.store, Store.get, Store.indexCases]
      | cons bit rest =>
          have firstSteps : BitRegister.run program 2
              (({r with input := bit :: rest}).state base) =
                ({r with input := rest}).state
                  ((if bit then one else zero).entry
                    (if bit then base + 3 + zero.size else base + 3)) := by
            cases bit <;>
              simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1, h2,
                Instruction.execute, Instruction.nextControl, Instruction.update,
                Registers.store, Store.get, Store.set, Store.indexCases] <;> rfl
          simp only [ReadTree.scan, ReadTree.entry]
          rw [BitRegister.run_add, firstSteps]
          cases bit
          · exact iz (base + 3) r rest pz
          · exact io (base + 3 + zero.size) r rest po

/-- A complete four-bit dispatch table. Leaf addresses are ordinary finite data. -/
def tokenTree (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Nat) :
    ReadTree :=
  .branch
    (.branch
      (.branch (.branch (.leaf a0) (.leaf a1)) (.branch (.leaf a2) (.leaf a3)))
      (.branch (.branch (.leaf a4) (.leaf a5)) (.branch (.leaf a6) (.leaf a7))))
    (.branch
      (.branch (.branch (.leaf a8) (.leaf a9)) (.branch (.leaf a10) (.leaf a11)))
      (.branch (.branch (.leaf a12) (.leaf a13)) (.branch (.leaf a14) (.leaf a15))))

theorem tokenTree_size (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Nat) :
    (tokenTree a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).size = 45 := rfl

theorem tokenTree_depth (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Nat) :
    (tokenTree a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).depth = 4 := rfl

end PNP.Concrete.NANDFrontend
