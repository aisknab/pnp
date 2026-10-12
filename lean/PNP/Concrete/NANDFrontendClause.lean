/-
Copyright (c) 2026 PNP Labs.

Exact execution of the complete three-literal clause block. Every literal
index can have arbitrary finite length; all delimiters and repeated literals
are written by the finite instruction table.
-/

import PNP.Concrete.NANDFrontendLiteral

namespace PNP.Concrete.NANDFrontend

open BitRegister

theorem Segment.head {program : Program 9} {base : Nat}
    (first second : List (Instruction 9)) (whole : Segment program base (first ++ second)) :
    Segment program base first := by
  have checked := Segment.slice [] first second
    (show Segment program base ([] ++ first ++ second) from whole)
  simpa only [List.length_nil, Nat.add_zero] using checked

theorem Segment.tail {program : Program 9} {base : Nat}
    (first second : List (Instruction 9)) (whole : Segment program base (first ++ second)) :
    Segment program (base + first.length) second := by
  apply Segment.slice first second []
  simpa only [List.append_nil] using whole

def Operand.literal (selected : Operand × Bool) (r : Registers) : CNFLiteral :=
  ⟨selected.2, (selected.1.value r).length⟩

def clauseFuel (first second third : Operand × Bool) (r : Registers) : Nat :=
  4 * (first.1.value r).length + 4 * (second.1.value r).length +
    4 * (third.1.value r).length + 22

def clauseBits (first second third : Operand × Bool) (r : Registers) : BitString :=
  threeBits (Operand.literal first r) (Operand.literal second r) (Operand.literal third r)

theorem clause_segments (program : Program 9) (base next : Nat) (first second third : Operand × Bool)
    (placed : Segment program base (clauseCode base first second third next)) :
    Segment program base (pairCode base false true (base + 2)) ∧
    Segment program (base + 2) (literalCode (base + 2) first.1 first.2 (base + 11)) ∧
    Segment program (base + 11) (literalCode (base + 11) second.1 second.2 (base + 20)) ∧
    Segment program (base + 20) (literalCode (base + 20) third.1 third.2 (base + 29)) ∧
    Segment program (base + 29) (pairCode (base + 29) true false next) := by
  have layout : Segment program base
      (pairCode base false true (base + 2) ++
        (literalCode (base + 2) first.1 first.2 (base + 11) ++
          (literalCode (base + 11) second.1 second.2 (base + 20) ++
            (literalCode (base + 20) third.1 third.2 (base + 29) ++
              pairCode (base + 29) true false next)))) := by
    simpa only [clauseCode, List.append_assoc] using placed
  have h0 := Segment.head _ _ layout
  have tail0 : Segment program (base + 2)
      (literalCode (base + 2) first.1 first.2 (base + 11) ++
        (literalCode (base + 11) second.1 second.2 (base + 20) ++
          (literalCode (base + 20) third.1 third.2 (base + 29) ++
            pairCode (base + 29) true false next))) := by
    simpa only [pairCode_length] using Segment.tail _ _ layout
  have h1 := Segment.head _ _ tail0
  have tail1 : Segment program (base + 11)
      (literalCode (base + 11) second.1 second.2 (base + 20) ++
        (literalCode (base + 20) third.1 third.2 (base + 29) ++
          pairCode (base + 29) true false next)) := by
    simpa only [literalCode_length, Nat.add_assoc] using Segment.tail _ _ tail0
  have h2 := Segment.head _ _ tail1
  have tail2 : Segment program (base + 20)
      (literalCode (base + 20) third.1 third.2 (base + 29) ++
        pairCode (base + 29) true false next) := by
    simpa only [literalCode_length, Nat.add_assoc] using Segment.tail _ _ tail1
  have h3 := Segment.head _ _ tail2
  have h4 : Segment program (base + 29) (pairCode (base + 29) true false next) := by
    simpa only [literalCode_length, Nat.add_assoc] using Segment.tail _ _ tail2
  exact ⟨h0, h1, h2, h3, h4⟩

theorem clause_run (program : Program 9) (base next : Nat) (first second third : Operand × Bool)
    (r : Registers) (placed : Segment program base (clauseCode base first second third next)) :
    BitRegister.run program (clauseFuel first second third r) (r.state base) =
      ({r with temp := [], reversed := (clauseBits first second third r).reverse ++ r.reversed}).state next := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := clause_segments program base next first second third placed
  let r1 := {r with reversed := true :: false :: r.reversed}
  let r2 := {r1 with temp := [], reversed := (literalBits first.2 (first.1.value r).length).reverse ++ r1.reversed}
  let r3 := {r2 with temp := [], reversed := (literalBits second.2 (second.1.value r).length).reverse ++ r2.reversed}
  let r4 := {r3 with temp := [], reversed := (literalBits third.2 (third.1.value r).length).reverse ++ r3.reversed}
  have value1 (operand : Operand) : operand.value r1 = operand.value r := by cases operand <;> rfl
  have value2 (operand : Operand) : operand.value r2 = operand.value r := by cases operand <;> rfl
  have value3 (operand : Operand) : operand.value r3 = operand.value r := by cases operand <;> rfl
  have h1 : BitRegister.run program (4 * (first.1.value r).length + 6) (r1.state (base + 2)) =
      r2.state (base + 11) := by
    have checked := literal_run program (base + 2) (base + 11) first.1 first.2 r1 p1
    rw [value1] at checked
    exact checked
  have h2 : BitRegister.run program (4 * (second.1.value r).length + 6) (r2.state (base + 11)) =
      r3.state (base + 20) := by
    have checked := literal_run program (base + 11) (base + 20) second.1 second.2 r2 p2
    rw [value2] at checked
    exact checked
  have h3 : BitRegister.run program (4 * (third.1.value r).length + 6) (r3.state (base + 20)) =
      r4.state (base + 29) := by
    have checked := literal_run program (base + 20) (base + 29) third.1 third.2 r3 p3
    rw [value3] at checked
    exact checked
  have fuel : clauseFuel first second third r =
      2 + ((4 * (first.1.value r).length + 6) +
        ((4 * (second.1.value r).length + 6) + ((4 * (third.1.value r).length + 6) + 2))) := by
    unfold clauseFuel
    omega
  rw [fuel, BitRegister.run_add, pair_run program base (base + 2) false true r p0]
  change BitRegister.run program
    ((4 * (first.1.value r).length + 6) +
      ((4 * (second.1.value r).length + 6) + ((4 * (third.1.value r).length + 6) + 2)))
    (r1.state (base + 2)) = _
  rw [BitRegister.run_add, h1, BitRegister.run_add, h2, BitRegister.run_add, h3,
    pair_run program (base + 29) next true false r4 p4]
  simp only [r4, r3, r2, r1, clauseBits, Operand.literal, threeBits,
    List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append, List.append_assoc]

theorem unit_run (program : Program 9) (base next : Nat) (operand : Operand) (positive : Bool)
    (r : Registers) (placed : Segment program base (unitCode base operand positive next)) :
    BitRegister.run program (12 * (operand.value r).length + 22) (r.state base) =
      ({r with temp := [], reversed :=
        (encodeTokenPairs (encodeClauseTokens (unitClause (operand.value r).length positive))).reverse ++ r.reversed}).state next := by
  have checked := clause_run program base next (operand, positive) (operand, positive) (operand, positive) r placed
  have fuel : clauseFuel (operand, positive) (operand, positive) (operand, positive) r =
      12 * (operand.value r).length + 22 := by
    change 4 * (operand.value r).length + 4 * (operand.value r).length +
      4 * (operand.value r).length + 22 = 12 * (operand.value r).length + 22
    omega
  rw [fuel] at checked
  simpa only [clauseBits, Operand.literal, threeBits_exact, unitClause] using checked

end PNP.Concrete.NANDFrontend
