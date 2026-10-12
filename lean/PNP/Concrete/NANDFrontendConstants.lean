/-
Copyright (c) 2026 PNP Labs.

The two required constant clauses are emitted by the same exact unit writer
used by the frontend. Both source-step cost and byte order are checked.
-/

import PNP.Concrete.NANDFrontendHeader

namespace PNP.Concrete.NANDFrontend

open BitRegister

def constantsCode (base next : Nat) : List (Instruction 9) :=
  [.copy 4 1 (base + 1)] ++ unitCode (base + 1) .left false (base + 32) ++
    [.push 4 true (base + 33)] ++ unitCode (base + 33) .left true next

def constantBits (inputs : Nat) : BitString :=
  encodeTokenPairs (encodeClauseListTokens [unitClause inputs false, unitClause (inputs + 1) true])

def withConstants (r : Registers) : Registers :=
  {r with left := true :: r.inputs, temp := [], reversed := (constantBits r.inputs.length).reverse ++ r.reversed}

def constantsFuel (r : Registers) : Nat := 24 * r.inputs.length + 58

theorem constantsCode_length (base next : Nat) : (constantsCode base next).length = 64 := by
  simp only [constantsCode, List.length_append, unitCode_length]
  rfl

theorem constants_run (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (constantsCode base next)) :
    BitRegister.run program (constantsFuel r) (r.state base) = (withConstants r).state next := by
  have whole : Segment program base ([.copy 4 1 (base + 1)] ++
      (unitCode (base + 1) .left false (base + 32) ++
        ([.push 4 true (base + 33)] ++ unitCode (base + 33) .left true next))) := by
    simpa only [constantsCode, List.append_assoc] using placed
  have h0 := placed 0 (by rw [constantsCode_length]; decide)
  simp only [Nat.add_zero, constantsCode, List.cons_append, BitRegister.lookup] at h0
  have rest1 := Segment.tail _ _ whole
  have low := Segment.head _ _ rest1
  have rest2 := Segment.tail _ _ rest1
  rw [unitCode_length] at rest2
  change Segment program (base + 1 + 31) _ at rest2
  have n32 : base + 1 + 31 = base + 32 := by omega
  rw [n32] at rest2
  have push := Segment.head _ _ rest2
  have h32 := push 0 (by change 0 < 1; decide)
  simp only [Nat.add_zero, BitRegister.lookup] at h32
  have high := Segment.tail _ _ rest2
  change Segment program (base + 32 + 1) _ at high
  have n33 : base + 32 + 1 = base + 33 := by omega
  rw [n33] at high
  let r1 : Registers := {r with left := r.inputs}
  let r2 : Registers := {r1 with
    temp := []
    reversed := (encodeTokenPairs (encodeClauseTokens (unitClause r.inputs.length false))).reverse ++ r.reversed}
  let r3 : Registers := {r2 with left := true :: r.inputs}
  have start : BitRegister.run program 1 (r.state base) = r1.state (base + 1) := by
    simp only [BitRegister.run, BitRegister.step, Registers.state, h0,
      Instruction.execute, Instruction.nextControl, Instruction.update]
    rfl
  have lowRun : BitRegister.run program (12 * r.inputs.length + 22) (r1.state (base + 1)) =
      r2.state (base + 32) := unit_run program (base + 1) (base + 32) .left false r1 low
  have pushRun : BitRegister.run program 1 (r2.state (base + 32)) = r3.state (base + 33) := by
    simp only [BitRegister.run, BitRegister.step, Registers.state, h32,
      Instruction.execute, Instruction.nextControl, Instruction.update]
    rfl
  have highRun := unit_run program (base + 33) next .left true r3 high
  simp only [Operand.value, r3, List.length_cons] at highRun
  have fuel : constantsFuel r = 1 + ((12 * r.inputs.length + 22) +
      (1 + (12 * (r.inputs.length + 1) + 22))) := by
    unfold constantsFuel
    omega
  rw [fuel, BitRegister.run_add, start, BitRegister.run_add, lowRun,
    BitRegister.run_add, pushRun, highRun]
  simp only [withConstants, constantBits, encodeClauseListTokens, encodeTokenPairs_append,
    List.reverse_append, encodeTokenPairs, List.reverse_nil, List.nil_append,
    List.append_assoc, r2, r1]

theorem unitBits_length (index : Nat) (positive : Bool) :
    (encodeTokenPairs (encodeClauseTokens (unitClause index positive))).length = 6 * index + 16 := by
  have encoded := threeBits_exact ⟨positive, index⟩ ⟨positive, index⟩ ⟨positive, index⟩
  change threeBits ⟨positive, index⟩ ⟨positive, index⟩ ⟨positive, index⟩ =
    encodeTokenPairs (encodeClauseTokens (unitClause index positive)) at encoded
  rw [← encoded, threeBits_length]
  change 2 * index + 2 * index + 2 * index + 16 = 6 * index + 16
  omega

theorem constantBits_length (inputs : Nat) : (constantBits inputs).length = 12 * inputs + 38 := by
  simp only [constantBits, encodeClauseListTokens, encodeTokenPairs_append,
    List.length_append, unitBits_length, encodeTokenPairs, List.length_nil]
  omega

end PNP.Concrete.NANDFrontend
