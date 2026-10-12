/-
Copyright (c) 2026 PNP Labs.

Exact execution of all three clauses for an arbitrary NAND gate.
The output retains the two repeated gate literals in each positive clause.
-/

import PNP.Concrete.NANDFrontendClause

namespace PNP.Concrete.NANDFrontend

open BitRegister

def gateFuel (r : Registers) : Nat :=
  8 * r.left.length + 8 * r.right.length + 20 * r.gate.length + 66

def gateBits (r : Registers) : BitString :=
  clauseBits (.left, false) (.right, false) (.gate, false) r ++
    clauseBits (.left, true) (.gate, true) (.gate, true) r ++
    clauseBits (.right, true) (.gate, true) (.gate, true) r

theorem gate_segments (program : Program 9) (base next : Nat)
    (placed : Segment program base (gateCode base next)) :
    Segment program base (clauseCode base (.left, false) (.right, false) (.gate, false) (base + 31)) ∧
    Segment program (base + 31)
      (clauseCode (base + 31) (.left, true) (.gate, true) (.gate, true) (base + 62)) ∧
    Segment program (base + 62)
      (clauseCode (base + 62) (.right, true) (.gate, true) (.gate, true) next) := by
  have layout : Segment program base
      (clauseCode base (.left, false) (.right, false) (.gate, false) (base + 31) ++
        (clauseCode (base + 31) (.left, true) (.gate, true) (.gate, true) (base + 62) ++
          clauseCode (base + 62) (.right, true) (.gate, true) (.gate, true) next)) := by
    simpa only [gateCode, List.append_assoc] using placed
  have h0 := Segment.head _ _ layout
  have tail0 : Segment program (base + 31)
      (clauseCode (base + 31) (.left, true) (.gate, true) (.gate, true) (base + 62) ++
        clauseCode (base + 62) (.right, true) (.gate, true) (.gate, true) next) := by
    simpa only [clauseCode_length] using Segment.tail _ _ layout
  have h1 := Segment.head _ _ tail0
  have h2 : Segment program (base + 62)
      (clauseCode (base + 62) (.right, true) (.gate, true) (.gate, true) next) := by
    simpa only [clauseCode_length, Nat.add_assoc] using Segment.tail _ _ tail0
  exact ⟨h0, h1, h2⟩

theorem gate_run (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (gateCode base next)) :
    BitRegister.run program (gateFuel r) (r.state base) =
      ({r with temp := [], reversed := (gateBits r).reverse ++ r.reversed}).state next := by
  obtain ⟨p0, p1, p2⟩ := gate_segments program base next placed
  let r1 := {r with temp := [], reversed :=
    (clauseBits (.left, false) (.right, false) (.gate, false) r).reverse ++ r.reversed}
  let r2 := {r1 with temp := [], reversed :=
    (clauseBits (.left, true) (.gate, true) (.gate, true) r).reverse ++ r1.reversed}
  have h1 : BitRegister.run program
      (clauseFuel (.left, true) (.gate, true) (.gate, true) r) (r1.state (base + 31)) =
        r2.state (base + 62) :=
    clause_run program (base + 31) (base + 62) (.left, true) (.gate, true) (.gate, true) r1 p1
  have fuel : gateFuel r =
      clauseFuel (.left, false) (.right, false) (.gate, false) r +
        (clauseFuel (.left, true) (.gate, true) (.gate, true) r +
          clauseFuel (.right, true) (.gate, true) (.gate, true) r) := by
    simp only [gateFuel, clauseFuel, Operand.value]
    omega
  rw [fuel, BitRegister.run_add,
    clause_run program base (base + 31) (.left, false) (.right, false) (.gate, false) r p0]
  change BitRegister.run program
    (clauseFuel (.left, true) (.gate, true) (.gate, true) r +
      clauseFuel (.right, true) (.gate, true) (.gate, true) r) (r1.state (base + 31)) = _
  rw [BitRegister.run_add, h1]
  have h2 := clause_run program (base + 62) next (.right, true) (.gate, true) (.gate, true) r2 p2
  change BitRegister.run program
      (clauseFuel (.right, true) (.gate, true) (.gate, true) r) (r2.state (base + 62)) =
    ({r2 with temp := [], reversed :=
      (clauseBits (.right, true) (.gate, true) (.gate, true) r).reverse ++ r2.reversed}).state next at h2
  rw [h2]
  simp only [r2, r1, gateBits, List.reverse_append, List.append_assoc]

theorem gateBits_canonical (inputs ordinal : Nat) (gate : LockedNAND.RawGate) (r : Registers) :
    gateBits {r with
      left := List.replicate (sourceIndex inputs gate.left) true
      right := List.replicate (sourceIndex inputs gate.right) true
      gate := List.replicate (inputs + 2 + ordinal) true} =
        encodeTokenPairs (encodeClauseListTokens (gateClauses inputs ordinal gate)) := by
  simp only [gateBits, clauseBits, Operand.literal, Operand.value, List.length_replicate,
    threeBits_exact, gateClauses, encodeClauseListTokens, encodeTokenPairs_append,
    List.append_nil, List.append_assoc]

theorem gateBits_length (r : Registers) :
    (gateBits r).length = 4 * r.left.length + 4 * r.right.length + 10 * r.gate.length + 48 := by
  simp only [gateBits, List.length_append, clauseBits, Operand.literal, Operand.value, threeBits_length]
  omega

theorem gateFuel_length (r : Registers) :
    gateFuel r + 30 = 2 * (gateBits r).length := by
  rw [gateBits_length]
  unfold gateFuel
  omega

end PNP.Concrete.NANDFrontend
