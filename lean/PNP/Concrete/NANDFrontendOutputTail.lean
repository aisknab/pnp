/-
Copyright (c) 2026 PNP Labs.

Final positive output clause, formula terminator and exact record packing.
All source instructions and variable-length output bytes are included.
-/

import PNP.Concrete.NANDFrontendConstants

namespace PNP.Concrete.NANDFrontend

open BitRegister

def outputTailCode (base next : Nat) : List (Instruction 9) :=
  unitCode base .left true (base + 31) ++
    pairCode (base + 31) true false (base + 33) ++ packCode (base + 33) next

def withOutputUnit (r : Registers) : Registers :=
  {r with
    temp := []
    reversed := (encodeTokenPairs (encodeClauseTokens (unitClause r.left.length true))).reverse ++ r.reversed}

def beforeOutputPack (r : Registers) : Registers :=
  {withOutputUnit r with reversed := false :: true :: (withOutputUnit r).reversed}

def outputTailFuel (r : Registers) : Nat :=
  12 * r.left.length + 22 + (2 + packFuel (beforeOutputPack r))

def finishedOutput (r : Registers) : Registers := packed (beforeOutputPack r)

theorem outputTailCode_length (base next : Nat) : (outputTailCode base next).length = 50 := by
  simp only [outputTailCode, List.length_append, unitCode_length, pairCode_length, packCode_length]

theorem outputTail_run (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (outputTailCode base next)) :
    BitRegister.run program (outputTailFuel r) (r.state base) = (finishedOutput r).state next := by
  have whole : Segment program base (unitCode base .left true (base + 31) ++
      (pairCode (base + 31) true false (base + 33) ++ packCode (base + 33) next)) := by
    simpa only [outputTailCode, List.append_assoc] using placed
  have unit := Segment.head _ _ whole
  have rest1 := Segment.tail _ _ whole
  rw [unitCode_length] at rest1
  have pair := Segment.head _ _ rest1
  have pack := Segment.tail _ _ rest1
  rw [pairCode_length] at pack
  have offset : base + 31 + 2 = base + 33 := by omega
  rw [offset] at pack
  have hu := unit_run program base (base + 31) .left true r unit
  change BitRegister.run program (12 * r.left.length + 22) (r.state base) =
    (withOutputUnit r).state (base + 31) at hu
  unfold outputTailFuel
  rw [BitRegister.run_add, hu, BitRegister.run_add,
    pair_run program (base + 31) (base + 33) true false (withOutputUnit r) pair]
  exact pack_run program (base + 33) next (beforeOutputPack r) pack

theorem outputTailFuel_eq (r : Registers) :
    outputTailFuel r =
      30 * r.left.length + 3 * r.reversed.length + 3 * r.width.length + 3 * r.inputs.length + 87 := by
  simp only [outputTailFuel, beforeOutputPack, withOutputUnit, packFuel,
    List.length_cons, List.length_append, List.length_reverse, unitBits_length]
  omega

theorem finishedOutput_data (r : Registers) :
    (finishedOutput r).output =
      true :: (List.replicate r.inputs.length true ++ false ::
        (List.replicate r.width.length true ++ false ::
          (r.reversed.reverse ++
            encodeTokenPairs (encodeClauseTokens (unitClause r.left.length true)) ++ [true, false]))) := by
  simp only [finishedOutput, packed, beforeOutputPack, withOutputUnit,
    List.reverse_cons, List.reverse_append, List.reverse_reverse, List.append_assoc,
    List.cons_append, List.nil_append]

end PNP.Concrete.NANDFrontend
