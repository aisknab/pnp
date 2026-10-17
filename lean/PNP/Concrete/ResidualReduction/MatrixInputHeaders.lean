import PNP.Concrete.ResidualReduction.MatrixInputFields
import PNP.Concrete.ResidualReduction.MatrixReconstructionStep

/-! Literal parsing of both matrix headers from the original input register.
The second terminator flag suffices: a missing first terminator leaves no
unread input from which the second reader could obtain a terminator. -/

namespace PNP.Concrete.ResidualReduction.MatrixInputHeaders
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixStrictHeader
open PNP.Concrete.ResidualReduction.MatrixInputFields

def start (input : BitString) : State :=
  ⟨{base 0 [] with input := input}, [], [], []⟩

def afterFirst (input : BitString) : State :=
  ⟨{base 0 [] with input := (scan input).rest, target := List.replicate (scan input).count true, sign := if (scan input).terminated then [true] else []}, [], [], []⟩

def secondSeed (input : BitString) : State :=
  ⟨{base 0 [] with input := (scan input).rest, sign := if (scan input).terminated then [true] else []},
    List.replicate (scan input).count true, [], []⟩

def result (input : BitString) : State :=
  ⟨{base 0 [] with input := (fields input).payload, target := List.replicate (fields input).rows true, sign := if (fields input).terminated then [true] else []},
    List.replicate (fields input).dimension true, [], []⟩

def saveDimension : Block 12 :=
  .seq (.action (.copy 9 1)) (.action (.clear 1))

def block : Block 12 :=
  .seq (lift MatrixStrictHeader.block)
    (.seq saveDimension (lift MatrixStrictHeader.block))

def fuel (input : BitString) : Nat :=
  blockFuel input + (2 + blockFuel (scan input).rest)

theorem first_exec (input : BitString) :
    Exec (lift MatrixStrictHeader.block) (start input).store
      (blockFuel input) (afterFirst input).store := by
  have core : Exec MatrixStrictHeader.block (start input).core.store
      (blockFuel input) (afterFirst input).core.store := by
    simpa only [start, afterFirst, MatrixStrictHeader.result, base, List.replicate_zero, List.append_nil] using
      MatrixStrictHeader.block_exec input (base 0 [])
  exact lift_exec _ (start input) _ (afterFirst input).core core

theorem saveDimension_exec (input : BitString) :
    Exec saveDimension (afterFirst input).store 2 (secondSeed input).store :=
  Exec.seq (.action _ _) (.action _ _)

theorem second_exec (input : BitString) :
    Exec (lift MatrixStrictHeader.block) (secondSeed input).store
      (blockFuel (scan input).rest) (result input).store := by
  have core : Exec MatrixStrictHeader.block (secondSeed input).core.store
      (blockFuel (scan input).rest) (result input).core.store := by
    cases firstFlag : (scan input).terminated <;>
      cases secondFlag : (scan (scan input).rest).terminated <;>
      simpa only [secondSeed, result, fields, MatrixStrictHeader.result, base,
        List.replicate_zero, List.append_nil, firstFlag, secondFlag,
        Bool.false_eq_true, if_false, if_true] using
        MatrixStrictHeader.block_exec (scan input).rest (secondSeed input).core
  exact lift_exec _ (secondSeed input) _ (result input).core core

theorem block_exec (input : BitString) :
    Exec block (start input).store (fuel input) (result input).store :=
  Exec.seq (first_exec input) (Exec.seq (saveDimension_exec input) (second_exec input))

theorem fuel_bound (input : BitString) : fuel input ≤ 8 * input.length + 20 := by
  have first := MatrixStrictHeader.blockFuel_bound input
  have second := MatrixStrictHeader.blockFuel_bound (scan input).rest
  have size := MatrixStrictHeader.scan_size input
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.MatrixInputHeaders
