import PNP.Concrete.ResidualReduction.MatrixReconstructionLoop

/-! Literal canonical serialization of the computed complete solution Space.
The parameter header is constructed by a counted unary loop and then tagged;
its cost is included in the complete prepared-matrix solver phase. -/

namespace PNP.Concrete.ResidualReduction.MatrixSolutionSerialization
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixReconstruction

private theorem replicate_snoc (width : Nat) (output : BitString) :
    List.replicate width true ++ true :: output =
      List.replicate (width + 1) true ++ output := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simpa only [List.replicate_succ, List.cons_append] using
      congrArg (List.cons true) ih

def unaryBody : Block 9 := .seq (.action (.push 8 true)) (.action (.pop 2))
def unaryLoop : Block 9 := .loop 2 unaryBody

theorem unaryLoop_exec (r : Registers) (width : Nat) :
    Exec unaryLoop ({r with remaining := List.replicate width true}).store
      (3 * width + 1)
      ({r with remaining := [], output := List.replicate width true ++ r.output}).store := by
  induction width generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ width ih =>
    have step : Exec unaryBody
        ({r with remaining := List.replicate (width + 1) true}).store 2
        ({r with remaining := List.replicate width true, output := true :: r.output}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step
      (ih {r with output := true :: r.output})
    have word := replicate_snoc width r.output
    have cost : 3 * (width + 1) + 1 = 1 + (2 + (3 * width + 1)) := by omega
    rw [cost]
    simpa only [unaryLoop, word] using checked

theorem solution_some_bits {n : Nat} (s : Space n) :
    (solutionCodec n).encode (some s) =
      true :: (List.replicate s.parameters true ++ false :: mapBits s.forms) := by
  change true :: (NativeNormalization.NativeBitCodec.natural s.parameters ++
    (mapCodec n s.parameters).encode s.forms) = _
  rw [mapCodec_bits]
  simp only [NativeNormalization.NativeBitCodec.natural, List.append_assoc,
    List.cons_append, List.nil_append]

def prepare : Block 9 :=
  .seq (.action (.copy 2 1)) <| .seq (.action (.pop 2)) <|
    .seq (.action (.copy 8 0)) (.action (.push 8 false))
def block : Block 9 := .seq prepare (.seq unaryLoop (.action (.push 8 true)))

def coreResult {n : Nat} (s : Space n) : Registers :=
  {(ready s [] []).core with output := (solutionCodec n).encode (some s)}

theorem block_exec {n : Nat} (s : Space n) :
    Exec block (ready s [] []).core.store (3 * s.parameters + 6) (coreResult s).store := by
  let r := (ready s [] []).core
  have prepared : Exec prepare r.store 4
      ({r with remaining := List.replicate s.parameters true, output := false :: mapBits s.forms}).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have copied : Exec unaryLoop
      ({r with remaining := List.replicate s.parameters true, output := false :: mapBits s.forms}).store
      (3 * s.parameters + 1)
      ({r with output := List.replicate s.parameters true ++ false :: mapBits s.forms}).store := by
    simpa only [r, ready, base] using
      unaryLoop_exec {r with output := false :: mapBits s.forms} s.parameters
  have tagged : Exec (.action (.push (8 : Fin 9) true))
      ({r with output := List.replicate s.parameters true ++ false :: mapBits s.forms}).store 1
      ({r with output := true :: (List.replicate s.parameters true ++ false :: mapBits s.forms)}).store := .action _ _
  have checked := Exec.seq prepared (Exec.seq copied tagged)
  have cost : 3 * s.parameters + 6 = 4 + ((3 * s.parameters + 1) + 1) := by omega
  simpa only [block, coreResult, solution_some_bits, r, cost] using checked

def result {n : Nat} (s : Space n) : State :=
  {ready s [] [] with core := coreResult s}

theorem lifted_exec {n : Nat} (s : Space n) :
    Exec (lift block) (ready s [] []).store (3 * s.parameters + 6) (result s).store :=
  lift_exec block (ready s [] []) _ (coreResult s) (block_exec s)

end PNP.Concrete.ResidualReduction.MatrixSolutionSerialization
