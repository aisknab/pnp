import PNP.Concrete.ResidualReduction.SourcePlaneMatrixProjection
import PNP.Concrete.ResidualReduction.SourceMatrixPacket

/-! Materialize the one extra source row from the two original normal words.
The source-family count is retained from its parsed header. No augmented
family, coefficient matrix, or equation witness is supplied to this phase. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourcePlaneMatrix

structure State where
  core : SourceMatrixPacket.State
  normals : BitString
def State.store (r : State) : Store 17 := Frame.join r.core.store (.cons r.normals .nil)
def registers (r : State) : Registers := r.core.core.core.core
def setRegisters (r : State) (value : Registers) : State :=
  {r with core := SourceMatrixPacket.setCore r.core value}
def lift16 (body : Block 16) : Block 17 := Frame.block 1 body
theorem lift16_exec (body : Block 16) (r : State) (fuel : Nat) (after : SourceMatrixPacket.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift16 body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked (.cons r.normals .nil)
def lift15 (body : Block 15) : Block 17 := lift16 (SourceMatrixPacket.lift15 body)
theorem lift15_exec (body : Block 15) (r : State) (fuel : Nat) (after : SourceMatrixConstruction.State)
    (checked : Exec body r.core.core.store fuel after.store) :
    Exec (lift15 body) r.store fuel ({r with core := {r.core with core := after}}).store :=
  lift16_exec _ r fuel _ (SourceMatrixPacket.lift15_exec body r.core fuel after checked)
def lift9 (body : Block 9) : Block 17 := lift16 (SourceMatrixPacket.lift9 body)
theorem lift9_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body (registers r).store fuel after.store) :
    Exec (lift9 body) r.store fuel (setRegisters r after).store :=
  lift16_exec _ r fuel _ (SourceMatrixPacket.lift9_exec body r.core fuel after checked)

def start {n : Nat} (F : Family n) (alpha beta : Affine n) : State :=
  ⟨SourceMatrixPacket.inputState F, matrixBits [alpha, beta]⟩
def augmentedInput {n : Nat} (F : Family n) (alpha beta : Affine n) : State :=
  ⟨⟨SourceMatrixConstruction.inputState (augmented F alpha beta), List.replicate F.length true⟩,
    matrixBits [alpha, beta]⟩

def seed : Block 17 := .seq (.action (.copy 3 0)) (.action (.clear 0))
def suffix : Block 17 := .seq (.action (.copy 3 8)) <|
  .seq (.action (.copy 8 16)) (.action (.push 8 false))
def restore : Block 17 := .seq (.action (.copy 0 8)) (.action (.clear 8))
def block : Block 17 := .seq seed <| .seq (lift9 ClauseQuery.reverseLoop) <|
  .seq suffix (.seq (lift9 ClauseQuery.reverseLoop) restore)
def fuel {n : Nat} (F : Family n) : Nat := 8 * (familyBits F).length + 9

theorem block_exec {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Exec block (start F alpha beta).store (fuel F) (augmentedInput F alpha beta).store := by
  let before := start F alpha beta
  let staged := setRegisters before {base 0 [] with excess := familyBits F}
  let reversed := setRegisters before {base 0 [] with output := (familyBits F).reverse}
  let secondReady := setRegisters before {base 0 [] with excess := (familyBits F).reverse, output := false :: matrixBits [alpha, beta]}
  let appended := setRegisters before {base 0 [] with output := familyBits F ++ false :: matrixBits [alpha, beta]}
  have seeded : Exec seed before.store 2 staged.store := Exec.seq (.action _ _) (.action _ _)
  have firstCore : Exec ClauseQuery.reverseLoop (registers staged).store
      (4 * (familyBits F).length + 1) (registers reversed).store := by
    simpa only [staged, reversed, registers, setRegisters, SourceMatrixPacket.setCore, base,
      List.append_nil] using ClauseQuery.reverse_exec (base 0 []) (familyBits F)
  have first := lift9_exec ClauseQuery.reverseLoop staged _ (registers reversed) firstCore
  have setupSecond : Exec suffix reversed.store 3 secondReady.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have secondCore : Exec ClauseQuery.reverseLoop (registers secondReady).store
      (4 * (familyBits F).length + 1) (registers appended).store := by
    simpa only [secondReady, appended, registers, setRegisters, SourceMatrixPacket.setCore, base,
      List.length_reverse, List.reverse_reverse] using
      ClauseQuery.reverse_exec {base 0 [] with output := false :: matrixBits [alpha, beta]} (familyBits F).reverse
  have second := lift9_exec ClauseQuery.reverseLoop secondReady _ (registers appended) secondCore
  have restored : Exec restore appended.store 2 (augmentedInput F alpha beta).store := by
    simp only [augmentedInput, SourceMatrixConstruction.inputState, augmented_bits]
    exact Exec.seq (.action _ _) (.action _ _)
  have cost : fuel F = 2 + ((4 * (familyBits F).length + 1) +
      (3 + ((4 * (familyBits F).length + 1) + 2))) := by
    unfold fuel
    omega
  simpa only [block, cost, before] using Exec.seq seeded (Exec.seq first (Exec.seq setupSecond (Exec.seq second restored)))

end PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation
