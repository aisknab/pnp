import PNP.Concrete.ResidualReduction.SourceLineMatrixEncoding

/-! Literal construction of the synthetic rank-one rows. The coordinate loop
is bounded by the original dimension and emits each full unit covector.
Every copy, emitted bit and loop test is charged; no row oracle is used. -/

namespace PNP.Concrete.ResidualReduction.SourceLineMatrixRows
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceLineMatrix
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation

def ready {n : Nat} (rows : Nat) (alpha : Affine n) (i remaining : Nat) (output : BitString) : State :=
  ⟨⟨SourceMatrixConstruction.ready ([] : Family n) i 0 remaining 0 output,
    List.replicate rows true⟩, affineWord alpha⟩

def rowSeed : Block 17 := .seq (.action (.push 8 false)) (.action (.copy 3 16))
def unitSeed : Block 17 := .seq (.action (.copy 1 10)) (.action (.copy 2 9))
def rowBlock : Block 17 := .seq rowSeed <| .seq (lift9 ClauseQuery.reverseLoop) <|
  .seq unitSeed (.seq (lift9 SourceUnitDirectionInstructions.block) (.action (.push 8 false)))
def rowFuel (n i : Nat) : Nat := SourceUnitDirectionInstructions.fuel n i + 4 * (n + 1) + 6

theorem rowBlock_exec {n : Nat} (rows : Nat) (alpha : Affine n) (i : Fin n)
    (remaining : Nat) (output : BitString) :
    Exec rowBlock (ready rows alpha i.val remaining output).store (rowFuel n i.val)
      (ready rows alpha i.val remaining ((rowBytes alpha i.val).reverse ++ output)).store := by
  let before := ready rows alpha i.val remaining output
  let staged := setRegisters before {base 0 [] with excess := affineWord alpha, output := false :: output}
  let afterAlpha := ready rows alpha i.val remaining ((affineWord alpha).reverse ++ false :: output)
  let unitReady := setRegisters afterAlpha {registers afterAlpha with
    target := List.replicate i.val true, remaining := List.replicate n true}
  let afterUnit := ready rows alpha i.val remaining
    ((SourceUnitDirectionInstructions.word n i.val).reverse ++ (affineWord alpha).reverse ++ false :: output)
  have seeded : Exec rowSeed before.store 2 staged.store :=
    Exec.seq (.action _ _) (.action _ _)
  have alphaCore : Exec ClauseQuery.reverseLoop (registers staged).store
      (4 * (n + 1) + 1) (registers afterAlpha).store := by
    simpa only [staged, before, afterAlpha, ready, registers, setRegisters,
      SourceMatrixPacket.setCore, SourceMatrixConstruction.ready,
      SourcePolarInstructions.working, base, affineWord_length] using
      ClauseQuery.reverse_exec {base 0 [] with output := false :: output} (affineWord alpha)
  have alphaExec : Exec (lift9 ClauseQuery.reverseLoop) staged.store
      (4 * (n + 1) + 1) afterAlpha.store :=
    lift9_exec _ staged _ (registers afterAlpha) alphaCore
  have prepared : Exec unitSeed afterAlpha.store 2 unitReady.store :=
    Exec.seq (.action _ _) (.action _ _)
  have unitCore : Exec SourceUnitDirectionInstructions.block (registers unitReady).store
      (SourceUnitDirectionInstructions.fuel n i.val) (registers afterUnit).store := by
    simpa only [unitReady, afterAlpha, afterUnit, ready, registers, setRegisters,
      SourceMatrixPacket.setCore, SourceMatrixConstruction.ready,
      SourcePolarInstructions.working, base, SourceUnitDirectionInstructions.unit_bytes,
      List.replicate_zero, List.append_assoc] using
      SourceUnitDirectionInstructions.block_exec (registers afterAlpha) n i
  have unitExec : Exec (lift9 SourceUnitDirectionInstructions.block) unitReady.store
      (SourceUnitDirectionInstructions.fuel n i.val) afterUnit.store :=
    lift9_exec _ unitReady _ (registers afterUnit) unitCore
  have constant : Exec (.action (.push (8 : Fin 17) false)) afterUnit.store 1
      (ready rows alpha i.val remaining ((rowBytes alpha i.val).reverse ++ output)).store := by
    simp only [afterUnit, rowBytes, List.reverse_cons, List.reverse_append, List.reverse_nil,
      List.cons_append, List.nil_append, List.append_assoc]
    exact .action _ _
  have cost : rowFuel n i.val =
      2 + ((4 * (n + 1) + 1) + (2 + (SourceUnitDirectionInstructions.fuel n i.val + 1))) := by
    unfold rowFuel
    omega
  simpa only [rowBlock, cost, before] using
    Exec.seq seeded (Exec.seq alphaExec (Exec.seq prepared (Exec.seq unitExec constant)))

theorem rowFuel_bound (n : Nat) (i : Fin n) : rowFuel n i.val ≤ 8 * n + 10 := by
  have unit := SourceUnitDirectionInstructions.fuel_bound n i
  unfold rowFuel
  omega

def advance : Block 17 := .seq (.action (.push 10 true)) (.action (.pop 13))
def step : Block 17 := .seq rowBlock advance
theorem step_exec {n : Nat} (rows : Nat) (alpha : Affine n) (i : Fin n)
    (remaining : Nat) (output : BitString) :
    Exec step (ready rows alpha i.val (remaining + 1) output).store (rowFuel n i.val + 2)
      (ready rows alpha (i.val + 1) remaining ((rowBytes alpha i.val).reverse ++ output)).store := by
  have moved : Exec advance
      (ready rows alpha i.val (remaining + 1) ((rowBytes alpha i.val).reverse ++ output)).store 2
      (ready rows alpha (i.val + 1) remaining ((rowBytes alpha i.val).reverse ++ output)).store :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq (rowBlock_exec rows alpha i (remaining + 1) output) moved

def loop : Block 17 := .loop 13 step
def loopFuel (n : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, count + 1 => 1 + ((rowFuel n i + 2) + loopFuel n (i + 1) count)
theorem loop_exec {n : Nat} (rows : Nat) (alpha : Affine n)
    (count i : Nat) (output : BitString) (bound : i + count ≤ n) :
    Exec loop (ready rows alpha i count output).store (loopFuel n i count)
      (ready rows alpha (i + count) 0 ((rowsBytes alpha i count).reverse ++ output)).store := by
  induction count generalizing i output with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have hi : i < n := by omega
    let current : Fin n := ⟨i, hi⟩
    have one := step_exec rows alpha current count output
    have rest := ih (i + 1) ((rowBytes alpha i).reverse ++ output) (by omega)
    have checked := Exec.loopStep (source := (13 : Fin 17)) rfl one rest
    have index : i + 1 + count = i + (count + 1) := by omega
    simpa only [loop, loopFuel, current, rowsBytes_succ, List.reverse_append,
      List.append_assoc, index] using checked

theorem loopFuel_bound (n count i : Nat) (bound : i + count ≤ n) :
    loopFuel n i count ≤ (8 * n + 13) * count + 1 := by
  induction count generalizing i with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have hi : i < n := by omega
    have one := rowFuel_bound n ⟨i, hi⟩
    have rest := ih (i + 1) (by omega)
    simp only [loopFuel, Nat.mul_add, Nat.mul_one] at one rest ⊢
    omega

end PNP.Concrete.ResidualReduction.SourceLineMatrixRows
