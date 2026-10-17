import PNP.Concrete.ResidualReduction.SourceActivityFamilyInstructions
import PNP.Concrete.ResidualReduction.SourceDirectionBudget

/-! Compute the actual direction space before constructing its activity
matrix. A protected word retains the original family across both kernels;
the retained computed map and original dimension are transferred by literal
instructions. This prepared phase includes both computations, but its raw
parser and final encoded interface remain separate integration obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceActivityConstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

structure State where
  core : SourceDirectionInstructions.State
  source : BitString
def State.store (r : State) : Store 21 := Frame.join r.core.store (.cons r.source .nil)
def lifted (body : Block 20) : Block 21 := Frame.block 1 body
theorem lifted_exec (body : Block 20) (r : State) (fuel : Nat) (after : SourceDirectionInstructions.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked (.cons r.source .nil)
def family (body : Block 18) : Block 21 := lifted (SourceDirectionInstructions.family body)

def start {n : Nat} (F : Family n) (U : System n) : State := ⟨SourceDirectionInstructions.start F U, []⟩
def saved {n : Nat} (F : Family n) (U : System n) : State := ⟨SourceDirectionInstructions.start F U, familyBits F⟩
def computed {n : Nat} (F : Family n) (U : System n) : State := ⟨SourceDirectionInstructions.result F U, familyBits F⟩
def ready {n : Nat} (F : Family n) (U : System n) (source output : BitString) : State :=
  ⟨⟨SourcePolarFamilyInstructions.ready n (directionSpace F U).parameters
    (mapBits (directionSpace F U).forms) source output, List.replicate n true, (matrixBits U).reverse⟩, []⟩
def result {n : Nat} (F : Family n) (U : System n) : State :=
  ready F U [] (sourceBits F (directionSpace F U))

theorem save_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (.action (.copy (20 : Fin 21) 17)) (start F U).store 1 (saved F U).store := .action _ _
theorem direction_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (lifted SourceDirectionInstructions.block) (saved F U).store
      (SourceDirectionInstructions.fuel F U) (computed F U).store :=
  lifted_exec _ (saved F U) _ _ (SourceDirectionInstructions.block_exec F U)
def prepare : Block 21 := .seq (lifted SourceDirectionInstructions.prepareFamily) <|
  .seq (.action (.copy 17 20)) (.action (.clear 20))
private theorem prepare_space_exec {n : Nat} (s : Space n) (U : System n) (source : BitString) :
    Exec prepare (State.mk (SourceDirectionInstructions.fromKernel ([] : Family n) U s) source).store 7
      (State.mk ⟨SourcePolarFamilyInstructions.ready n s.parameters (mapBits s.forms) source [],
        List.replicate n true, (matrixBits U).reverse⟩ []).store := by
  let before : State := ⟨SourceDirectionInstructions.fromKernel ([] : Family n) U s, source⟩
  let prepared : State := ⟨SourceDirectionInstructions.familyReady ([] : Family n) U s, source⟩
  have moved : Exec (lifted SourceDirectionInstructions.prepareFamily) before.store 5 prepared.store :=
    lifted_exec _ before _ _ (SourceDirectionInstructions.prepareFamily_exec ([] : Family n) U s)
  have restored : Exec (.seq (.action (.copy (17 : Fin 21) 20)) (.action (.clear 20)))
      prepared.store 2
      (State.mk ⟨SourcePolarFamilyInstructions.ready n s.parameters (mapBits s.forms) source [],
        List.replicate n true, (matrixBits U).reverse⟩ []).store :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq moved restored
theorem prepare_exec {n : Nat} (F : Family n) (U : System n) :
    Exec prepare (computed F U).store 7 (ready F U (familyBits F) []).store :=
  prepare_space_exec (directionSpace F U) U (familyBits F)
theorem activity_exec {n : Nat} (F : Family n) (U : System n) :
    Exec (family SourceActivityFamilyInstructions.block) (ready F U (familyBits F) []).store
      (SourceActivityFamilyInstructions.fuel F (directionSpace F U)) (result F U).store :=
  lifted_exec _ (ready F U (familyBits F) []) _ _
    (SourceDirectionInstructions.family_exec _ (ready F U (familyBits F) []).core _ _
      (SourceActivityFamilyInstructions.block_exec F (directionSpace F U)))

def block : Block 21 := .seq (.action (.copy 20 17)) <|
  .seq (lifted SourceDirectionInstructions.block) <| .seq prepare (family SourceActivityFamilyInstructions.block)
def fuel {n : Nat} (F : Family n) (U : System n) : Nat :=
  1 + (SourceDirectionInstructions.fuel F U + (7 + SourceActivityFamilyInstructions.fuel F (directionSpace F U)))
theorem block_exec {n : Nat} (F : Family n) (U : System n) :
    Exec block (start F U).store (fuel F U) (result F U).store :=
  Exec.seq (save_exec F U) (Exec.seq (direction_exec F U) (Exec.seq (prepare_exec F U) (activity_exec F U)))
theorem result_output {n : Nat} (F : Family n) (U : System n) :
    (result F U).store.get 8 = coefficientMatrixBits (activityMatrix (directionSpace F U) F) :=
  sourceBits_matrix F (directionSpace F U)
theorem output_length {n : Nat} (F : Family n) (U : System n) :
    ((result F U).store.get 8).length = F.length * (directionSpace F U).parameters :=
  sourceBits_length F (directionSpace F U)
theorem original_output_bound {n : Nat} (F : Family n) (U : System n) :
    ((result F U).store.get 8).length ≤
      (codec.encode ⟨n, U, F⟩).length * (codec.encode ⟨n, U, F⟩).length := by
  rw [output_length]
  exact Nat.mul_le_mul (SourceDirectionEncoding.family_bound n F U)
    (Nat.le_trans (kernelSpace_parameter_bound (directionSystem F U))
      (SourceDirectionEncoding.dimension_bound n F U))
theorem retained_map {n : Nat} (F : Family n) (U : System n) :
    (result F U).store.get 15 = mapBits (directionSpace F U).forms := rfl
theorem retained_width {n : Nat} (F : Family n) (U : System n) :
    (result F U).store.get 1 = List.replicate ((directionSpace F U).parameters + 1) true := rfl

def activityBudget (L : Nat) : Nat :=
  (130 * (L + 2) * (L + 1) + 1) * L + 1 + (4 * (L * L) + 3)
theorem activity_bound {n : Nat} (F : Family n) (U : System n) :
    SourceActivityFamilyInstructions.fuel F (directionSpace F U) ≤ activityBudget (codec.encode ⟨n, U, F⟩).length := by
  let L := (codec.encode ⟨n, U, F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F U
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F U
  have hk : (directionSpace F U).parameters ≤ L :=
    Nat.le_trans (kernelSpace_parameter_bound (directionSystem F U)) hn
  have coefficient := Nat.mul_le_mul (Nat.mul_le_mul_left 130 (Nat.add_le_add_right hk 2))
    (Nat.add_le_add_right hn 1)
  have scan := Nat.mul_le_mul (Nat.add_le_add_right coefficient 1) hm
  have payload := Nat.mul_le_mul hm hk
  exact Nat.le_trans (SourceActivityFamilyInstructions.fuel_bound F (directionSpace F U))
    (Nat.add_le_add (Nat.add_le_add_right scan 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 4 payload) 3))
def activityPolynomial : NatPolynomial :=
  .add (.add (.mul (.add (.mul (.mul (.constant 130) (.add .variable (.constant 2)))
    (.add .variable (.constant 1))) (.constant 1)) .variable) (.constant 1))
    (.add (.mul (.constant 4) (.mul .variable .variable)) (.constant 3))
theorem activityPolynomial_eval (L : Nat) : activityPolynomial.eval L = activityBudget L := rfl
def costPolynomial : NatPolynomial :=
  .add (.add SourceDirectionBudget.costPolynomial activityPolynomial) (.constant 8)
theorem original_input_bound {n : Nat} (F : Family n) (U : System n) :
    fuel F U ≤ costPolynomial.eval (codec.encode ⟨n, U, F⟩).length := by
  have direction := SourceDirectionBudget.original_input_bound F U
  have activity := activity_bound F U
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, activityPolynomial_eval]
  unfold fuel
  omega
def program : Program 21 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (U : System n) :
    BitRegister.run program (fuel F U + 1) ⟨.running 0, (start F U).store⟩ =
      ⟨.accepted, (result F U).store⟩ := (block_exec F U).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceActivityConstruction
