import PNP.Concrete.ResidualReduction.SourceLinePullbackKernels

/-! One source-derived construction of both exact constrained-query matrices.
All maps and matrices are produced internally and transferred by literal
instructions. Selection, witness lifting and the raw entry boundary remain
downstream obligations; this file does not claim a complete line query. -/

namespace PNP.Concrete.ResidualReduction.SourceLinePullback
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra (coefficientMatrixBits)

def normalPull {n : Nat} (F : Family n) (alpha : Affine n) :
    Matrix (leftSpace F alpha).parameters (rightSpace F alpha).parameters :=
  pullMatrix (SourceLine.normalQueryMatrix F alpha) (leftSpace F alpha) (rightSpace F alpha)
def activityPull {n : Nat} (F : Family n) (alpha : Affine n) :
    Matrix (leftSpace F alpha).parameters (rightSpace F alpha).parameters :=
  pullMatrix (SourceLine.activityQueryMatrix F alpha) (leftSpace F alpha) (rightSpace F alpha)
def normalData {n : Nat} (F : Family n) (alpha : Affine n) : Saved :=
  {kernelData F alpha with pulledNormal := coefficientMatrixBits (normalPull F alpha)}
def resultData {n : Nat} (F : Family n) (alpha : Affine n) : Saved :=
  {normalData F alpha with pulledActivity := coefficientMatrixBits (activityPull F alpha)}

def pullWords (matrix leftMap rightMap leftWidth rightWidth : BitString) : SourceBilinearPullback.State :=
  ⟨⟨⟨base 0 [], []⟩, matrix, leftMap, rightMap, leftWidth, rightWidth, [], [], []⟩, [], [], []⟩
def resetForPull : Block 38 := Frame.block 26 clearSolver
theorem resetForPull_exec (r : MatrixReconstruction.State) (data : Saved) :
    Exec resetForPull (solverStore r data) 12 (pullStore (pullWords [] [] [] [] []) data) :=
  Frame.execution (clearSolver_exec r) (solverFrame data)
def loadPull : Block 38 := .seq (.action (.copy 10 30)) <|
  .seq (.action (.copy 11 32)) <| .seq (.action (.copy 12 34)) <|
  .seq (.action (.copy 13 33)) (.action (.copy 14 35))
private theorem loadPull_exec (data : Saved) :
    Exec loadPull (pullStore (pullWords [] [] [] [] []) data) 5
      (pullStore (pullWords data.normalMatrix data.leftMap data.rightMap data.leftWidth data.rightWidth) data) := by
  let r := pullWords [] [] [] [] []
  let a := pullWords data.normalMatrix [] [] [] []
  let b := pullWords data.normalMatrix data.leftMap [] [] []
  let c := pullWords data.normalMatrix data.leftMap data.rightMap [] []
  let d := pullWords data.normalMatrix data.leftMap data.rightMap data.leftWidth []
  let e := pullWords data.normalMatrix data.leftMap data.rightMap data.leftWidth data.rightWidth
  have first : Exec (.action (.copy (10 : Fin 38) 30)) (pullStore r data) 1 (pullStore a data) :=
    copy_from_saved r.store (pullFrame data) 10 9
  have second : Exec (.action (.copy (11 : Fin 38) 32)) (pullStore a data) 1 (pullStore b data) :=
    copy_from_saved a.store (pullFrame data) 11 11
  have third : Exec (.action (.copy (12 : Fin 38) 34)) (pullStore b data) 1 (pullStore c data) :=
    copy_from_saved b.store (pullFrame data) 12 13
  have fourth : Exec (.action (.copy (13 : Fin 38) 33)) (pullStore c data) 1 (pullStore d data) :=
    copy_from_saved c.store (pullFrame data) 13 12
  have fifth : Exec (.action (.copy (14 : Fin 38) 35)) (pullStore d data) 1 (pullStore e data) :=
    copy_from_saved d.store (pullFrame data) 14 14
  exact Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth fifth)))
private theorem normalStart_words {n : Nat} (F : Family n) (alpha : Affine n) :
    pullWords (kernelData F alpha).normalMatrix (kernelData F alpha).leftMap
      (kernelData F alpha).rightMap (kernelData F alpha).leftWidth (kernelData F alpha).rightWidth =
      SourceBilinearPullback.start (SourceLine.normalQueryMatrix F alpha) (leftSpace F alpha) (rightSpace F alpha) := by
  have bytes : SourceLineQueryMatrices.normalBytes F alpha =
      coefficientMatrixBits (SourceLine.normalQueryMatrix F alpha) :=
    (SourceLineQueryMatrixAlgebra.normal_query_bytes F alpha).symm
  change pullWords (SourceLineQueryMatrices.normalBytes F alpha)
    (mapBits (leftSpace F alpha).forms) (mapBits (rightSpace F alpha).forms)
    (List.replicate (leftSpace F alpha).parameters true) (List.replicate (rightSpace F alpha).parameters true) = _
  rw [bytes]
  rfl

def normalStart {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  pullStore (SourceBilinearPullback.start (SourceLine.normalQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (kernelData F alpha)
def prepareNormal : Block 38 := .seq resetForPull loadPull
theorem prepareNormal_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepareNormal (kernelsDone F alpha) 17 (normalStart F alpha) := by
  have loaded := loadPull_exec (kernelData F alpha)
  rw [normalStart_words] at loaded
  exact Exec.seq
    (resetForPull_exec (MatrixSolutionSerialization.result (rightSpace F alpha)) (kernelData F alpha)) loaded
def pull : Block 38 := Frame.block 17 SourceBilinearPullback.block
def pullFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceBilinearPullback.fuel (n + F.length) (directionSpace F [alpha]).parameters
    (leftSpace F alpha).parameters (rightSpace F alpha).parameters
def normalDone {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  pullStore (SourceBilinearPullback.result (SourceLine.normalQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (kernelData F alpha)
theorem normal_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec pull (normalStart F alpha) (pullFuel F alpha) (normalDone F alpha) :=
  Frame.execution (SourceBilinearPullback.block_exec (SourceLine.normalQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (pullFrame (kernelData F alpha))

def saveNormal : Block 38 := .action (.copy 36 8)
private theorem saveNormal_words (r : SourceBilinearPullback.State) (data : Saved) :
    Exec saveNormal (pullStore r data) 1
      (pullStore r {data with pulledNormal := (SourceBilinearPullback.registers r).output}) :=
  copy_to_saved r.store (pullFrame data) 15 8
def normalSaved {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  pullStore (SourceBilinearPullback.result (SourceLine.normalQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (normalData F alpha)
theorem saveNormal_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec saveNormal (normalDone F alpha) 1 (normalSaved F alpha) :=
  saveNormal_words (SourceBilinearPullback.result (SourceLine.normalQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (kernelData F alpha)

def retarget (r : SourceBilinearPullback.State) (matrix : BitString) : SourceBilinearPullback.State :=
  let cleared := SourceBilinearPullback.setRegisters r {SourceBilinearPullback.registers r with output := []}
  {cleared with core := {cleared.core with matrix := matrix, leftIndex := []}}
def prepareActivity : Block 38 := .seq (.action (.clear 8)) <|
  .seq (.action (.clear 15)) (.action (.copy 10 31))
private theorem prepareActivity_words (r : SourceBilinearPullback.State) (data : Saved) :
    Exec prepareActivity (pullStore r data) 3 (pullStore (retarget r data.activityMatrix) data) := by
  let a := SourceBilinearPullback.setRegisters r {SourceBilinearPullback.registers r with output := []}
  let b := {a with core := {a.core with leftIndex := []}}
  have first : Exec (.action (.clear (8 : Fin 38))) (pullStore r data) 1 (pullStore a data) :=
    clear_core r.store (pullFrame data) 8
  have second : Exec (.action (.clear (15 : Fin 38))) (pullStore a data) 1 (pullStore b data) :=
    clear_core a.store (pullFrame data) 15
  have third : Exec (.action (.copy (10 : Fin 38) 31)) (pullStore b data) 1
      (pullStore (retarget r data.activityMatrix) data) := copy_from_saved b.store (pullFrame data) 10 10
  exact Exec.seq first (Exec.seq second third)
private theorem retarget_result {m n : Nat} (M N : Matrix m n) (s : Space m) (t : Space n) :
    retarget (SourceBilinearPullback.result M s t) (coefficientMatrixBits N) =
      SourceBilinearPullback.start N s t := rfl
def activityStart {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  pullStore (SourceBilinearPullback.start (SourceLine.activityQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (normalData F alpha)
theorem prepareActivity_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepareActivity (normalSaved F alpha) 3 (activityStart F alpha) := by
  have bytes : (normalData F alpha).activityMatrix = coefficientMatrixBits (SourceLine.activityQueryMatrix F alpha) :=
    (SourceLineQueryMatrixAlgebra.activity_query_bytes F alpha).symm
  have checked := prepareActivity_words (SourceBilinearPullback.result (SourceLine.normalQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (normalData F alpha)
  rw [bytes, retarget_result] at checked
  exact checked
def activityDone {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  pullStore (SourceBilinearPullback.result (SourceLine.activityQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (normalData F alpha)
theorem activity_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec pull (activityStart F alpha) (pullFuel F alpha) (activityDone F alpha) :=
  Frame.execution (SourceBilinearPullback.block_exec (SourceLine.activityQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (pullFrame (normalData F alpha))
def saveActivity : Block 38 := .action (.copy 37 8)
private theorem saveActivity_words (r : SourceBilinearPullback.State) (data : Saved) :
    Exec saveActivity (pullStore r data) 1
      (pullStore r {data with pulledActivity := (SourceBilinearPullback.registers r).output}) :=
  copy_to_saved r.store (pullFrame data) 16 8
def result {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  pullStore (SourceBilinearPullback.result (SourceLine.activityQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (resultData F alpha)
theorem saveActivity_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec saveActivity (activityDone F alpha) 1 (result F alpha) :=
  saveActivity_words (SourceBilinearPullback.result (SourceLine.activityQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)) (normalData F alpha)

def block : Block 38 := .seq kernels <| .seq prepareNormal <| .seq pull <|
  .seq saveNormal <| .seq prepareActivity <| .seq pull saveActivity
def fuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  kernelsFuel F alpha + (17 + (pullFuel F alpha + (1 + (3 + (pullFuel F alpha + 1)))))
theorem block_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec block (start F alpha) (fuel F alpha) (result F alpha) :=
  Exec.seq (kernels_exec F alpha) <| Exec.seq (prepareNormal_exec F alpha) <|
    Exec.seq (normal_exec F alpha) <| Exec.seq (saveNormal_exec F alpha) <|
    Exec.seq (prepareActivity_exec F alpha) <| Exec.seq (activity_exec F alpha) (saveActivity_exec F alpha)
def program : Program 38 := block.program 0 37
theorem program_run {n : Nat} (F : Family n) (alpha : Affine n) :
    BitRegister.run program (fuel F alpha + 1) ⟨.running 0, start F alpha⟩ =
      ⟨.accepted, result F alpha⟩ := (block_exec F alpha).program_run 0 37

theorem result_normal {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).get 36 = coefficientMatrixBits (normalPull F alpha) :=
  Frame.get_frame _ (pullFrame (resultData F alpha)) 15
theorem result_activity {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).get 37 = coefficientMatrixBits (activityPull F alpha) :=
  Frame.get_frame _ (pullFrame (resultData F alpha)) 16
theorem retained_direction {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).get 28 = mapBits (directionSpace F [alpha]).forms :=
  Frame.get_frame _ (pullFrame (resultData F alpha)) 7
theorem retained_left_map {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).get 32 = mapBits (leftSpace F alpha).forms :=
  Frame.get_frame _ (pullFrame (resultData F alpha)) 11
theorem retained_right_map {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).get 34 = mapBits (rightSpace F alpha).forms :=
  Frame.get_frame _ (pullFrame (resultData F alpha)) 13

private theorem query_with_spaces {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) (s : Space m) (t : Space n)
    (hs : solve m (homogeneous rs) = some s) (ht : solve n (homogeneous ts) = some t) :
    query rs ts A C =
      (BilinearSelection.select (pullMatrix A s t) (pullMatrix C s t)).witness.map
        (fun w => (s.direction (sumUnits w.1), t.direction (sumUnits w.2))) := by
  simp only [query, hs, ht]
  cases (BilinearSelection.select (pullMatrix A s t) (pullMatrix C s t)).witness <;> rfl

/-- The transformed matrices are the exact inputs of the existing ordered
selector, not merely matrices admitting an equivalent witness. -/
theorem exact_query_interface {n : Nat} (F : Family n) (alpha : Affine n) :
    SourceLine.lineRawQuery F alpha =
      (BilinearSelection.select (normalPull F alpha) (activityPull F alpha)).witness.map
        (fun w => ((leftSpace F alpha).direction (sumUnits w.1),
          (rightSpace F alpha).direction (sumUnits w.2))) := by
  rw [SourceLine.lineRawQuery_eq]
  exact query_with_spaces (SourceLine.rankOneRows F alpha) []
    (SourceLine.normalQueryMatrix F alpha) (SourceLine.activityQueryMatrix F alpha)
    (leftSpace F alpha) (rightSpace F alpha)
    (kernelSpace_spec (SourceLine.rankOneRows F alpha)) (kernelSpace_spec [])

end PNP.Concrete.ResidualReduction.SourceLinePullback
