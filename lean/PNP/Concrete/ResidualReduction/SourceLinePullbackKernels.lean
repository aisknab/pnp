import PNP.Concrete.ResidualReduction.SourceLinePullbackState

/-! Compute the exact two constrained-query solution maps. The right system
has no equations, but its map is still produced by the checked solver: no
unproved identity-map or basis-order convention is substituted. -/

namespace PNP.Concrete.ResidualReduction.SourceLinePullback
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def leftSpace {n : Nat} (F : Family n) (alpha : Affine n) : Space (n + F.length) :=
  kernelSpace (SourceLine.rankOneRows F alpha)
def rightSpace {n : Nat} (F : Family n) (alpha : Affine n) :
    Space (directionSpace F [alpha]).parameters :=
  kernelSpace ([] : System (directionSpace F [alpha]).parameters)
def leftData {n : Nat} (F : Family n) (alpha : Affine n) : Saved :=
  {derivedData F alpha with
    leftMap := mapBits (leftSpace F alpha).forms,
    leftWidth := List.replicate (leftSpace F alpha).parameters true}
def kernelData {n : Nat} (F : Family n) (alpha : Affine n) : Saved :=
  {leftData F alpha with
    rightMap := mapBits (rightSpace F alpha).forms,
    rightWidth := List.replicate (rightSpace F alpha).parameters true}

def lineWords (data : Saved) : SourcePlaneMatrixAugmentation.State :=
  ⟨⟨⟨⟨{base 0 [] with input := data.source}, data.dimension, [], []⟩,
    [], [], []⟩, data.rows⟩, data.normal⟩
def loadLeftData : Block 38 := .seq (.action (.copy 0 24)) <|
  .seq (.action (.clear 1)) (.action (.clear 8))
def loadLeftMeta : Block 38 := .seq (.action (.copy 9 26)) <|
  .seq (.action (.copy 15 27)) (.action (.copy 16 25))
def clearLeftTail : Block 38 := .seq (.action (.clear 18)) <|
  .seq (.action (.clear 19)) <| .seq (.action (.clear 21)) <|
  .seq (.action (.clear 22)) (.action (.clear 23))
def prepareLeft : Block 38 := .seq loadLeftData (.seq loadLeftMeta clearLeftTail)
def leftDataState (r : SourceLineQueryMatrices.State) (data : Saved) : SourceLineQueryMatrices.State :=
  SourceLineQueryMatrices.setRegisters r
    {SourceLineQueryMatrices.registers r with input := data.source, target := [], output := []}
def leftMetaState (r : SourceLineQueryMatrices.State) (data : Saved) : SourceLineQueryMatrices.State :=
  {r with core := {r.core with core := {r.core.core with family := {r.core.core.family with core :=
    {r.core.core.family.core with width := data.dimension, map := data.rows, savedOutput := data.normal}}}}}
def leftTailState (r : SourceLineQueryMatrices.State) : SourceLineQueryMatrices.State :=
  {r with
    core := {r.core with core := {r.core.core with dimension := [], normals := []}},
    rows := [], normal := [], activity := []}

private theorem loadLeftData_exec (r : SourceLineQueryMatrices.State) (data : Saved) :
    Exec loadLeftData (matricesStore r data) 3 (matricesStore (leftDataState r data) data) := by
  let a := SourceLineQueryMatrices.setRegisters r
    {SourceLineQueryMatrices.registers r with input := data.source}
  let b := SourceLineQueryMatrices.setRegisters a
    {SourceLineQueryMatrices.registers a with target := []}
  have first : Exec (.action (.copy (0 : Fin 38) 24)) (matricesStore r data) 1 (matricesStore a data) :=
    copy_from_saved r.store data.store 0 0
  have second : Exec (.action (.clear (1 : Fin 38))) (matricesStore a data) 1 (matricesStore b data) :=
    clear_core a.store data.store 1
  have third : Exec (.action (.clear (8 : Fin 38))) (matricesStore b data) 1
      (matricesStore (leftDataState r data) data) := clear_core b.store data.store 8
  exact Exec.seq first (Exec.seq second third)
private theorem loadLeftMeta_exec (r : SourceLineQueryMatrices.State) (data : Saved) :
    Exec loadLeftMeta (matricesStore r data) 3 (matricesStore (leftMetaState r data) data) := by
  let a := {r with core := {r.core with core := {r.core.core with family := {r.core.core.family with core :=
    {r.core.core.family.core with width := data.dimension}}}}}
  let b := {a with core := {a.core with core := {a.core.core with family := {a.core.core.family with core :=
    {a.core.core.family.core with map := data.rows}}}}}
  have first : Exec (.action (.copy (9 : Fin 38) 26)) (matricesStore r data) 1 (matricesStore a data) :=
    copy_from_saved r.store data.store 9 2
  have second : Exec (.action (.copy (15 : Fin 38) 27)) (matricesStore a data) 1 (matricesStore b data) :=
    copy_from_saved a.store data.store 15 3
  have third : Exec (.action (.copy (16 : Fin 38) 25)) (matricesStore b data) 1
      (matricesStore (leftMetaState r data) data) := copy_from_saved b.store data.store 16 1
  exact Exec.seq first (Exec.seq second third)
private theorem clearLeftTail_exec (r : SourceLineQueryMatrices.State) (data : Saved) :
    Exec clearLeftTail (matricesStore r data) 5 (matricesStore (leftTailState r) data) := by
  let a := {r with core := {r.core with core := {r.core.core with dimension := []}}}
  let b := {a with core := {a.core with core := {a.core.core with normals := []}}}
  let c := {b with rows := []}
  let d := {c with normal := []}
  have first : Exec (.action (.clear (18 : Fin 38))) (matricesStore r data) 1 (matricesStore a data) :=
    clear_core r.store data.store 18
  have second : Exec (.action (.clear (19 : Fin 38))) (matricesStore a data) 1 (matricesStore b data) :=
    clear_core a.store data.store 19
  have third : Exec (.action (.clear (21 : Fin 38))) (matricesStore b data) 1 (matricesStore c data) :=
    clear_core b.store data.store 21
  have fourth : Exec (.action (.clear (22 : Fin 38))) (matricesStore c data) 1 (matricesStore d data) :=
    clear_core c.store data.store 22
  have fifth : Exec (.action (.clear (23 : Fin 38))) (matricesStore d data) 1
      (matricesStore (leftTailState r) data) := clear_core d.store data.store 23
  exact Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth fifth)))

private def matrixWords (n k : Nat) (map normal activity normals rows : BitString) :
    SourceLineQueryMatrices.State :=
  ⟨⟨⟨{SourcePolarFamilyInstructions.ready n k map [] [] with core :=
    { (SourcePolarFamilyInstructions.ready n k map [] []).core with core :=
      {base k [] with output := normal}}}, List.replicate n true, normals⟩, []⟩, rows, normal, activity⟩
/- This compares a fixed 38-register layout with abstract word fields only. -/
set_option maxHeartbeats 800000 in
private theorem preparedLeft_store (n k : Nat) (map normal activity normals rows : BitString) (data : Saved) :
    matricesStore (leftTailState (leftMetaState
      (leftDataState (matrixWords n k map normal activity normals rows) data) data)) data =
      lineStore (lineWords data) data := rfl
private theorem prepareLeft_words (n k : Nat) (map normal activity normals rows : BitString) (data : Saved) :
    Exec prepareLeft (matricesStore (matrixWords n k map normal activity normals rows) data) 11
      (lineStore (lineWords data) data) := by
  let r := matrixWords n k map normal activity normals rows
  have checked : Exec prepareLeft (matricesStore r data) 11
      (matricesStore (leftTailState (leftMetaState (leftDataState r data) data)) data) :=
    Exec.seq (loadLeftData_exec r data)
      (Exec.seq (loadLeftMeta_exec (leftDataState r data) data)
        (clearLeftTail_exec (leftMetaState (leftDataState r data) data) data))
  rw [preparedLeft_store] at checked
  exact checked
private theorem lineWords_source {n : Nat} (F : Family n) (alpha : Affine n) :
    lineWords (derivedData F alpha) = SourceLineMatrixAugmentation.start F alpha := by
  unfold lineWords derivedData sourceData
  simp only [matrixBits, List.append_nil]
  rfl
def leftStart {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  lineStore (SourceLineMatrixAugmentation.start F alpha) (derivedData F alpha)
theorem prepareLeft_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepareLeft (captured F alpha) 11 (leftStart F alpha) := by
  rw [leftStart, ← lineWords_source]
  exact prepareLeft_words n (directionSpace F [alpha]).parameters
    (mapBits (directionSpace F [alpha]).forms) (SourceLineQueryMatrices.normalBytes F alpha)
    (SourceLineQueryMatrices.activityBytes F alpha) (matrixBits [alpha]).reverse
    (List.replicate F.length true) (derivedData F alpha)

def left : Block 38 := Frame.block 21 SourceLineSolver.block
def leftDone {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  lineStore (SourceLineSolver.result F alpha) (derivedData F alpha)
theorem left_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec left (leftStart F alpha) (SourceLineSolver.fuel F alpha) (leftDone F alpha) :=
  Frame.execution (SourceLineSolver.block_exec F alpha) (lineFrame (derivedData F alpha))

def captureLeft : Block 38 := .seq (.action (.copy 32 0)) <|
  .seq (.action (.copy 33 1)) (.action (.pop 33))
private theorem captureLeft_words (r : SourcePlaneMatrixAugmentation.State) (data : Saved) :
    Exec captureLeft (lineStore r data) 3
      (lineStore r {data with
        leftMap := (SourcePlaneSolver.solver r).core.input,
        leftWidth := (SourcePlaneSolver.solver r).core.target.tail}) := by
  let a := {data with leftMap := (SourcePlaneSolver.solver r).core.input}
  let b := {a with leftWidth := (SourcePlaneSolver.solver r).core.target}
  let c := {b with leftWidth := b.leftWidth.tail}
  have first : Exec (.action (.copy (32 : Fin 38) 0)) (lineStore r data) 1 (lineStore r a) :=
    copy_to_saved r.store (lineFrame data) 15 0
  have second : Exec (.action (.copy (33 : Fin 38) 1)) (lineStore r a) 1 (lineStore r b) :=
    copy_to_saved r.store (lineFrame a) 16 1
  have third : Exec (.action (.pop (33 : Fin 38))) (lineStore r b) 1 (lineStore r c) :=
    pop_saved r.store (lineFrame b) 16
  exact Exec.seq first (Exec.seq second third)
def leftCaptured {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  lineStore (SourceLineSolver.result F alpha) (leftData F alpha)
theorem captureLeft_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec captureLeft (leftDone F alpha) 3 (leftCaptured F alpha) := by
  have checked := captureLeft_words (SourceLineSolver.result F alpha) (derivedData F alpha)
  rw [SourceLineSolver.result_solver] at checked
  exact checked

def zeroSolver : MatrixReconstruction.State := ⟨base 0 [], [], [], []⟩
private def clearFirst : Block 9 := .seq (.action (.clear 0)) <|
  .seq (.action (.clear 1)) (.action (.clear 2))
private def firstCleared (r : Registers) : Registers :=
  {r with input := [], target := [], remaining := []}
private theorem clearFirst_exec (r : Registers) :
    Exec clearFirst r.store 3 (firstCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
private def clearSecond : Block 9 := .seq (.action (.clear 3)) <|
  .seq (.action (.clear 4)) (.action (.clear 5))
private def secondCleared (r : Registers) : Registers :=
  {r with excess := [], sign := [], mode := []}
private theorem clearSecond_exec (r : Registers) :
    Exec clearSecond r.store 3 (secondCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
private def clearThird : Block 9 := .seq (.action (.clear 6)) <|
  .seq (.action (.clear 7)) (.action (.clear 8))
private def thirdCleared (r : Registers) : Registers :=
  {r with active := [], reserved := [], output := []}
private theorem clearThird_exec (r : Registers) :
    Exec clearThird r.store 3 (thirdCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
private def clearRegisters : Block 9 := .seq clearFirst (.seq clearSecond clearThird)
private theorem clearRegisters_exec (r : Registers) :
    Exec clearRegisters r.store 9 (base 0 []).store :=
  Exec.seq (clearFirst_exec r)
    (Exec.seq (clearSecond_exec (firstCleared r)) (clearThird_exec (secondCleared (firstCleared r))))
private def clearSolverMeta : Block 12 := .seq (.action (.clear 9)) <|
  .seq (.action (.clear 10)) (.action (.clear 11))
private theorem clearSolverMeta_exec (r : MatrixReconstruction.State) :
    Exec clearSolverMeta r.store 3 (MatrixReconstruction.State.mk r.core [] [] []).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def clearSolver : Block 12 := .seq (MatrixReconstruction.lift clearRegisters) clearSolverMeta
theorem clearSolver_exec (r : MatrixReconstruction.State) :
    Exec clearSolver r.store 12 zeroSolver.store :=
  Exec.seq (MatrixReconstruction.lift_exec clearRegisters r 9 (base 0 []) (clearRegisters_exec r.core))
    (clearSolverMeta_exec {r with core := base 0 []})
def clearLeftSolver : Block 38 := Frame.block 21 (SourcePlaneSolver.lift12 clearSolver)
theorem clearLeftSolver_exec (r : SourcePlaneMatrixAugmentation.State) (data : Saved) :
    Exec clearLeftSolver (lineStore r data) 12
      (lineStore (SourcePlaneSolver.setSolver r zeroSolver) data) :=
  Frame.execution
    (SourcePlaneSolver.lift12_exec clearSolver r 12 zeroSolver
      (clearSolver_exec (SourcePlaneSolver.solver r))) (lineFrame data)

def clearLeftMeta : Block 38 := .seq (.action (.clear 12)) <|
  .seq (.action (.clear 13)) <| .seq (.action (.clear 14)) <|
  .seq (.action (.clear 15)) (.action (.clear 16))
def leftMetaCleared (r : SourcePlaneMatrixAugmentation.State) : SourcePlaneMatrixAugmentation.State :=
  {r with
    core := {r.core with core := {r.core.core with source := [], outer := [], inner := []}, rows := []},
    normals := []}
private theorem clearLeftMeta_exec (r : SourcePlaneMatrixAugmentation.State) (data : Saved) :
    Exec clearLeftMeta (lineStore r data) 5 (lineStore (leftMetaCleared r) data) := by
  let a := {r with core := {r.core with core := {r.core.core with source := []}}}
  let b := {a with core := {a.core with core := {a.core.core with outer := []}}}
  let c := {b with core := {b.core with core := {b.core.core with inner := []}}}
  let d := {c with core := {c.core with rows := []}}
  have first : Exec (.action (.clear (12 : Fin 38))) (lineStore r data) 1 (lineStore a data) :=
    clear_core r.store (lineFrame data) 12
  have second : Exec (.action (.clear (13 : Fin 38))) (lineStore a data) 1 (lineStore b data) :=
    clear_core a.store (lineFrame data) 13
  have third : Exec (.action (.clear (14 : Fin 38))) (lineStore b data) 1 (lineStore c data) :=
    clear_core b.store (lineFrame data) 14
  have fourth : Exec (.action (.clear (15 : Fin 38))) (lineStore c data) 1 (lineStore d data) :=
    clear_core c.store (lineFrame data) 15
  have fifth : Exec (.action (.clear (16 : Fin 38))) (lineStore d data) 1
      (lineStore (leftMetaCleared r) data) := clear_core d.store (lineFrame data) 16
  exact Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth fifth)))
def copyRightWidth : Block 38 := .seq (.action (.copy 1 29)) (.action (.copy 9 29))
private theorem copyRightWidth_exec (data : Saved) :
    Exec copyRightWidth (solverStore zeroSolver data) 2
      (solverStore ⟨{base 0 [] with target := data.directionWidth}, data.directionWidth, [], []⟩ data) := by
  let a : MatrixReconstruction.State := ⟨{base 0 [] with target := data.directionWidth}, [], [], []⟩
  have first : Exec (.action (.copy (1 : Fin 38) 29)) (solverStore zeroSolver data) 1
      (solverStore a data) := copy_from_saved zeroSolver.store (solverFrame data) 1 17
  have second : Exec (.action (.copy (9 : Fin 38) 29)) (solverStore a data) 1
      (solverStore ⟨a.core, data.directionWidth, [], []⟩ data) :=
    copy_from_saved a.store (solverFrame data) 9 17
  exact Exec.seq first second
def prepareRight : Block 38 := .seq clearLeftSolver (.seq clearLeftMeta copyRightWidth)
def rightStart {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  solverStore (MatrixSolutionInstructions.start (directionSpace F [alpha]).parameters [])
    (leftData F alpha)
private theorem prepareRight_words (r : SourcePlaneMatrixAugmentation.State) (data : Saved) :
    Exec prepareRight (lineStore r data) 19
      (solverStore ⟨{base 0 [] with target := data.directionWidth}, data.directionWidth, [], []⟩ data) := by
  exact Exec.seq (clearLeftSolver_exec r data)
    (Exec.seq (clearLeftMeta_exec (SourcePlaneSolver.setSolver r zeroSolver) data)
      (copyRightWidth_exec data))
theorem prepareRight_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepareRight (leftCaptured F alpha) 19 (rightStart F alpha) :=
  prepareRight_words (SourceLineSolver.result F alpha) (leftData F alpha)

theorem empty_solver_result (n : Nat) :
    MatrixSolutionInstructions.result n ([] : System n) =
      MatrixSolutionSerialization.result (kernelSpace ([] : System n)) :=
  MatrixKernelSolver.result_eq n []
def right : Block 38 := Frame.block 26 MatrixSolutionInstructions.phase
def rightDone {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  solverStore (MatrixSolutionSerialization.result (rightSpace F alpha)) (leftData F alpha)
def rightFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  MatrixSolutionInstructions.phaseFuel (directionSpace F [alpha]).parameters []
theorem right_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec right (rightStart F alpha) (rightFuel F alpha) (rightDone F alpha) := by
  have checked := Frame.execution
    (MatrixSolutionInstructions.phase_exec (directionSpace F [alpha]).parameters [])
    (solverFrame (leftData F alpha))
  rw [empty_solver_result] at checked
  exact checked

def captureRight : Block 38 := .seq (.action (.copy 34 0)) <|
  .seq (.action (.copy 35 1)) (.action (.pop 35))
private theorem captureRight_words (r : MatrixReconstruction.State) (data : Saved) :
    Exec captureRight (solverStore r data) 3
      (solverStore r {data with rightMap := r.core.input, rightWidth := r.core.target.tail}) := by
  let a := {data with rightMap := r.core.input}
  let b := {a with rightWidth := r.core.target}
  let c := {b with rightWidth := b.rightWidth.tail}
  have first : Exec (.action (.copy (34 : Fin 38) 0)) (solverStore r data) 1 (solverStore r a) :=
    copy_to_saved r.store (solverFrame data) 22 0
  have second : Exec (.action (.copy (35 : Fin 38) 1)) (solverStore r a) 1 (solverStore r b) :=
    copy_to_saved r.store (solverFrame a) 23 1
  have third : Exec (.action (.pop (35 : Fin 38))) (solverStore r b) 1 (solverStore r c) :=
    pop_saved r.store (solverFrame b) 23
  exact Exec.seq first (Exec.seq second third)
def kernelsDone {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  solverStore (MatrixSolutionSerialization.result (rightSpace F alpha)) (kernelData F alpha)
theorem captureRight_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec captureRight (rightDone F alpha) 3 (kernelsDone F alpha) :=
  captureRight_words (MatrixSolutionSerialization.result (rightSpace F alpha)) (leftData F alpha)

def kernels : Block 38 := .seq save <| .seq matrices <| .seq capture <|
  .seq prepareLeft <| .seq left <| .seq captureLeft <| .seq prepareRight <|
  .seq right captureRight
def kernelsFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  5 + (SourceLineQueryMatrices.fuel F alpha + (5 + (11 + (SourceLineSolver.fuel F alpha +
    (3 + (19 + (rightFuel F alpha + 3)))))))
theorem kernels_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec kernels (start F alpha) (kernelsFuel F alpha) (kernelsDone F alpha) :=
  Exec.seq (save_exec F alpha) <| Exec.seq (matrices_exec F alpha) <| Exec.seq (capture_exec F alpha) <|
    Exec.seq (prepareLeft_exec F alpha) <| Exec.seq (left_exec F alpha) <| Exec.seq (captureLeft_exec F alpha) <|
    Exec.seq (prepareRight_exec F alpha) <| Exec.seq (right_exec F alpha) (captureRight_exec F alpha)

end PNP.Concrete.ResidualReduction.SourceLinePullback
