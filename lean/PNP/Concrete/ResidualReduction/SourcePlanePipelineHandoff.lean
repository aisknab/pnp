import PNP.Concrete.ResidualReduction.SourcePlanePipelineState

/-! Transfer retained source bytes into the plane constructor after the
activity matrix has been computed. No plane matrix or solution is supplied
by the caller. The overwritten registers are charged as literal actions. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePipeline
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra (sourceBits)

def planeWords (data : Saved) : SourcePlaneMatrixAugmentation.State :=
  ⟨⟨⟨⟨{base 0 [] with input := data.source}, data.dimension, [], []⟩, [], [], []⟩,
      data.rows⟩, data.normals⟩
def loadPlaneData : Block 29 := .seq (.action (.copy 0 22)) <|
  .seq (.action (.clear 1)) (.action (.clear 8))
def loadPlaneMeta : Block 29 := .seq (.action (.copy 9 28)) <|
  .seq (.action (.copy 15 27)) (.action (.copy 16 23))
def clearPlaneTail : Block 29 := .seq (.action (.clear 18)) (.action (.clear 19))
def preparePlane : Block 29 := .seq loadPlaneData (.seq loadPlaneMeta clearPlaneTail)

def planeDataState (r : SourceActivityConstruction.State) (data : Saved) : SourceActivityConstruction.State :=
  {r with core := {r.core with family := {r.core.family with core :=
    {r.core.family.core with core := {r.core.family.core.core with input := data.source, target := [], output := []}}}}}
def planeMetaState (r : SourceActivityConstruction.State) (data : Saved) : SourceActivityConstruction.State :=
  {r with core := {r.core with family := {r.core.family with core :=
    {r.core.family.core with width := data.dimension, map := data.rows, savedOutput := data.normals}}}}
def planeTailState (r : SourceActivityConstruction.State) : SourceActivityConstruction.State :=
  {r with core := {r.core with dimension := [], normals := []}}
private theorem loadPlaneData_exec (r : SourceActivityConstruction.State) (data : Saved) :
    Exec loadPlaneData (activityStore r data) 3 (activityStore (planeDataState r data) data) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
private theorem loadPlaneMeta_exec (r : SourceActivityConstruction.State) (data : Saved) :
    Exec loadPlaneMeta (activityStore r data) 3 (activityStore (planeMetaState r data) data) := by
  let first : SourceActivityConstruction.State :=
    {r with core := {r.core with family := {r.core.family with core :=
      {r.core.family.core with width := data.dimension}}}}
  let second : SourceActivityConstruction.State :=
    {first with core := {first.core with family := {first.core.family with core :=
      {first.core.family.core with map := data.rows}}}}
  have a : Exec (.action (.copy (9 : Fin 29) 28)) (activityStore r data) 1
      (activityStore first data) := .action _ _
  have b : Exec (.action (.copy (15 : Fin 29) 27)) (activityStore first data) 1
      (activityStore second data) := .action _ _
  have c : Exec (.action (.copy (16 : Fin 29) 23)) (activityStore second data) 1
      (activityStore (planeMetaState r data) data) := .action _ _
  exact Exec.seq a (Exec.seq b c)
private theorem clearPlaneTail_exec (r : SourceActivityConstruction.State) (data : Saved) :
    Exec clearPlaneTail (activityStore r data) 2 (activityStore (planeTailState r) data) :=
  Exec.seq (.action _ _) (.action _ _)
private theorem preparePlane_words (n k : Nat) (map matrix normals : BitString) (data : Saved) :
    let r : SourceActivityConstruction.State :=
      ⟨⟨SourcePolarFamilyInstructions.ready n k map [] matrix, List.replicate n true, normals⟩, []⟩
    Exec preparePlane (activityStore r data) 8 (planeStore (planeWords data) data) := by
  let r : SourceActivityConstruction.State :=
    ⟨⟨SourcePolarFamilyInstructions.ready n k map [] matrix, List.replicate n true, normals⟩, []⟩
  exact Exec.seq (loadPlaneData_exec r data)
    (Exec.seq (loadPlaneMeta_exec (planeDataState r data) data)
      (clearPlaneTail_exec (planeMetaState (planeDataState r data) data) data))

def planeStart {n : Nat} (F : Family n) (a b : Affine n) : Store 29 :=
  planeStore (SourcePlaneMatrixAugmentation.start F a b) (derivedData F a b)
theorem preparePlane_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec preparePlane (captured F a b) 8 (planeStart F a b) :=
  preparePlane_words n (directionSpace F [a, b]).parameters
    (mapBits (directionSpace F [a, b]).forms) (sourceBits F (directionSpace F [a, b]))
    (matrixBits [a, b]).reverse (derivedData F a b)

def plane : Block 29 := Frame.block 12 SourcePlaneSolver.block
def planeDone {n : Nat} (F : Family n) (a b : Affine n) : Store 29 :=
  planeStore (SourcePlaneSolver.result F a b) (derivedData F a b)
theorem plane_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec plane (planeStart F a b) (SourcePlaneSolver.fuel F a b) (planeDone F a b) :=
  Frame.execution (SourcePlaneSolver.block_exec F a b) (planeFrame (derivedData F a b))

def construct : Block 29 := .seq save <| .seq activity <| .seq capture <| .seq preparePlane plane
def constructFuel {n : Nat} (F : Family n) (a b : Affine n) : Nat :=
  4 + (SourceActivityConstruction.fuel F [a, b] + (5 + (8 + SourcePlaneSolver.fuel F a b)))
theorem construct_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec construct (start F a b) (constructFuel F a b) (planeDone F a b) :=
  Exec.seq (save_exec F a b) <| Exec.seq (activity_exec F a b) <|
    Exec.seq (capture_exec F a b) <| Exec.seq (preparePlane_exec F a b) (plane_exec F a b)
theorem plane_output {n : Nat} (F : Family n) (a b : Affine n) :
    (planeDone F a b).get 8 = (solutionCodec F.length).encode
      (solve F.length (SourcePlane.planeRows F a b)) := SourcePlaneSolver.result_output F a b
theorem plane_retains_matrix {n : Nat} (F : Family n) (a b : Affine n) :
    (planeDone F a b).get 24 = SourceActivityMapAlgebra.coefficientMatrixBits
      (activityMatrix (directionSpace F [a, b]) F) :=
  SourceActivityMapAlgebra.sourceBits_matrix F (directionSpace F [a, b])
theorem plane_retains_direction {n : Nat} (F : Family n) (a b : Affine n) :
    (planeDone F a b).get 25 = mapBits (directionSpace F [a, b]).forms := rfl

end PNP.Concrete.ResidualReduction.SourcePlanePipeline
