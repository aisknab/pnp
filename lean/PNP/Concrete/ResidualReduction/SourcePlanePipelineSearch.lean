import PNP.Concrete.ResidualReduction.SourcePlanePipelineHandoff

/-! The plane search consumes the solution map computed by the source plane
solver and the activity matrix computed before it. The register handoff is
literal code. It preserves the protected direction map for later lifting. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePipeline
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceAffineOutput (core setCore setRegisters)

def searchView (r : SourcePlaneMatrixAugmentation.State) : SourceAffineSearch.State :=
  ⟨⟨⟨⟨r.core.core.core, r.core.core.source⟩, r.core.core.outer, r.core.core.inner, r.core.rows⟩,
      r.normals, [], [], [], []⟩, []⟩
theorem searchView_store (r : SourcePlaneMatrixAugmentation.State) (data : Saved) :
    searchStore (searchView r).store data = planeStore r data := rfl

def searchMapState (r : SourceAffineSearch.State) : SourceAffineSearch.State :=
  {r with core := {r.core with sourceMap := (core r).core.input, parameters := (core r).core.target.tail}}
def searchCopiedMap (r : SourceAffineSearch.State) : SourceAffineSearch.State :=
  {r with core := {r.core with sourceMap := (core r).core.input, parameters := (core r).core.target}}
def searchTrimmedMap (r : SourceAffineSearch.State) : SourceAffineSearch.State :=
  {r with core := {r.core with parameters := r.core.parameters.tail}}
def copySearchMap : Block 29 := .seq (.action (.copy 16 0)) (.action (.copy 17 1))
def transferSearchMap : Block 29 := .seq copySearchMap (.action (.pop 17))
private theorem copySearchMap_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec copySearchMap (searchStore r.store data) 2 (searchStore (searchCopiedMap r).store data) := by
  let first := {r with core := {r.core with sourceMap := (core r).core.input}}
  have a : Exec (.action (.copy (16 : Fin 29) 0)) (searchStore r.store data) 1
      (searchStore first.store data) := .action _ _
  have b : Exec (.action (.copy (17 : Fin 29) 1)) (searchStore first.store data) 1
      (searchStore (searchCopiedMap r).store data) := .action _ _
  exact Exec.seq a b
private theorem search_parameters_get (r : SourceAffineSearch.State) (data : Saved) :
    (searchStore r.store data).get 17 = r.core.parameters := rfl
private theorem search_parameters_set (r : SourceAffineSearch.State) (data : Saved) (word : BitString) :
    (searchStore r.store data).set 17 word =
      searchStore ({r with core := {r.core with parameters := word}}).store data := rfl
private theorem trimSearchMap_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec (.action (.pop (17 : Fin 29))) (searchStore r.store data) 1
      (searchStore (searchTrimmedMap r).store data) := by
  have checked := Exec.action (.pop (17 : Fin 29)) (searchStore r.store data)
  simpa only [Action.update, Action.instruction, Instruction.update,
    search_parameters_get, search_parameters_set, searchTrimmedMap] using checked
theorem transferSearchMap_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec transferSearchMap (searchStore r.store data) 3 (searchStore (searchMapState r).store data) :=
  Exec.seq (copySearchMap_exec r data) (trimSearchMap_exec (searchCopiedMap r) data)

def searchMatrixState (r : SourceAffineSearch.State) (data : Saved) : SourceAffineSearch.State :=
  setRegisters r {(core r).core with input := data.matrix, target := data.directionWidth, sign := data.rows}
def transferSearchMatrix : Block 29 := .seq (.action (.copy 0 24)) <|
  .seq (.action (.copy 1 26)) (.action (.copy 4 27))
theorem transferSearchMatrix_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec transferSearchMatrix (searchStore r.store data) 3
      (searchStore (searchMatrixState r data).store data) := by
  let first := setRegisters r {(core r).core with input := data.matrix}
  let second := setRegisters first {(core first).core with target := data.directionWidth}
  have a : Exec (.action (.copy (0 : Fin 29) 24)) (searchStore r.store data) 1
      (searchStore first.store data) := .action _ _
  have b : Exec (.action (.copy (1 : Fin 29) 26)) (searchStore first.store data) 1
      (searchStore second.store data) := .action _ _
  have c : Exec (.action (.copy (4 : Fin 29) 27)) (searchStore second.store data) 1
      (searchStore (searchMatrixState r data).store data) := .action _ _
  exact Exec.seq a (Exec.seq b c)

def searchCleanState (r : SourceAffineSearch.State) : SourceAffineSearch.State :=
  let cleaned := setRegisters r {(core r).core with reserved := [], output := []}
  {cleaned with core := {cleaned.core with core := {cleaned.core.core with core :=
    {cleaned.core.core.core with weights := []}}}}
def cleanSearch : Block 29 := .seq (.action (.clear 7)) <|
  .seq (.action (.clear 8)) (.action (.clear 12))
theorem cleanSearch_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec cleanSearch (searchStore r.store data) 3 (searchStore (searchCleanState r).store data) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def searchWidthState (r : SourceAffineSearch.State) (data : Saved) : SourceAffineSearch.State :=
  setCore r {core r with width := data.directionWidth, pending := data.directionWidth}
def transferSearchWidth : Block 29 := .seq (.action (.copy 9 26)) (.action (.copy 11 26))
theorem transferSearchWidth_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec transferSearchWidth (searchStore r.store data) 2
      (searchStore (searchWidthState r data).store data) := by
  let first := setCore r {core r with width := data.directionWidth}
  have a : Exec (.action (.copy (9 : Fin 29) 26)) (searchStore r.store data) 1
      (searchStore first.store data) := .action _ _
  have b : Exec (.action (.copy (11 : Fin 29) 26)) (searchStore first.store data) 1
      (searchStore (searchWidthState r data).store data) := .action _ _
  exact Exec.seq a b

def searchFrameState (r : SourceAffineSearch.State) (data : Saved) : SourceAffineSearch.State :=
  {r with core := {r.core with core := {r.core.core with source := [], dimension := data.directionWidth, direction := []}}}
def transferSearchFrame : Block 29 := .seq (.action (.clear 13)) <|
  .seq (.action (.copy 14 26)) (.action (.clear 15))
theorem transferSearchFrame_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec transferSearchFrame (searchStore r.store data) 3
      (searchStore (searchFrameState r data).store data) := by
  let first := {r with core := {r.core with core := {r.core.core with source := []}}}
  let second := {first with core := {first.core with core := {first.core.core with dimension := data.directionWidth}}}
  have a : Exec (.action (.clear (13 : Fin 29))) (searchStore r.store data) 1
      (searchStore first.store data) := .action _ _
  have b : Exec (.action (.copy (14 : Fin 29) 26)) (searchStore first.store data) 1
      (searchStore second.store data) := .action _ _
  have c : Exec (.action (.clear (15 : Fin 29))) (searchStore second.store data) 1
      (searchStore (searchFrameState r data).store data) := .action _ _
  exact Exec.seq a (Exec.seq b c)

def searchCountState (r : SourceAffineSearch.State) (data : Saved) : SourceAffineSearch.State :=
  {r with core := {r.core with remaining := data.directionWidth}}
def transferSearchCount : Block 29 := .action (.copy 20 26)
theorem transferSearchCount_exec (r : SourceAffineSearch.State) (data : Saved) :
    Exec transferSearchCount (searchStore r.store data) 1
      (searchStore (searchCountState r data).store data) := .action _ _

def prepareSearch : Block 29 := .seq transferSearchMap <| .seq transferSearchMatrix <|
  .seq cleanSearch <| .seq transferSearchWidth <| .seq transferSearchFrame transferSearchCount
def preparedSearch (r : SourceAffineSearch.State) (data : Saved) : SourceAffineSearch.State :=
  searchCountState (searchFrameState (searchWidthState
    (searchCleanState (searchMatrixState (searchMapState r) data)) data) data) data
theorem prepareSearch_words (r : SourceAffineSearch.State) (data : Saved) :
    Exec prepareSearch (searchStore r.store data) 15 (searchStore (preparedSearch r data).store data) :=
  Exec.seq (transferSearchMap_exec r data) <|
    Exec.seq (transferSearchMatrix_exec (searchMapState r) data) <|
      Exec.seq (cleanSearch_exec (searchMatrixState (searchMapState r) data) data) <|
        Exec.seq (transferSearchWidth_exec (searchCleanState (searchMatrixState (searchMapState r) data)) data) <|
          Exec.seq (transferSearchFrame_exec (searchWidthState
            (searchCleanState (searchMatrixState (searchMapState r) data)) data) data)
            (transferSearchCount_exec (searchFrameState (searchWidthState
              (searchCleanState (searchMatrixState (searchMapState r) data)) data) data) data)

def searchWords (matrix map dimension rows parameters : BitString) : SourceAffineSearch.State :=
  ⟨⟨⟨⟨⟨{base 0 [] with input := matrix, target := dimension, sign := rows}, dimension, [], dimension⟩,
      []⟩, [], dimension, []⟩, map, parameters, [], [], dimension⟩, []⟩
theorem bilinear_start_words {m n : Nat} (M : Matrix m n) (s : Space m) :
    SourceBilinearSearch.start M s = searchWords (SourceActivityMapAlgebra.coefficientMatrixBits M)
      (mapBits s.forms) (List.replicate n true) (List.replicate m true) (List.replicate s.parameters true) := by
  change searchWords (SourceActivityMapAlgebra.coefficientMatrixBits M)
    (mapBits (SourceBilinearFamily.forms M s.forms)) (List.replicate n true)
      (List.replicate m true) (List.replicate s.parameters true) = _
  rw [SourceBilinearFamily.forms_bits]

def planeSolution {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length) :
    SourcePlaneMatrixAugmentation.State :=
  SourcePlaneSolver.setSolver (SourcePlaneSolver.saved F a b) (MatrixSolutionSerialization.result s)
theorem planeSolution_store {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (SourcePlane.planeRows F a b) = some s) :
    planeDone F a b = searchStore (searchView (planeSolution F a b s)).store (derivedData F a b) := by
  unfold planeDone SourcePlaneSolver.result
  rw [SourceAffineInput.result_some F.length (SourcePlane.planeRows F a b) s computed]
  rfl
theorem preparedSearch_eq {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length) :
    preparedSearch (searchView (planeSolution F a b s)) (derivedData F a b) =
      SourcePlanePreparedSearch.start F a b s := by
  rw [SourcePlanePreparedSearch.start, bilinear_start_words]
  change searchWords (SourceActivityMapAlgebra.sourceBits F (directionSpace F [a, b]))
    (mapBits s.forms) (List.replicate (directionSpace F [a, b]).parameters true)
      (List.replicate F.length true) (List.replicate s.parameters true) = _
  rw [SourceActivityMapAlgebra.sourceBits_matrix]
theorem prepareSearch_exec {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (SourcePlane.planeRows F a b) = some s) :
    Exec prepareSearch (planeDone F a b) 15
      (searchStore (SourcePlanePreparedSearch.start F a b s).store (derivedData F a b)) := by
  rw [planeSolution_store F a b s computed, ← preparedSearch_eq F a b s]
  exact prepareSearch_words (searchView (planeSolution F a b s)) (derivedData F a b)

end PNP.Concrete.ResidualReduction.SourcePlanePipeline
