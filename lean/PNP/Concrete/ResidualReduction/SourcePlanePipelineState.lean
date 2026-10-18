import PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch

/-! Protected original inputs and derived data for the literal plane-query
pipeline. Every retained value is copied from a source register. The initial
frame supplies no activity matrix, solution map or successful candidate. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePipeline
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra (sourceBits)

/-- Registers 22 through 28, outside every reused stage's working prefix. -/
structure Saved where
  source : BitString
  normals : BitString
  matrix : BitString
  directionMap : BitString
  directionWidth : BitString
  rows : BitString
  dimension : BitString
def Saved.store (r : Saved) : Store 7 :=
  .cons r.source <| .cons r.normals <| .cons r.matrix <| .cons r.directionMap <|
    .cons r.directionWidth <| .cons r.rows (.cons r.dimension .nil)
def activityStore (r : SourceActivityConstruction.State) (saved : Saved) : Store 29 :=
  Frame.join r.store (.cons [] saved.store)
def planeFrame (saved : Saved) : Store 12 :=
  .cons [] <| .cons [] <| .cons [] <| .cons [] (.cons [] saved.store)
def planeStore (r : SourcePlaneMatrixAugmentation.State) (saved : Saved) : Store 29 :=
  Frame.join r.store (planeFrame saved)
def searchStore (r : Store 22) (saved : Saved) : Store 29 := Frame.join r saved.store

/-- A fixed list of ordinary copy/reset operations, including its last jump. -/
def transfers : List (Action 29) → Block 29
  | [] => .skip
  | a :: rest => .seq (.action a) (transfers rest)
def transferStore : List (Action 29) → Store 29 → Store 29
  | [], r => r
  | a :: rest, r => transferStore rest (a.update r)
theorem transfers_exec (actions : List (Action 29)) (r : Store 29) :
    Exec (transfers actions) r (actions.length + 1) (transferStore actions r) := by
  induction actions generalizing r with
  | nil => exact .skip r
  | cons a rest ih =>
    have checked := Exec.seq (Exec.action a r) (ih (a.update r))
    simpa only [transfers, transferStore, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using checked

def initialData {n : Nat} (F : Family n) : Saved :=
  ⟨[], [], [], [], [], List.replicate F.length true, []⟩
def sourceData {n : Nat} (F : Family n) (a b : Affine n) : Saved :=
  ⟨familyBits F, matrixBits [a, b], [], [], [], List.replicate F.length true, List.replicate n true⟩
def derivedData {n : Nat} (F : Family n) (a b : Affine n) : Saved :=
  {sourceData F a b with matrix := sourceBits F (directionSpace F [a, b]), directionMap := mapBits (directionSpace F [a, b]).forms, directionWidth := List.replicate (directionSpace F [a, b]).parameters true}

def start {n : Nat} (F : Family n) (a b : Affine n) : Store 29 :=
  activityStore (SourceActivityConstruction.start F [a, b]) (initialData F)
def saved {n : Nat} (F : Family n) (a b : Affine n) : Store 29 :=
  activityStore (SourceActivityConstruction.start F [a, b]) (sourceData F a b)
def activityDone {n : Nat} (F : Family n) (a b : Affine n) : Store 29 :=
  activityStore (SourceActivityConstruction.result F [a, b]) (sourceData F a b)
def captured {n : Nat} (F : Family n) (a b : Affine n) : Store 29 :=
  activityStore (SourceActivityConstruction.result F [a, b]) (derivedData F a b)

def saveActions : List (Action 29) := [.copy 22 17, .copy 23 0, .copy 28 18]
def save : Block 29 := transfers saveActions
theorem save_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec save (start F a b) 4 (saved F a b) := transfers_exec saveActions (start F a b)

def activity : Block 29 := Frame.block 8 SourceActivityConstruction.block
theorem activity_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec activity (saved F a b) (SourceActivityConstruction.fuel F [a, b]) (activityDone F a b) :=
  Frame.execution (SourceActivityConstruction.block_exec F [a, b]) (.cons [] (sourceData F a b).store)

def captureActions : List (Action 29) := [.copy 24 8, .copy 25 15, .copy 26 1, .pop 26]
def capture : Block 29 := transfers captureActions
private theorem capture_words (n k : Nat) (map matrix normals : BitString) (data : Saved) :
    let r : SourceActivityConstruction.State :=
      ⟨⟨SourcePolarFamilyInstructions.ready n k map [] matrix, List.replicate n true, normals⟩, []⟩
    Exec capture (activityStore r data) 5
      (activityStore r {data with matrix := matrix, directionMap := map, directionWidth := List.replicate k true}) := by
  let r : SourceActivityConstruction.State :=
    ⟨⟨SourcePolarFamilyInstructions.ready n k map [] matrix, List.replicate n true, normals⟩, []⟩
  let first := {data with matrix := matrix}
  let second := {first with directionMap := map}
  let third := {second with directionWidth := List.replicate (k + 1) true}
  let fourth := {second with directionWidth := List.replicate k true}
  have a : Exec (.action (.copy (24 : Fin 29) 8)) (activityStore r data) 1
      (activityStore r first) := .action _ _
  have b : Exec (.action (.copy (25 : Fin 29) 15)) (activityStore r first) 1
      (activityStore r second) := .action _ _
  have c : Exec (.action (.copy (26 : Fin 29) 1)) (activityStore r second) 1
      (activityStore r third) := .action _ _
  have d : Exec (.action (.pop (26 : Fin 29))) (activityStore r third) 1
      (activityStore r fourth) := .action _ _
  exact Exec.seq a (Exec.seq b (Exec.seq c (Exec.seq d (.skip _))))

theorem capture_exec {n : Nat} (F : Family n) (a b : Affine n) :
    Exec capture (activityDone F a b) 5 (captured F a b) :=
  capture_words n (directionSpace F [a, b]).parameters
    (mapBits (directionSpace F [a, b]).forms) (sourceBits F (directionSpace F [a, b]))
    (matrixBits [a, b]).reverse (sourceData F a b)

theorem initial_no_matrix {n : Nat} (F : Family n) (a b : Affine n) :
    (start F a b).get 24 = [] := rfl
theorem initial_no_direction_map {n : Nat} (F : Family n) (a b : Affine n) :
    (start F a b).get 25 = [] := rfl
theorem captured_matrix {n : Nat} (F : Family n) (a b : Affine n) :
    (captured F a b).get 24 = SourceActivityMapAlgebra.coefficientMatrixBits
      (activityMatrix (directionSpace F [a, b]) F) :=
  SourceActivityMapAlgebra.sourceBits_matrix F (directionSpace F [a, b])
theorem captured_direction_map {n : Nat} (F : Family n) (a b : Affine n) :
    (captured F a b).get 25 = mapBits (directionSpace F [a, b]).forms := rfl
theorem captured_direction_width {n : Nat} (F : Family n) (a b : Affine n) :
    (captured F a b).get 26 = List.replicate (directionSpace F [a, b]).parameters true := rfl

end PNP.Concrete.ResidualReduction.SourcePlanePipeline
