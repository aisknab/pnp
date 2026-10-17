import PNP.Concrete.ResidualReduction.SourceBilinearPullbackInstructions
import PNP.Concrete.ResidualReduction.SourceLineSolver

/-! Protected inputs and computed data for the exact line-query pullbacks.
The initial state supplies only the original family and normal. Both matrices,
both solution maps and every transformed coefficient are computed by the
program; the fixed frame is outside each reused working prefix. -/

namespace PNP.Concrete.ResidualReduction.SourceLinePullback
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra (coefficientMatrixBits)

/-- Registers 24 through 37, outside all reused working prefixes. -/
structure Saved where
  source : BitString := []
  normal : BitString := []
  dimension : BitString := []
  rows : BitString := []
  directionMap : BitString := []
  directionWidth : BitString := []
  normalMatrix : BitString := []
  activityMatrix : BitString := []
  leftMap : BitString := []
  leftWidth : BitString := []
  rightMap : BitString := []
  rightWidth : BitString := []
  pulledNormal : BitString := []
  pulledActivity : BitString := []
def Saved.store (r : Saved) : Store 14 :=
  .cons r.source <| .cons r.normal <| .cons r.dimension <| .cons r.rows <|
  .cons r.directionMap <| .cons r.directionWidth <| .cons r.normalMatrix <|
  .cons r.activityMatrix <| .cons r.leftMap <| .cons r.leftWidth <|
  .cons r.rightMap <| .cons r.rightWidth <| .cons r.pulledNormal (.cons r.pulledActivity .nil)
def emptyFrame : (n : Nat) → Store n
  | 0 => .nil
  | n + 1 => .cons [] (emptyFrame n)
def matricesStore (r : SourceLineQueryMatrices.State) (data : Saved) : Store 38 :=
  Frame.join r.store data.store
def lineFrame (data : Saved) : Store 21 := Frame.join (emptyFrame 7) data.store
def lineStore (r : SourcePlaneMatrixAugmentation.State) (data : Saved) : Store 38 :=
  Frame.join r.store (lineFrame data)
def solverFrame (data : Saved) : Store 26 := Frame.join (emptyFrame 12) data.store
def solverStore (r : MatrixReconstruction.State) (data : Saved) : Store 38 :=
  Frame.join r.store (solverFrame data)
def pullFrame (data : Saved) : Store 17 := Frame.join (emptyFrame 3) data.store
def pullStore (r : SourceBilinearPullback.State) (data : Saved) : Store 38 :=
  Frame.join r.store (pullFrame data)

private theorem set_frame {extra count : Nat} (core : Store count) (frame : Store extra)
    (i : Fin extra) (word : BitString) :
    (Frame.join core frame).set (Frame.frameIndex count i) word =
      Frame.join core (frame.set i word) := by
  induction core with
  | nil =>
    have position : Frame.frameIndex 0 i = i := by
      apply Fin.ext
      exact Nat.zero_add i.val
    rw [position]
    rfl
  | @cons count first rest ih =>
    have position : Frame.frameIndex (count + 1) i = (Frame.frameIndex count i).succ := by
      apply Fin.ext
      change count + 1 + i.val = count + i.val + 1
      omega
    rw [position]
    exact congrArg (Store.cons first) ih

theorem copy_to_saved {count extra : Nat} (core : Store count) (frame : Store extra)
    (destination : Fin extra) (source : Fin count) :
    Exec (.action (.copy (Frame.frameIndex count destination) (Frame.index extra source)))
      (Frame.join core frame) 1 (Frame.join core (frame.set destination (core.get source))) := by
  have checked := Exec.action (.copy (Frame.frameIndex count destination) (Frame.index extra source))
    (Frame.join core frame)
  simpa only [Action.update, Action.instruction, Instruction.update, Frame.get_core, set_frame] using checked

theorem copy_from_saved {count extra : Nat} (core : Store count) (frame : Store extra)
    (destination : Fin count) (source : Fin extra) :
    Exec (.action (.copy (Frame.index extra destination) (Frame.frameIndex count source)))
      (Frame.join core frame) 1 (Frame.join (core.set destination (frame.get source)) frame) := by
  have checked := Exec.action (.copy (Frame.index extra destination) (Frame.frameIndex count source))
    (Frame.join core frame)
  simpa only [Action.update, Action.instruction, Instruction.update, Frame.get_frame, Frame.set_core] using checked
theorem clear_core {count extra : Nat} (core : Store count) (frame : Store extra) (destination : Fin count) :
    Exec (.action (.clear (Frame.index extra destination))) (Frame.join core frame) 1
      (Frame.join (core.set destination []) frame) :=
  Frame.execution (Exec.action (.clear destination) core) frame
theorem pop_saved {count extra : Nat} (core : Store count) (frame : Store extra) (destination : Fin extra) :
    Exec (.action (.pop (Frame.frameIndex count destination))) (Frame.join core frame) 1
      (Frame.join core (frame.set destination (frame.get destination).tail)) := by
  have checked := Exec.action (.pop (Frame.frameIndex count destination)) (Frame.join core frame)
  simpa only [Action.update, Action.instruction, Instruction.update, Frame.get_frame, set_frame] using checked

def transfers {count : Nat} : List (Action count) → Block count
  | [] => .skip
  | a :: rest => .seq (.action a) (transfers rest)
def transferStore {count : Nat} : List (Action count) → Store count → Store count
  | [], r => r
  | a :: rest, r => transferStore rest (a.update r)
theorem transfers_exec {count : Nat} (actions : List (Action count)) (r : Store count) :
    Exec (transfers actions) r (actions.length + 1) (transferStore actions r) := by
  induction actions generalizing r with
  | nil => exact .skip r
  | cons a rest ih =>
    have checked := Exec.seq (Exec.action a r) (ih (a.update r))
    simpa only [transfers, transferStore, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using checked

def initialData : Saved := {}
def sourceData {n : Nat} (F : Family n) (alpha : Affine n) : Saved :=
  {source := familyBits F, normal := matrixBits [alpha],
   dimension := List.replicate n true, rows := List.replicate F.length true}
def derivedData {n : Nat} (F : Family n) (alpha : Affine n) : Saved :=
  {sourceData F alpha with
    directionMap := mapBits (directionSpace F [alpha]).forms,
    directionWidth := List.replicate (directionSpace F [alpha]).parameters true,
    normalMatrix := SourceLineQueryMatrices.normalBytes F alpha,
    activityMatrix := SourceLineQueryMatrices.activityBytes F alpha}
def start {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  matricesStore (SourceLineQueryMatrices.start F alpha) initialData
def saved {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  matricesStore (SourceLineQueryMatrices.start F alpha) (sourceData F alpha)
def matricesDone {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  matricesStore (SourceLineQueryMatrices.result F alpha) (sourceData F alpha)
def captured {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  matricesStore (SourceLineQueryMatrices.result F alpha) (derivedData F alpha)

def saveActions : List (Action 38) := [.copy 24 17, .copy 25 0, .copy 26 18, .copy 27 21]
def save : Block 38 := transfers saveActions
private theorem save_words (r : SourceLineQueryMatrices.State) (data : Saved) :
    Exec save (matricesStore r data) 5
      (matricesStore r {data with
        source := r.core.core.family.source,
        normal := (SourceLineQueryMatrices.registers r).input,
        dimension := r.core.core.dimension, rows := r.rows}) := by
  let a := {data with source := r.core.core.family.source}
  let b := {a with normal := (SourceLineQueryMatrices.registers r).input}
  let c := {b with dimension := r.core.core.dimension}
  let d := {c with rows := r.rows}
  have first : Exec (.action (.copy (24 : Fin 38) 17))
      (matricesStore r data) 1 (matricesStore r a) :=
    copy_to_saved r.store data.store 0 17
  have second : Exec (.action (.copy (25 : Fin 38) 0))
      (matricesStore r a) 1 (matricesStore r b) :=
    copy_to_saved r.store a.store 1 0
  have third : Exec (.action (.copy (26 : Fin 38) 18))
      (matricesStore r b) 1 (matricesStore r c) :=
    copy_to_saved r.store b.store 2 18
  have fourth : Exec (.action (.copy (27 : Fin 38) 21))
      (matricesStore r c) 1 (matricesStore r d) :=
    copy_to_saved r.store c.store 3 21
  exact Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth (.skip _))))
theorem save_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec save (start F alpha) 5 (saved F alpha) :=
  save_words (SourceLineQueryMatrices.start F alpha) initialData

def matrices : Block 38 := Frame.block 14 SourceLineQueryMatrices.block
theorem matrices_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec matrices (saved F alpha) (SourceLineQueryMatrices.fuel F alpha) (matricesDone F alpha) :=
  Frame.execution (SourceLineQueryMatrices.block_exec F alpha) (sourceData F alpha).store

def captureActions : List (Action 38) := [.copy 28 15, .copy 29 1, .copy 30 22, .copy 31 23]
def capture : Block 38 := transfers captureActions
private theorem capture_words (r : SourceLineQueryMatrices.State) (data : Saved) :
    Exec capture (matricesStore r data) 5
      (matricesStore r {data with
        directionMap := r.core.core.family.core.map,
        directionWidth := (SourceLineQueryMatrices.registers r).target,
        normalMatrix := r.normal, activityMatrix := r.activity}) := by
  let a := {data with directionMap := r.core.core.family.core.map}
  let b := {a with directionWidth := (SourceLineQueryMatrices.registers r).target}
  let c := {b with normalMatrix := r.normal}
  let d := {c with activityMatrix := r.activity}
  have first : Exec (.action (.copy (28 : Fin 38) 15))
      (matricesStore r data) 1 (matricesStore r a) :=
    copy_to_saved r.store data.store 4 15
  have second : Exec (.action (.copy (29 : Fin 38) 1))
      (matricesStore r a) 1 (matricesStore r b) :=
    copy_to_saved r.store a.store 5 1
  have third : Exec (.action (.copy (30 : Fin 38) 22))
      (matricesStore r b) 1 (matricesStore r c) :=
    copy_to_saved r.store b.store 6 22
  have fourth : Exec (.action (.copy (31 : Fin 38) 23))
      (matricesStore r c) 1 (matricesStore r d) :=
    copy_to_saved r.store c.store 7 23
  exact Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth (.skip _))))
theorem capture_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec capture (matricesDone F alpha) 5 (captured F alpha) :=
  capture_words (SourceLineQueryMatrices.result F alpha) (sourceData F alpha)

theorem matrices_saved_get (r : SourceLineQueryMatrices.State) (data : Saved) (i : Fin 14) :
    (matricesStore r data).get (Frame.frameIndex 24 i) = data.store.get i :=
  Frame.get_frame r.store data.store i
theorem initial_no_derived_data {n : Nat} (F : Family n) (alpha : Affine n) :
    (start F alpha).get 28 = [] ∧ (start F alpha).get 30 = [] ∧
    (start F alpha).get 31 = [] ∧ (start F alpha).get 32 = [] ∧
    (start F alpha).get 34 = [] ∧ (start F alpha).get 36 = [] ∧
    (start F alpha).get 37 = [] :=
  ⟨matrices_saved_get _ initialData 4, matrices_saved_get _ initialData 6,
   matrices_saved_get _ initialData 7, matrices_saved_get _ initialData 8,
   matrices_saved_get _ initialData 10, matrices_saved_get _ initialData 12,
   matrices_saved_get _ initialData 13⟩
theorem captured_normal {n : Nat} (F : Family n) (alpha : Affine n) :
    (captured F alpha).get 30 = coefficientMatrixBits (SourceLine.normalQueryMatrix F alpha) :=
  (matrices_saved_get _ (derivedData F alpha) 6).trans
    (SourceLineQueryMatrixAlgebra.normal_query_bytes F alpha).symm
theorem captured_activity {n : Nat} (F : Family n) (alpha : Affine n) :
    (captured F alpha).get 31 = coefficientMatrixBits (SourceLine.activityQueryMatrix F alpha) :=
  (matrices_saved_get _ (derivedData F alpha) 7).trans
    (SourceLineQueryMatrixAlgebra.activity_query_bytes F alpha).symm

end PNP.Concrete.ResidualReduction.SourceLinePullback
