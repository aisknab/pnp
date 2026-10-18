import PNP.Concrete.ResidualReduction.SourceMatrixWitnessInstructions

/-! Reuse the internally computed line-query matrices and maps. The search
uses a 19-register prefix; all original-source metadata remains protected.
This handoff performs no elimination or matrix construction a second time. -/

namespace PNP.Concrete.ResidualReduction.SourceLineWitness
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra (coefficientMatrixBits)
open PNP.Concrete.ResidualReduction.SourceLinePullback (copy_from_saved)

structure Work where
  core : Registers
  normal : BitString
  activity : BitString
  width : BitString
  firstRow : BitString
  secondRow : BitString
  firstColumn : BitString
  secondColumn : BitString
  rowWidth : BitString
  rowResult : BitString
  scratch : BitString
def Work.words (r : Work) : Store 10 :=
  .cons r.normal <| .cons r.activity <| .cons r.width <| .cons r.firstRow <|
  .cons r.secondRow <| .cons r.firstColumn <| .cons r.secondColumn <|
  .cons r.rowWidth <| .cons r.rowResult (.cons r.scratch .nil)
def Work.store (r : Work) : Store 19 := Frame.join r.core.store r.words
def frame (data : SourceLinePullback.Saved) : Store 19 :=
  Frame.join (SourceLinePullback.emptyFrame 5) data.store
def store (core : Store 19) (data : SourceLinePullback.Saved) : Store 38 := Frame.join core (frame data)
def workStore (r : Work) (data : SourceLinePullback.Saved) : Store 38 := store r.store data

def fromPullback {n : Nat} (F : Family n) (alpha : Affine n) : Work :=
  ⟨{base 0 [] with output := coefficientMatrixBits (SourceLinePullback.activityPull F alpha)},
    [], coefficientMatrixBits (SourceLine.activityQueryMatrix F alpha),
    mapBits (SourceLinePullback.leftSpace F alpha).forms,
    mapBits (SourceLinePullback.rightSpace F alpha).forms,
    List.replicate (SourceLinePullback.leftSpace F alpha).parameters true,
    List.replicate (SourceLinePullback.rightSpace F alpha).parameters true,
    List.replicate (SourceLinePullback.leftSpace F alpha).parameters true, [], [], []⟩
theorem pullback_state {n : Nat} (F : Family n) (alpha : Affine n) :
    SourceLinePullback.result F alpha = workStore (fromPullback F alpha) (SourceLinePullback.resultData F alpha) := rfl

def clearPositions : Block 19 := .seq (.action (.clear 12)) <|
  .seq (.action (.clear 13)) <| .seq (.action (.clear 14)) (.action (.clear 15))
def positionsCleared (r : Work) : Work :=
  {r with firstRow := [], secondRow := [], firstColumn := [], secondColumn := []}
theorem clearPositions_exec (r : Work) :
    Exec clearPositions r.store 4 (positionsCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
def clearEnds : Block 19 := .seq (.action (.clear 17)) (.action (.clear 18))
def endsCleared (r : Work) : Work := {r with rowResult := [], scratch := []}
theorem clearEnds_exec (r : Work) :
    Exec clearEnds r.store 2 (endsCleared r).store := Exec.seq (.action _ _) (.action _ _)

def load : Block 38 := .seq (.action (.copy 9 36)) <|
  .seq (.action (.copy 10 37)) <| .seq (.action (.copy 11 35)) (.action (.copy 16 33))
def loaded (r : Work) (data : SourceLinePullback.Saved) : Work :=
  {r with
    normal := data.pulledNormal, activity := data.pulledActivity,
    width := data.rightWidth, rowWidth := data.leftWidth}
theorem load_exec (r : Work) (data : SourceLinePullback.Saved) :
    Exec load (workStore r data) 4 (workStore (loaded r data) data) := by
  let a := {r with normal := data.pulledNormal}
  let b := {a with activity := data.pulledActivity}
  let c := {b with width := data.rightWidth}
  have first : Exec (.action (.copy (9 : Fin 38) 36)) (workStore r data) 1 (workStore a data) :=
    copy_from_saved r.store (frame data) 9 17
  have second : Exec (.action (.copy (10 : Fin 38) 37)) (workStore a data) 1 (workStore b data) :=
    copy_from_saved a.store (frame data) 10 18
  have third : Exec (.action (.copy (11 : Fin 38) 35)) (workStore b data) 1 (workStore c data) :=
    copy_from_saved b.store (frame data) 11 16
  have fourth : Exec (.action (.copy (16 : Fin 38) 33)) (workStore c data) 1 (workStore (loaded r data) data) :=
    copy_from_saved c.store (frame data) 16 14
  exact Exec.seq first (Exec.seq second (Exec.seq third fourth))

def prepare : Block 38 := .seq (Frame.block 19 clearPositions) <|
  .seq (Frame.block 19 clearEnds) load
def ready (r : Work) (data : SourceLinePullback.Saved) : Work :=
  loaded (endsCleared (positionsCleared r)) data
theorem prepare_exec (r : Work) (data : SourceLinePullback.Saved) :
    Exec prepare (workStore r data) 10 (workStore (ready r data) data) :=
  Exec.seq (Frame.execution (clearPositions_exec r) (frame data))
    (Exec.seq (Frame.execution (clearEnds_exec (positionsCleared r)) (frame data))
      (load_exec (endsCleared (positionsCleared r)) data))
def searchStart {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  store (SourceMatrixWitness.start (fromPullback F alpha).core
    (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha))
    (SourceLinePullback.resultData F alpha)
theorem ready_state {n : Nat} (F : Family n) (alpha : Affine n) :
    workStore (ready (fromPullback F alpha) (SourceLinePullback.resultData F alpha)) (SourceLinePullback.resultData F alpha) =
      searchStart F alpha := rfl
theorem source_prepare_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepare (SourceLinePullback.result F alpha) 10 (searchStart F alpha) := by
  rw [pullback_state, ← ready_state]
  exact prepare_exec _ _

theorem saved_get (core : Store 19) (data : SourceLinePullback.Saved) (i : Fin 14) :
    (store core data).get (Frame.frameIndex 24 i) = data.store.get i := by
  have first := Frame.get_frame core (frame data) (Frame.frameIndex 5 i)
  have second := Frame.get_frame (SourceLinePullback.emptyFrame 5) data.store i
  have position : Frame.frameIndex 19 (Frame.frameIndex 5 i) = Frame.frameIndex 24 i := by
    apply Fin.ext
    change 19 + (5 + i.val) = 24 + i.val
    omega
  rw [position] at first
  exact first.trans second

end PNP.Concrete.ResidualReduction.SourceLineWitness
