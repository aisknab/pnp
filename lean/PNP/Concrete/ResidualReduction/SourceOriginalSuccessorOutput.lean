import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorApply

/-! Serialize the complete optional construction, not just the reduced rows.
Successful output retains the selected weights and discovered chart coordinates
required by the existing exact model-bijection theorem. Failure remains absence. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChart (retained)

def capture : Block 56 := .seq (save .choice 8) <| .seq (.action (.pop 49)) reset
theorem capture_exec (r : Store 48) (s : Saved) (word : BitString) (h : r.get 8 = true :: word) :
    Exec capture (full r s) 51 (work [] [] (fieldSet .choice s word)) := by
  have store := save_exec Field.choice 8 r s
  rw [h] at store
  have pop : Exec (.action (.pop (49 : Fin 56))) (full r (fieldSet .choice s (true :: word))) 1
      (full r (fieldSet .choice s word)) :=
    SourceLinePullback.pop_saved r (fieldSet .choice s (true :: word)).store (1 : Fin 8)
  exact Exec.seq store (Exec.seq pop (reset_exec r (fieldSet .choice s word)))

def assembled {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) (G : Family n) : SourceClosure.ConstructedStep n F.length :=
  ⟨w.weights,c.1,c.2,G⟩
def saved {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) (G : Family n) : Saved :=
  {retained F w c with choice := (SourceEncoding.familyCodec n).encode G}
def emit : Block 56 := .seq (.action (.copy 8 49)) <|
  .seq (prepend .tail) <| .seq (SourceOriginalSuccessorApply.unaryPrefix .pivot) <|
  .seq (prepend .weights) (.action (.push 8 true))
def emitFuel (n rows pivot : Nat) : Nat := 8 * n + 8 * pivot + 8 * rows + 33

theorem emit_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) (G : Family n) :
    Exec emit (work [] [] (saved F w c G)) (emitFuel n F.length c.1.val)
      (work [] ((stepCodec n F.length).encode (some (assembled F w c G))) (saved F w c G)) := by
  let s := saved F w c G
  let out := (SourceEncoding.familyCodec n).encode G
  let tail := (SourceEncoding.pointCodec n).encode c.2
  let weights := (SourceEncoding.pointCodec F.length).encode w.weights
  have load : Exec (.action (.copy (8 : Fin 56) 49)) (work [] [] s) 1 (work [] out s) := .action _ _
  have tails := prepend_exec Field.tail s out
  have pivot := SourceOriginalSuccessorApply.unaryPrefix_exec Field.pivot s c.1.val (tail ++ out) rfl
  have weight := prepend_exec Field.weights s (natural c.1.val ++ (tail ++ out))
  have tag : Exec (.action (.push (8 : Fin 56) true))
      (work [] (weights ++ (natural c.1.val ++ (tail ++ out))) s) 1
      (work [] ((stepCodec n F.length).encode (some (assembled F w c G))) s) := .action _ _
  have cost : emitFuel n F.length c.1.val =
      1 + ((8 * n + 10) + ((8 * c.1.val + 11) + ((8 * F.length + 10) + 1))) := by
    unfold emitFuel
    omega
  simpa only [emit,cost,s,out,tail,weights,Field.word,saved,retained,
    SourceOriginalSuccessorChoice.loaded,SourceOriginalSuccessorChoice.normalsAfter,
    SourceOriginalSuccessorChoice.weightBytes,SourceEncoding.point_length] using
    Exec.seq load (Exec.seq tails (Exec.seq pivot (Exec.seq weight tag)))

def success : Block 56 := .seq capture emit
def block : Block 56 := .branch 8 failure failure success
def stepResult {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Option (SourceClosure.ConstructedStep n F.length) :=
  (SourceOriginalSuccessorApply.result F w c).map (assembled F w c)
def fuel {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Nat :=
  match SourceOriginalSuccessorApply.result F w c with
  | none => 51
  | some _ => 52 + emitFuel n F.length c.1.val
def finished {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Store 56 :=
  match SourceOriginalSuccessorApply.result F w c with
  | none => work [] [false] (retained F w c)
  | some G => work [] ((stepCodec n F.length).encode (some (assembled F w c G))) (saved F w c G)

theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    Exec block (SourceOriginalSuccessorApply.finished F w c) (fuel F w c) (finished F w c) := by
  let r := Frame.join (SourceChartedSuccessorFinish.finished
    (SourceOriginalSuccessorChart.family F w c) c.1 w.normals) (Store.empty 19)
  let s := retained F w c
  have out := SourceOriginalSuccessorApply.output_eq F w c
  cases h : SourceOriginalSuccessorApply.result F w c with
  | none =>
    rw [h] at out
    have flag : (SourceOriginalSuccessorApply.finished F w c).get 8 = [false] := out
    simpa only [block,fuel,finished,h] using
      (Exec.zero flag (failure_exec r s) : Exec block _ 51 _)
  | some G =>
    rw [h] at out
    have flag : (SourceOriginalSuccessorApply.finished F w c).get 8 =
        true :: (SourceEncoding.familyCodec n).encode G := out
    have coreFlag : r.get 8 = true :: (SourceEncoding.familyCodec n).encode G :=
      (working_get r s 8).symm.trans flag
    have capture := capture_exec r s ((SourceEncoding.familyCodec n).encode G) coreFlag
    have emit := emit_exec F w c G
    have cost : 52 + emitFuel n F.length c.1.val = 1 + (51 + emitFuel n F.length c.1.val) := by omega
    simpa only [block,fuel,finished,h,cost,saved,fieldSet,s] using
      (Exec.one flag (Exec.seq capture emit) : Exec block _ _ _)

theorem output_eq {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    (finished F w c).get 8 = (stepCodec n F.length).encode (stepResult F w c) := by
  cases h : SourceOriginalSuccessorApply.result F w c <;>
    simp only [finished,stepResult,h,Option.map] <;> rfl

theorem fuel_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    fuel F w c ≤ 8 * n + 8 * c.1.val + 8 * F.length + 85 := by
  cases h : SourceOriginalSuccessorApply.result F w c <;>
    simp only [fuel,h,emitFuel] <;> omega

theorem stepResult_build {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) (h : SourceBalance.chooseChart w.direction = some c) :
    stepResult F w c = SourceWitnessSelection.build F w := by
  simp only [SourceWitnessSelection.build,SourceClosure.buildStep,h,Option.bind]
  rfl

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorOutput
