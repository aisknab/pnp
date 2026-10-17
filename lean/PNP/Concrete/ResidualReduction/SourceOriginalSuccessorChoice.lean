import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorInput

/-! Read the actual selected Choice. Optional normals and weights are split by
the parsed source dimensions; the direction suffix is retained for chart discovery.
The loader theorem holds for arbitrary choices, while the outer program supplies
only the actual raw selector output. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChoice
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete.ResidualReduction.MatrixInstructions

def bytes {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : BitString :=
  (SourceChoiceEncoding.codec (n + 1) F.length).encode (some w)
def weightBytes {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : BitString :=
  (SourceEncoding.pointCodec F.length).encode w.weights
def directionBytes {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : BitString :=
  (SourceEncoding.pointCodec (n + 1)).encode w.direction
def normalBytes {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : BitString :=
  (SourceChartedSuccessorState.normalsCodec n).encode w.normals

theorem bytes_eq {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    bytes F w = true :: (normalBytes F w ++ (weightBytes F w ++ directionBytes F w)) := rfl

def before {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : Saved :=
  SourceOriginalSuccessorInput.data F (bytes F w)
def normalSaved (n : Nat) : SourceChartedSuccessorState.Saved :=
  {SourceChartedSuccessorState.emptySaved with dimension := List.replicate n true}
def normalsAfter {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : Saved :=
  {before F w with choice := weightBytes F w ++ directionBytes F w,normals := normalBytes F w}
def loaded {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : Saved :=
  {normalsAfter F w with choice := directionBytes F w,weights := weightBytes F w}

def normalPrepare : Block 56 := .seq (.action (.copy 0 49)) <|
  .seq (.action (.pop 0)) <| .seq (.action (.copy 23 50)) (.action (.pop 23))
def normalCapture : Block 56 := .seq (save .choice 0) <| .seq (save .normals 25) reset
def normals : Block 56 := .seq normalPrepare <|
  .seq (use29 SourceChartedSuccessorNormals.block) normalCapture

theorem normals_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    Exec normals (work [] [] (before F w))
      (SourceChartedSuccessorNormals.fuel n w.normals.isSome + 55)
      (work [] [] (normalsAfter F w)) := by
  let suffix := weightBytes F w ++ directionBytes F w
  let inner := SourceChartedSuccessorState.work (normalBytes F w ++ suffix) [] (normalSaved n)
  have prepare : Exec normalPrepare (work [] [] (before F w)) 4
      (state29 inner (before F w)) := by
    simp only [before,SourceOriginalSuccessorInput.data,bytes_eq,List.replicate_succ]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have parse := use29_exec
    (SourceChartedSuccessorNormals.block_exec w.normals suffix SourceChartedSuccessorState.emptySaved)
    (before F w)
  let after := SourceChartedSuccessorState.work suffix []
    {normalSaved n with normals := normalBytes F w}
  have clear := reset_exec (Frame.join after (Store.empty 19)) (normalsAfter F w)
  have cost : SourceChartedSuccessorNormals.fuel n w.normals.isSome + 55 =
      4 + (SourceChartedSuccessorNormals.fuel n w.normals.isSome + (1 + (1 + 49))) := by omega
  have store := save_exec Field.choice 0 (Frame.join after (Store.empty 19)) (before F w)
  have normalStore := save_exec Field.normals 25 (Frame.join after (Store.empty 19))
    (fieldSet .choice (before F w) suffix)
  simpa only [normals,normalCapture,cost,inner,after,normalSaved,normalBytes,
    normalsAfter,fieldSet,suffix] using
    Exec.seq prepare (Exec.seq parse (Exec.seq store (Exec.seq normalStore clear)))

def weightPrepare : Block 56 := .seq (.action (.copy 0 49)) (.action (.copy 2 51))
def weightCapture : Block 56 := .seq (save .weights 8) <| .seq (save .choice 0) reset
def weights : Block 56 := .seq weightPrepare <| .seq (core copyLoop) <|
  .seq (core ClauseQuery.reverseLoop) weightCapture

theorem weights_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    Exec weights (work [] [] (normalsAfter F w)) (9 * F.length + 55)
      (work [] [] (loaded F w)) := by
  let suffix := directionBytes F w
  let base := SourceScalarState.work suffix
  let r := {base with input := weightBytes F w ++ suffix,remaining := List.replicate F.length true}
  let copied := {base with excess := (weightBytes F w).reverse}
  let reversed := {base with output := weightBytes F w}
  have prepare : Exec weightPrepare (work [] [] (normalsAfter F w)) 2
      (withCore r (normalsAfter F w)) := Exec.seq (.action _ _) (.action _ _)
  have copy : Exec copyLoop r.store (5 * F.length + 1) copied.store := by
    simpa only [r,copied,weightBytes,SourceEncoding.point_length,base,SourceScalarState.work,
      List.append_nil] using copy_exec base (weightBytes F w) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * F.length + 1) reversed.store := by
    simpa only [copied,reversed,weightBytes,SourceEncoding.point_length,List.length_reverse,
      List.reverse_reverse,base,SourceScalarState.work,List.append_nil] using
      ClauseQuery.reverse_exec base (weightBytes F w).reverse
  let coreStore := Frame.join reversed.store (Store.empty 39)
  have store := save_exec Field.weights 8 coreStore (normalsAfter F w)
  have direction := save_exec Field.choice 0 coreStore
    (fieldSet .weights (normalsAfter F w) (weightBytes F w))
  have clear := reset_exec coreStore (loaded F w)
  have cost : 9 * F.length + 55 = 2 + ((5 * F.length + 1) + ((4 * F.length + 1) + (1 + (1 + 49)))) := by omega
  simpa only [weights,weightCapture,cost,coreStore,withCore,reversed,base,SourceScalarState.work,
    fieldSet,loaded,suffix] using Exec.seq prepare (Exec.seq (core_exec copy (normalsAfter F w))
      (Exec.seq (core_exec reverse (normalsAfter F w)) (Exec.seq store (Exec.seq direction clear))))

def block : Block 56 := .seq normals weights
def fuel {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : Nat :=
  SourceChartedSuccessorNormals.fuel n w.normals.isSome + 9 * F.length + 110
theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    Exec block (work [] [] (before F w)) (fuel F w) (work [] [] (loaded F w)) := by
  have cost : fuel F w = (SourceChartedSuccessorNormals.fuel n w.normals.isSome + 55) +
      (9 * F.length + 55) := by unfold fuel; omega
  simpa only [block,cost] using Exec.seq (normals_exec F w) (weights_exec F w)
theorem fuel_bound {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    fuel F w ≤ 18 * n + 9 * F.length + 160 := by
  have bound := SourceChartedSuccessorNormals.fuel_bound n w.normals.isSome
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChoice
