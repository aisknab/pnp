import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChart

/-! Construct the canonical successor packet from the actual chart output and
execute the complete scalar/candidate/gate/family pipeline. The original selected
weights and chart coordinates remain protected for final step serialization. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorApply
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChart (family retained)

def unaryPrefix (field : Field) : Block 56 := .seq (.action (.push 8 false)) (prepend field)
theorem unaryPrefix_exec (field : Field) (s : Saved) (count : Nat) (out : BitString)
    (h : field.word s = List.replicate count true) :
    Exec (unaryPrefix field) (work [] out s) (8 * count + 11)
      (work [] (natural count ++ out) s) := by
  have push : Exec (.action (.push (8 : Fin 56) false)) (work [] out s) 1
      (work [] (false :: out) s) := .action _ _
  have run := prepend_exec field s (false :: out)
  rw [h,List.length_replicate] at run
  have cost : 8 * count + 11 = 1 + (8 * count + 10) := by omega
  simpa only [unaryPrefix,cost,natural,List.append_assoc,List.singleton_append] using Exec.seq push run

def dimensionPrefix : Block 56 := .seq (.action (.push 8 false)) <|
  .seq (.action (.copy 5 50)) <| .seq (.action (.pop 5)) (core SourceChartedSuccessorWords.prepend)
theorem dimensionPrefix_exec (n : Nat) (s : Saved) (out : BitString) :
    Exec dimensionPrefix (work [] out {s with dimension := List.replicate (n + 1) true})
      (8 * n + 12) (work [] (natural n ++ out) {s with dimension := List.replicate (n + 1) true}) := by
  let saved := {s with dimension := List.replicate (n + 1) true}
  let r := SourceScalarState.work []
  let ready := SourceChartedSuccessorWords.prependReady r (List.replicate n true) (false :: out)
  have first : Exec (.seq (.action (.push (8 : Fin 56) false))
      (.seq (.action (.copy 5 50)) (.action (.pop 5)))) (work [] out saved) 3 (withCore ready saved) := by
    simp only [saved,List.replicate_succ]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have push : Exec (.action (.push (8 : Fin 56) false)) (work [] out saved) 1
      (work [] (false :: out) saved) := .action _ _
  have copy : Exec (.action (.copy (5 : Fin 56) 50)) (work [] (false :: out) saved) 1
      (withCore (SourceChartedSuccessorWords.prependReady r (List.replicate (n + 1) true) (false :: out)) saved) := .action _ _
  have pop : Exec (.action (.pop (5 : Fin 56)))
      (withCore (SourceChartedSuccessorWords.prependReady r (List.replicate (n + 1) true) (false :: out)) saved) 1
      (withCore ready saved) := by simp only [List.replicate_succ]; exact .action _ _
  have run := core_exec (SourceChartedSuccessorWords.prepend_exec r (List.replicate n true) (false :: out)) saved
  have cost : 8 * n + 12 = 1 + (1 + (1 + (8 * n + 9))) := by omega
  simpa only [dimensionPrefix,cost,List.length_replicate,ready,r,work,saved,SourceScalarState.work,
    SourceChartedSuccessorWords.prepended,natural,List.append_assoc,List.singleton_append] using
    Exec.seq push (Exec.seq copy (Exec.seq pop run))

def prepare : Block 56 := .seq (.action (.copy 8 49)) <|
  .seq (prepend .normals) <| .seq (unaryPrefix .pivot) <| .seq dimensionPrefix toInput
def prepareFuel {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Nat :=
  8 * (SourceOriginalSuccessorChoice.normalBytes F w).length + 8 * c.1.val + 8 * n + 36

theorem state29_initial_eq (input : BitString) (s : Saved) :
    state29 (SourceChartedSuccessorState.initial input) s = work input [] s := by
  rfl

theorem prepare_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    Exec prepare (work [] [] (retained F w c)) (prepareFuel F w c)
      (state29 (SourceChartedSuccessorState.initial
        (SourceChartedSuccessorInput.packet (family F w c) c.1 w.normals)) (retained F w c)) := by
  rw [state29_initial_eq]
  let s := retained F w c
  let G := (SourceEncoding.familyCodec (n + 1)).encode (family F w c)
  let N := SourceOriginalSuccessorChoice.normalBytes F w
  have load : Exec (.action (.copy (8 : Fin 56) 49)) (work [] [] s) 1 (work [] G s) := .action _ _
  have normal := prepend_exec Field.normals s G
  have pivot := unaryPrefix_exec Field.pivot s c.1.val (N ++ G) rfl
  have dimension := dimensionPrefix_exec n s (natural c.1.val ++ (N ++ G))
  have input := toInput_exec (natural n ++ (natural c.1.val ++ (N ++ G))) s
  have cost : prepareFuel F w c =
      1 + ((8 * N.length + 10) + ((8 * c.1.val + 11) + ((8 * n + 12) + 2))) := by
    unfold prepareFuel
    dsimp only [N]
    omega
  simpa only [prepare,cost,s,G,N,Field.word,retained,SourceOriginalSuccessorChoice.loaded,
    SourceOriginalSuccessorChoice.normalsAfter,SourceOriginalSuccessorChoice.before,
    SourceOriginalSuccessorInput.data,SourceOriginalSuccessorChoice.normalBytes,
    SourceChartedSuccessorInput.packet] using Exec.seq load
      (Exec.seq normal (Exec.seq pivot (Exec.seq dimension input)))

def finished {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Store 56 :=
  state29 (SourceChartedSuccessorFinish.finished (family F w c) c.1 w.normals) (retained F w c)
def block : Block 56 := .seq prepare (use29 SourceChartedSuccessorRaw.block)
def fuel {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Nat :=
  prepareFuel F w c + SourceChartedSuccessorRaw.fuel (family F w c) c.1 w.normals

theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    Exec block (work [] [] (retained F w c)) (fuel F w c) (finished F w c) :=
  Exec.seq (prepare_exec F w c)
    (use29_exec (SourceChartedSuccessorRaw.block_exec (family F w c) c.1 w.normals) (retained F w c))

def result {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Option (Family n) :=
  contract (SourceBalance.markSource F w.weights) c.1 c.2
    (SourceClosure.computedTail F w.weights c w.normals)

theorem output_eq {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    (finished F w c).get 8 = (SourceFamilyReductionEncoding.codec n).encode (result F w c) := by
  let inner := SourceChartedSuccessorFinish.finished (family F w c) c.1 w.normals
  have outer := Frame.get_core (Frame.join inner (Store.empty 19)) (retained F w c).store (8 : Fin 48)
  have middle := Frame.get_core inner (Store.empty 19) (8 : Fin 29)
  have output := SourceChartedSuccessorFinish.output_eq (family F w c) c.1 w.normals
  have exactResult := congrArg (SourceFamilyReductionEncoding.codec n).encode
    (SourceChartedSuccessorState.result_chart F w.weights c w.normals)
  exact outer.trans (middle.trans (output.trans exactResult))

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorApply
