import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChoice

/-! Discover the chart from the parsed selected direction, transform every
original row with the selected weights, and retain the actual pivot and tail
needed for solution reconstruction. All fields cross the boundary as bytes. -/

namespace PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChart
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceWitnessSelection
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorState
open PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChoice (loaded)

def prepare : Block 56 := .seq (.action (.copy 0 49)) <|
  .seq (.action (.push 1 false)) <| .seq (.action (.copy 9 48)) <|
  .seq (.action (.copy 12 50)) <| .seq (.action (.push 12 true)) (.action (.copy 13 53))

theorem prepare_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    Exec prepare (work [] [] (loaded F w)) 6
      (state15 (SourceChartSelectedFamily.initial F w.weights w.direction) (loaded F w)) := by
  simp only [loaded,SourceOriginalSuccessorChoice.normalsAfter,SourceOriginalSuccessorChoice.before,
    SourceOriginalSuccessorInput.data,SourceChartSelectedFamily.initial,SourceChartSelectedFamily.saved,
    List.replicate_succ]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))

def block : Block 56 := .seq prepare (use15 SourceChartSelectedFamily.block)
def chosenFuel {n : Nat} (F : Family (n + 1)) (c : Fin (n + 1) × Point n) : Nat :=
  13 * c.1.val + 33 + SourceChartFamily.fuel n c.1.val F.length
def success {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Store 56 :=
  state15 (SourceChartSelectedFamily.success F w.weights c) (loaded F w)
def absent {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) : Store 56 :=
  state15 (SourceChartStream.full {SourceChartSelection.absent (n + 1) with output := [false]}
    (SourceChartSelectedFamily.saved F w.weights)) (loaded F w)

theorem chosen_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) (h : SourceBalance.chooseChart w.direction = some c) :
    Exec block (work [] [] (loaded F w)) (chosenFuel F c) (success F w c) := by
  have run := use15_exec (SourceChartSelectedFamily.chosen_exec F w.weights w.direction c h) (loaded F w)
  have cost : chosenFuel F c = 6 + (13 * c.1.val + 27 + SourceChartFamily.fuel n c.1.val F.length) := by
    unfold chosenFuel
    omega
  simpa only [block,cost,success] using Exec.seq (prepare_exec F w) run

theorem absent_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (h : SourceBalance.chooseChart w.direction = none) :
    Exec block (work [] [] (loaded F w)) (5 * (n + 1) + 12) (absent F w) := by
  have run := use15_exec (SourceChartSelectedFamily.absent_exec F w.weights w.direction h) (loaded F w)
  have cost : 5 * (n + 1) + 12 = 6 + (5 * (n + 1) + 6) := by omega
  simpa only [block,cost,absent] using Exec.seq (prepare_exec F w) run

def family {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Family (n + 1) :=
  SourceChartFamily.result F w.weights c.1 c.2
def retained {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) : Saved :=
  {loaded F w with choice := (SourceEncoding.familyCodec (n + 1)).encode (family F w c),pivot := List.replicate c.1.val true,tail := (SourceEncoding.pointCodec n).encode c.2}

def captureMoves : Block 56 := .seq (save .choice 8) <|
  .seq (.action (.pop 49)) <| .seq (save .pivot 10) (save .tail 11)
def capture : Block 56 := .seq captureMoves reset

theorem capture_exec {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    Exec capture (success F w c) 53 (work [] [] (retained F w c)) := by
  let r := Frame.join (SourceChartSelectedFamily.success F w.weights c) (Store.empty 33)
  have moves : Exec captureMoves (success F w c) 4 (full r (retained F w c)) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  exact Exec.seq moves (reset_exec r (retained F w c))

theorem success_output {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length)
    (c : Fin (n + 1) × Point n) :
    (success F w c).get 8 = true :: (SourceEncoding.familyCodec (n + 1)).encode (family F w c) := rfl
theorem absent_output {n : Nat} (F : Family (n + 1)) (w : Choice (n + 1) F.length) :
    (absent F w).get 8 = [false] := rfl
theorem chosenFuel_bound {n : Nat} (F : Family (n + 1)) (c : Fin (n + 1) × Point n) :
    let L := (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩).length
    chosenFuel F c ≤ (70 * L + 159) * L + 46 := by
  dsimp only
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have pivot := c.1.isLt
  have familyBound := SourceChartFamily.fuel_source_bound F c.1
  dsimp only at familyBound
  simp only [chosenFuel,Nat.add_mul,Nat.mul_assoc] at *
  omega

end PNP.Concrete.ResidualReduction.SourceOriginalSuccessorChart
