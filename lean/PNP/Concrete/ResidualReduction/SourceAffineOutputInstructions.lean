import PNP.Concrete.ResidualReduction.SourceAffineSearchCorrectness
import PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions

/-! Literal emission of a selected affine-query witness. The original map is
read again to construct the selected weights, a counted program constructs the
direction, and one common reversal produces the canonical pair byte order.
This phase accepts retained indices, not caller-supplied witness bytes. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineOutput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def core (r : SourceAffineSearch.State) : MatrixReconstruction.State := r.core.core.core.core
def setCore (r : SourceAffineSearch.State) (after : MatrixReconstruction.State) : SourceAffineSearch.State :=
  {r with core := {r.core with core := {r.core.core with core := {r.core.core.core with core := after}}}}
def setRegisters (r : SourceAffineSearch.State) (after : Registers) : SourceAffineSearch.State :=
  setCore r {core r with core := after}
def lift12 (body : Block 12) : Block 22 :=
  SourceAffineSearch.lifted (SourceCandidateDirectionSearch.lifted (SourceCandidateEvaluation.lift12 body))
def lift9 (body : Block 9) : Block 22 := lift12 (MatrixReconstruction.lift body)

theorem lift12_exec (body : Block 12) (r : SourceAffineSearch.State) (fuel : Nat)
    (after : MatrixReconstruction.State) (checked : Exec body (core r).store fuel after.store) :
    Exec (lift12 body) r.store fuel (setCore r after).store :=
  SourceAffineSearch.lifted_exec _ r fuel _
    (SourceCandidateDirectionSearch.lifted_exec _ r.core fuel _
      (SourceCandidateEvaluation.lift12_exec body r.core.core fuel after checked))
theorem lift9_exec (body : Block 9) (r : SourceAffineSearch.State) (fuel : Nat)
    (after : Registers) (checked : Exec body (core r).core.store fuel after.store) :
    Exec (lift9 body) r.store fuel (setRegisters r after).store :=
  lift12_exec _ r fuel _ (MatrixReconstruction.lift_exec body (core r) fuel after checked)

def holder {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Nat) : SourceAffineSearch.State :=
  SourceAffineSearch.ready F forms q.isSome (SourceCandidateMapInstructions.cursor q) j 0 0 true
def mapState {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (j : Nat) (input output : BitString) : SourceAffineSearch.State :=
  setCore (holder F forms q j) (SourceCandidateMapInstructions.ready k q [] input [] output)
def weights {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) : BitString :=
  (SourceEncoding.pointCodec F.length).encode (mapEval forms (SourceCandidateMapInstructions.parameter q))
def witnessCodec (rows n : Nat) : Codec (Option (Point rows × Point n)) :=
  optionCodec (pairCodec (SourceEncoding.pointCodec rows) (SourceEncoding.pointCodec n))

def prepareData : Block 22 := .seq (.action (.copy 0 16)) (.action (.clear 8))
def prepareCounters : Block 22 := .seq (.action (.copy 9 17))
  (.seq (.action (.copy 10 18)) (.action (.copy 11 19)))
def prepareMap : Block 22 := .seq prepareData prepareCounters

theorem prepareMap_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Nat) :
    Exec prepareMap (holder F forms q j).store 5 (mapState F forms q j (mapBits forms) []).store := by
  let before := holder F forms q j
  let middle := setRegisters before {(core before).core with input := mapBits forms, output := []}
  have data : Exec prepareData before.store 2 middle.store := Exec.seq (.action _ _) (.action _ _)
  let width := setCore middle {core middle with width := List.replicate k true}
  let index := setCore width {core width with history := List.replicate (SourceCandidateMapInstructions.cursor q) true}
  have copiedWidth : Exec (.action (.copy (9 : Fin 22) 17)) middle.store 1 width.store := .action _ _
  have copiedIndex : Exec (.action (.copy (10 : Fin 22) 18)) width.store 1 index.store := .action _ _
  have copiedMarker : Exec (.action (.copy (11 : Fin 22) 19)) index.store 1
      (mapState F forms q j (mapBits forms) []).store := by
    cases q <;> exact .action _ _
  have counters : Exec prepareCounters middle.store 3 (mapState F forms q j (mapBits forms) []).store :=
    Exec.seq copiedWidth (Exec.seq copiedIndex copiedMarker)
  exact Exec.seq data counters

theorem map_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Nat) :
    Exec (lift12 SourceCandidateMapInstructions.loop) (mapState F forms q j (mapBits forms) []).store
      (SourceCandidateMapInstructions.loopFuel k q F.length) (mapState F forms q j [] (weights F forms q).reverse).store := by
  have checked := SourceCandidateMapInstructions.loop_exec forms q [] []
  simp only [List.append_nil] at checked
  exact lift12_exec _ (mapState F forms q j (mapBits forms) []) _ _ checked

def prepareDirection : Block 22 := .seq (.action (.copy 1 15)) (.action (.copy 2 14))
def directionState {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (j : Nat) (output : BitString) : SourceAffineSearch.State :=
  let r := mapState F forms q j [] output
  setRegisters r {(core r).core with target := List.replicate j true, remaining := List.replicate n true}

theorem prepareDirection_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Nat) (output : BitString) :
    Exec prepareDirection (mapState F forms q j [] output).store 2 (directionState F forms q j output).store :=
  Exec.seq (.action _ _) (.action _ _)

theorem direction_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Fin n) (output : BitString) :
    Exec (lift9 SourceUnitDirectionInstructions.block) (directionState F forms q j.val output).store
      (SourceUnitDirectionInstructions.fuel n j.val)
      (mapState F forms q j.val [] (((SourceEncoding.pointCodec n).encode (unitPoint n j)).reverse ++ output)).store :=
  lift9_exec _ (directionState F forms q j.val output) _ _
    (SourceUnitDirectionInstructions.block_exec (core (mapState F forms q j.val [] output)).core n j)

def emitDirection : Block 22 := .seq prepareDirection (lift9 SourceUnitDirectionInstructions.block)
def pairBits {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Fin n) : BitString :=
  weights F forms q ++ (SourceEncoding.pointCodec n).encode (unitPoint n j)

theorem emitDirection_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Fin n) :
    Exec emitDirection (mapState F forms q j.val [] (weights F forms q).reverse).store
      (2 + SourceUnitDirectionInstructions.fuel n j.val) (mapState F forms q j.val [] (pairBits F forms q j).reverse).store := by
  simpa only [emitDirection, pairBits, List.reverse_append] using
    Exec.seq (prepareDirection_exec F forms q j.val (weights F forms q).reverse)
      (direction_exec F forms q j (weights F forms q).reverse)

theorem reorder_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (j : Nat) (word : BitString) :
    Exec (lift12 SourceCandidateMapInstructions.reorder) (mapState F forms q j [] word.reverse).store
      (4 * word.length + 3) (mapState F forms q j [] word).store :=
  lift12_exec _ (mapState F forms q j [] word.reverse) _ _ (SourceCandidateMapInstructions.reorder_exec k q word)

def tag : Block 22 := .action (.push 8 true)
def result {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Fin n) : SourceAffineSearch.State :=
  mapState F forms q j.val [] ((witnessCodec F.length n).encode (some (mapEval forms (SourceCandidateMapInstructions.parameter q), unitPoint n j)))
def success : Block 22 := .seq prepareMap <| .seq (lift12 SourceCandidateMapInstructions.loop) <|
  .seq emitDirection (.seq (lift12 SourceCandidateMapInstructions.reorder) tag)
def successFuel (n k rows : Nat) (q : Option (Fin k)) (j : Nat) : Nat :=
  SourceCandidateMapInstructions.loopFuel k q rows + SourceUnitDirectionInstructions.fuel n j + 4 * (rows + n) + 11

theorem success_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Fin n) :
    Exec success (holder F forms q j.val).store (successFuel n k F.length q j.val) (result F forms q j).store := by
  have bytes : (pairBits F forms q j).length = F.length + n := by
    simp only [pairBits, weights, List.length_append, SourceEncoding.point_length]
  have reversed := reorder_exec F forms q j.val (pairBits F forms q j)
  rw [bytes] at reversed
  have tagged : Exec tag (mapState F forms q j.val [] (pairBits F forms q j)).store 1 (result F forms q j).store :=
    .action _ _
  have checked := Exec.seq (prepareMap_exec F forms q j.val)
    (Exec.seq (map_exec F forms q j.val) (Exec.seq (emitDirection_exec F forms q j) (Exec.seq reversed tagged)))
  have cost : successFuel n k F.length q j.val = 5 + (SourceCandidateMapInstructions.loopFuel k q F.length +
      ((2 + SourceUnitDirectionInstructions.fuel n j.val) + ((4 * (F.length + n) + 3) + 1))) := by
    unfold successFuel; omega
  simpa only [success, cost] using checked

theorem successFuel_bound {n k : Nat} (F : Family n) (q : Option (Fin k)) (j : Fin n) :
    successFuel n k F.length q j.val ≤ (9 * k + 29) * F.length + 8 * n + 12 := by
  have map := SourceCandidateMapInstructions.fuel_bound k q F.length
  have direction := SourceUnitDirectionInstructions.fuel_bound n j
  simp only [SourceCandidateMapInstructions.fuel, successFuel, Nat.mul_add] at map ⊢
  omega

end PNP.Concrete.ResidualReduction.SourceAffineOutput
