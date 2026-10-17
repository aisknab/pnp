import PNP.Concrete.ResidualReduction.SourceBilinearEvaluationInstructions
import PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions

/-! Construct a unit parameter internally, then apply the homogeneous part
of the encoded affine map. No coordinate vector is supplied to this phase.
The original parameter width remains protected through unit construction. -/

namespace PNP.Concrete.ResidualReduction.SourceMapUnit
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

structure State where
  core : Registers
  width : BitString
def State.store (r : State) : Store 10 := Frame.join r.core.store (.cons r.width .nil)
def lift (body : Block 9) : Block 10 := Frame.block 1 body
theorem lift_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked (.cons r.width .nil)
def start {m k : Nat} (forms : AffineMap m k) (j : Fin k) : State :=
  ⟨{base 0 [] with input := mapBits forms, target := List.replicate j.val true, remaining := List.replicate k true}, List.replicate k true⟩
def unitDone {m k : Nat} (forms : AffineMap m k) (j : Fin k) : State :=
  ⟨{base 0 [] with input := mapBits forms, output := ((SourceEncoding.pointCodec k).encode (unitPoint k j)).reverse}, List.replicate k true⟩
def unitForward {m k : Nat} (forms : AffineMap m k) (j : Fin k) : State :=
  ⟨{base 0 [] with input := mapBits forms, output := (SourceEncoding.pointCodec k).encode (unitPoint k j)}, List.replicate k true⟩
def mapReady {m k : Nat} (forms : AffineMap m k) (j : Fin k) : State :=
  ⟨SourceLinearMap.ready (unitPoint k j) (mapBits forms) [], List.replicate k true⟩
def result {m k : Nat} (forms : AffineMap m k) (j : Fin k) : State :=
  ⟨SourceLinearMap.ready (unitPoint k j) [] ((SourceEncoding.pointCodec m).encode (linearMapEval forms (unitPoint k j))), List.replicate k true⟩

theorem unit_exec {m k : Nat} (forms : AffineMap m k) (j : Fin k) :
    Exec (lift SourceUnitDirectionInstructions.block) (start forms j).store
      (SourceUnitDirectionInstructions.fuel k j.val) (unitDone forms j).store := by
  apply lift_exec
  simpa only [start, unitDone, base, List.replicate_zero, List.append_nil] using
    SourceUnitDirectionInstructions.block_exec {base 0 [] with input := mapBits forms} k j
theorem reverse_exec {m k : Nat} (forms : AffineMap m k) (j : Fin k) :
    Exec (lift SourceLineQueryMatrixPadding.reverseOutput) (unitDone forms j).store
      (4 * k + 3) (unitForward forms j).store := by
  apply lift_exec
  simpa only [unitDone, unitForward, base, List.length_reverse, SourceEncoding.point_length, List.reverse_reverse] using
    SourceLineQueryMatrixPadding.reverse_output_exec {base 0 [] with input := mapBits forms}
      ((SourceEncoding.pointCodec k).encode (unitPoint k j)).reverse
def prepare : Block 10 := .seq (.action (.copy 7 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 1 9))
theorem prepare_exec {m k : Nat} (forms : AffineMap m k) (j : Fin k) :
    Exec prepare (unitForward forms j).store 3 (mapReady forms j).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
theorem map_exec {m k : Nat} (forms : AffineMap m k) (j : Fin k) :
    Exec (lift SourceLinearMap.block) (mapReady forms j).store
      (SourceLinearMap.fuel m k) (result forms j).store :=
  lift_exec _ (mapReady forms j) _ _ (SourceLinearMap.block_exec forms (unitPoint k j))
def block : Block 10 := .seq (lift SourceUnitDirectionInstructions.block) <|
  .seq (lift SourceLineQueryMatrixPadding.reverseOutput) (.seq prepare (lift SourceLinearMap.block))
def fuel (m k j : Nat) : Nat :=
  SourceUnitDirectionInstructions.fuel k j + ((4 * k + 3) + (3 + SourceLinearMap.fuel m k))
theorem block_exec {m k : Nat} (forms : AffineMap m k) (j : Fin k) :
    Exec block (start forms j).store (fuel m k j.val) (result forms j).store :=
  Exec.seq (unit_exec forms j) (Exec.seq (reverse_exec forms j) (Exec.seq (prepare_exec forms j) (map_exec forms j)))
def budget (m k : Nat) : Nat := 4 * k + ((4 * k + 3) + (3 + SourceLinearMap.fuel m k))
theorem fuel_bound {m k : Nat} (j : Fin k) : fuel m k j.val ≤ budget m k :=
  Nat.add_le_add_right (SourceUnitDirectionInstructions.fuel_bound k j) _
theorem budget_mono (m k M K : Nat) (hm : m ≤ M) (hk : k ≤ K) : budget m k ≤ budget M K := by
  have map := SourceLinearMap.fuel_mono m k M K hm hk
  unfold budget
  omega

end PNP.Concrete.ResidualReduction.SourceMapUnit
