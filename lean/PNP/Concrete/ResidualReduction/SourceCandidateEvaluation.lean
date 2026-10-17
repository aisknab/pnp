import PNP.Concrete.ResidualReduction.SourceCandidateMapLoop
import PNP.Concrete.ResidualReduction.SourceWeightedActivityInstructions

/-! One complete affine-search candidate test: derive the weight bytes from
the encoded solution map, transfer them to the actual source-family activity
program, and evaluate an arbitrary unit direction. The runtime includes the
map construction and handoff as well as every source row, for either result. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateEvaluation
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

structure State where
  core : SourceWeightedActivityInstructions.State
  source : BitString
  dimension : BitString
  direction : BitString
def State.frame (r : State) : Store 3 := .cons r.source (.cons r.dimension (.cons r.direction .nil))
def State.store (r : State) : Store 16 := Frame.join r.core.store r.frame
def lift13 (body : Block 13) : Block 16 := Frame.block 3 body
theorem lift13_exec (body : Block 13) (r : State) (fuel : Nat) (after : SourceWeightedActivityInstructions.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift13 body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame
def lift12 (body : Block 12) : Block 16 := lift13 (SourceWeightedActivityInstructions.lifted body)
theorem lift12_exec (body : Block 12) (r : State) (fuel : Nat) (after : MatrixReconstruction.State)
    (checked : Exec body r.core.core.store fuel after.store) :
    Exec (lift12 body) r.store fuel ({r with core := {r.core with core := after}}).store :=
  lift13_exec _ r fuel _ (SourceWeightedActivityInstructions.lifted_exec body r.core fuel after checked)

def initial {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Nat) : State :=
  ⟨⟨SourceCandidateMapInstructions.ready k q [] (mapBits forms) [] [], []⟩,
    familyBits F, List.replicate n true, List.replicate j true⟩
def mapped {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Nat) : State :=
  ⟨⟨SourceCandidateMapInstructions.ready k q [] [] []
      ((SourceEncoding.pointCodec F.length).encode (mapEval forms (SourceCandidateMapInstructions.parameter q))), []⟩,
    familyBits F, List.replicate n true, List.replicate j true⟩
def loaded {n : Nat} (F : Family n) (w : Point F.length) (j : Nat) : State :=
  ⟨SourceWeightedActivityInstructions.ready n j (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) [],
    familyBits F, List.replicate n true, List.replicate j true⟩
def result {n : Nat} (F : Family n) (j : Nat) (value : Bool) : State :=
  ⟨SourceWeightedActivityInstructions.ready n j [] [] [value],
    familyBits F, List.replicate n true, List.replicate j true⟩

def copyData : Block 16 := .seq (.action (.copy 12 8)) (.seq (.action (.clear 8)) (.action (.copy 0 13)))
def copyCounters : Block 16 := .seq (.action (.copy 9 14)) (.seq (.action (.copy 10 15)) (.action (.copy 11 14)))
def prepare : Block 16 := .seq copyData copyCounters

theorem prepare_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Nat) :
    Exec prepare (mapped F forms q j).store 6
      (loaded F (mapEval forms (SourceCandidateMapInstructions.parameter q)) j).store := by
  let before := mapped F forms q j
  let weights := (SourceEncoding.pointCodec F.length).encode (mapEval forms (SourceCandidateMapInstructions.parameter q))
  let middle : State := {before with core := ⟨{before.core.core with core := {before.core.core.core with input := familyBits F, output := []}}, weights⟩}
  have data : Exec copyData before.store 3 middle.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have counters : Exec copyCounters middle.store 3
      (loaded F (mapEval forms (SourceCandidateMapInstructions.parameter q)) j).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq data counters

def block : Block 16 := .seq (lift12 SourceCandidateMapInstructions.block)
  (.seq prepare (lift13 SourceWeightedActivityInstructions.test))
def fuel (n k rows : Nat) (q : Option (Fin k)) (j : Nat) : Nat :=
  SourceCandidateMapInstructions.fuel k q rows + 6 + (SourceWeightedActivityInstructions.fuel n j rows + 1)

theorem block_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Fin n) :
    Exec block (initial F forms q j.val).store (fuel n k F.length q j.val)
      (result F j.val (weightedActivity F (mapEval forms (SourceCandidateMapInstructions.parameter q))
        (unitPoint n j))).store := by
  have construction : Exec (lift12 SourceCandidateMapInstructions.block) (initial F forms q j.val).store
      (SourceCandidateMapInstructions.fuel k q F.length) (mapped F forms q j.val).store :=
    lift12_exec _ (initial F forms q j.val) _ (mapped F forms q j.val).core.core
      (SourceCandidateMapInstructions.block_exec forms q)
  have prepared := prepare_exec F forms q j.val
  let weights := mapEval forms (SourceCandidateMapInstructions.parameter q)
  have tested : Exec (lift13 SourceWeightedActivityInstructions.test) (loaded F weights j.val).store
      (SourceWeightedActivityInstructions.fuel n j.val F.length + 1)
      (result F j.val (weightedActivity F weights (unitPoint n j))).store :=
    lift13_exec _ (loaded F weights j.val) _ (result F j.val (weightedActivity F weights (unitPoint n j))).core
      (SourceWeightedActivityInstructions.test_exec F weights j [])
  have cost : fuel n k F.length q j.val =
      SourceCandidateMapInstructions.fuel k q F.length + (6 + (SourceWeightedActivityInstructions.fuel n j.val F.length + 1)) := by
    unfold fuel; omega
  simpa only [block, cost] using Exec.seq construction (Exec.seq prepared tested)

theorem fuel_bound {n k : Nat} (F : Family n) (q : Option (Fin k)) (j : Fin n) :
    fuel n k F.length q j.val ≤ (9 * k + 24 * n + 98) * F.length + 12 := by
  have candidate := SourceCandidateMapInstructions.fuel_bound k q F.length
  have evaluation := SourceWeightedActivityInstructions.fuel_bound F j
  simp only [fuel, Nat.add_mul] at candidate evaluation ⊢
  omega

theorem computed_fuel_bound {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s)
    (q : Option (Fin s.parameters)) (j : Fin n) :
    fuel n s.parameters F.length q j.val ≤ (9 * F.length + 24 * n + 98) * F.length + 12 := by
  have parameters := solve_some_parameter_bound (SourceClosure.affineMaskRows F) s computed
  have mono := Nat.mul_le_mul_right F.length
    (show 9 * s.parameters + 24 * n + 98 ≤ 9 * F.length + 24 * n + 98 by omega)
  exact Nat.le_trans (fuel_bound F q j) (by omega)

end PNP.Concrete.ResidualReduction.SourceCandidateEvaluation
