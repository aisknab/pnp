import PNP.Concrete.ResidualReduction.SourceCandidateEvaluation
import PNP.Concrete.ResidualReduction.SourceMatrixSchedule

/-! Ordered finite-instruction search over every unit direction for one
computed affine parameter. Failed candidates are evaluated and charged in
full. The first successful index is retained; exhaustion is a separate false
result, including the zero-dimensional case. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def scan (p : Nat → Bool) : Nat → Nat → Nat × Bool
  | 0, j => (j, false)
  | count + 1, j => if p j then (j, true) else scan p count (j + 1)

theorem scan_first (p : Nat → Bool) (count j : Nat) :
    SourcePlane.firstTrue p (List.range' j count) =
      if (scan p count j).2 then some (scan p count j).1 else none := by
  induction count generalizing j with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ]
    cases h : p j <;> simp only [SourcePlane.firstTrue, scan, h, Bool.false_eq_true,
      if_false, if_true, ih]

def active {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) (j : Nat) : Bool :=
  if h : j < n then weightedActivity F (mapEval forms (SourceCandidateMapInstructions.parameter q)) (unitPoint n ⟨j, h⟩)
  else false
theorem active_fin {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Fin n) :
    active F forms q j.val = weightedActivity F (mapEval forms (SourceCandidateMapInstructions.parameter q)) (unitPoint n j) := by
  simp only [active, dif_pos j.isLt]

structure State where
  core : SourceCandidateEvaluation.State
  sourceMap : BitString
  parameters : BitString
  parameterIndex : BitString
  parameterMarker : BitString
  remaining : BitString
def State.frame (r : State) : Store 5 :=
  .cons r.sourceMap (.cons r.parameters (.cons r.parameterIndex (.cons r.parameterMarker (.cons r.remaining .nil))))
def State.store (r : State) : Store 21 := Frame.join r.core.store r.frame
def lifted (body : Block 16) : Block 21 := Frame.block 5 body
theorem lifted_exec (body : Block 16) (r : State) (fuel : Nat) (after : SourceCandidateEvaluation.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store := Frame.execution checked r.frame

def ready {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (j count : Nat) (found : Bool) : State :=
  ⟨SourceCandidateEvaluation.result F j found, mapBits forms, List.replicate k true,
    List.replicate (SourceCandidateMapInstructions.cursor q) true,
    List.replicate (SourceCandidateMapInstructions.marker q) true, List.replicate count true⟩
def prepared {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (j count : Nat) : State :=
  {ready F forms q j count false with core := SourceCandidateEvaluation.initial F forms q j}

def prepareData : Block 21 := .seq (.action (.copy 0 16)) (.action (.clear 8))
def prepareCounters : Block 21 := .seq (.action (.copy 9 17))
  (.seq (.action (.copy 10 18)) (.action (.copy 11 19)))
def prepare : Block 21 := .seq prepareData prepareCounters
theorem prepare_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j count : Nat) :
    Exec prepare (ready F forms q j count false).store 5 (prepared F forms q j count).store := by
  let before := ready F forms q j count false
  let registers := {before.core.core.core.core with input := mapBits forms, output := []}
  let middle : State := {before with core := {before.core with core := {before.core.core with core := {before.core.core.core with core := registers}}}}
  have data : Exec prepareData before.store 2 middle.store := Exec.seq (.action _ _) (.action _ _)
  have counters : Exec prepareCounters middle.store 3 (prepared F forms q j count).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq data counters

def nextDirection : Block 21 := .seq (.action (.push 10 true))
  (.seq (.action (.push 15 true)) (.action (.pop 20)))
def decide : Block 21 := .branch 8 nextDirection nextDirection (.action (.clear 20))
def step : Block 21 := .seq prepare (.seq (lifted SourceCandidateEvaluation.block) decide)

theorem evaluate_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Fin n) (count : Nat) :
    Exec (lifted SourceCandidateEvaluation.block) (prepared F forms q j.val count).store
      (SourceCandidateEvaluation.fuel n k F.length q j.val)
      (ready F forms q j.val count (active F forms q j.val)).store := by
  rw [active_fin]
  exact lifted_exec _ (prepared F forms q j.val count) _ _ (SourceCandidateEvaluation.block_exec F forms q j)

theorem step_false {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Fin n) (count : Nat) (failed : active F forms q j.val = false) :
    Exec step (ready F forms q j.val (count + 1) false).store
      (SourceCandidateEvaluation.fuel n k F.length q j.val + 9)
      (ready F forms q (j.val + 1) count false).store := by
  have tested := evaluate_exec F forms q j (count + 1)
  rw [failed] at tested
  have moved : Exec nextDirection (ready F forms q j.val (count + 1) false).store 3
      (ready F forms q (j.val + 1) count false).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have finish : Exec decide (ready F forms q j.val (count + 1) false).store 4
      (ready F forms q (j.val + 1) count false).store := Exec.zero (source := (8 : Fin 21)) rfl moved
  have cost : SourceCandidateEvaluation.fuel n k F.length q j.val + 9 =
      5 + (SourceCandidateEvaluation.fuel n k F.length q j.val + 4) := by omega
  simpa only [step, cost] using Exec.seq (prepare_exec F forms q j.val (count + 1)) (Exec.seq tested finish)

theorem step_true {n k : Nat} (F : Family n) (forms : AffineMap F.length k)
    (q : Option (Fin k)) (j : Fin n) (count : Nat) (found : active F forms q j.val = true) :
    Exec step (ready F forms q j.val (count + 1) false).store
      (SourceCandidateEvaluation.fuel n k F.length q j.val + 7)
      (ready F forms q j.val 0 true).store := by
  have tested := evaluate_exec F forms q j (count + 1)
  rw [found] at tested
  have finish : Exec decide (ready F forms q j.val (count + 1) true).store 2
      (ready F forms q j.val 0 true).store := Exec.one (source := (8 : Fin 21)) rfl (.action _ _)
  have cost : SourceCandidateEvaluation.fuel n k F.length q j.val + 7 =
      5 + (SourceCandidateEvaluation.fuel n k F.length q j.val + 2) := by omega
  simpa only [step, cost] using Exec.seq (prepare_exec F forms q j.val (count + 1)) (Exec.seq tested finish)

def loop : Block 21 := .loop 20 step
def fuel {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) : Nat → Nat → Nat
  | 0, _ => 1
  | count + 1, j => if active F forms q j then
      1 + ((SourceCandidateEvaluation.fuel n k F.length q j + 7) + 1)
    else 1 + ((SourceCandidateEvaluation.fuel n k F.length q j + 9) + fuel F forms q count (j + 1))

theorem loop_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (count j : Nat) (bound : j + count ≤ n) :
    Exec loop (ready F forms q j count false).store (fuel F forms q count j)
      (ready F forms q (scan (active F forms q) count j).1 0 (scan (active F forms q) count j).2).store := by
  induction count generalizing j with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have inside : j < n := by omega
    let current : Fin n := ⟨j, inside⟩
    cases h : active F forms q j with
    | false =>
      have first := step_false F forms q current count h
      have rest := ih (j + 1) (by omega)
      have checked := Exec.loopStep (source := (20 : Fin 21)) rfl first rest
      simpa only [loop, fuel, scan, h, Bool.false_eq_true, if_false, current] using checked
    | true =>
      have first := step_true F forms q current count h
      have last : Exec loop (ready F forms q j 0 true).store 1 (ready F forms q j 0 true).store :=
        Exec.loopStop rfl
      have checked := Exec.loopStep (source := (20 : Fin 21)) rfl first last
      simpa only [loop, fuel, scan, h, Bool.true_eq, if_true, current] using checked

theorem fuel_bound {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k))
    (count j : Nat) (bound : j + count ≤ n) :
    fuel F forms q count j ≤ ((9 * k + 24 * n + 98) * F.length + 22) * count + 1 := by
  induction count generalizing j with
  | zero => exact Nat.le_refl 1
  | succ count ih =>
    have inside : j < n := by omega
    have one := SourceCandidateEvaluation.fuel_bound F q (⟨j, inside⟩ : Fin n)
    change SourceCandidateEvaluation.fuel n k F.length q j ≤ (9 * k + 24 * n + 98) * F.length + 12 at one
    have rest := ih (j + 1) (by omega)
    cases h : active F forms q j <;>
      simp only [fuel, h, Bool.false_eq_true, if_false, if_true, Nat.mul_add, Nat.mul_one] <;> omega

theorem complete_exec {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) :
    Exec loop (ready F forms q 0 n false).store (fuel F forms q n 0)
      (ready F forms q (scan (active F forms q) n 0).1 0 (scan (active F forms q) n 0).2).store :=
  loop_exec F forms q n 0 (by omega)

theorem computed_fuel_bound {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) (q : Option (Fin s.parameters)) :
    fuel F s.forms q n 0 ≤ ((9 * F.length + 24 * n + 98) * F.length + 22) * n + 1 := by
  have parameters := solve_some_parameter_bound (SourceClosure.affineMaskRows F) s computed
  have rows := Nat.mul_le_mul_right F.length
    (show 9 * s.parameters + 24 * n + 98 ≤ 9 * F.length + 24 * n + 98 by omega)
  have outer := Nat.mul_le_mul_right n (show
    (9 * s.parameters + 24 * n + 98) * F.length + 22 ≤ (9 * F.length + 24 * n + 98) * F.length + 22 by omega)
  exact Nat.le_trans (fuel_bound F s.forms q n 0 (by omega)) (by omega)

theorem firstTrue_map {A B : Type} (p : B → Bool) (f : A → B) (xs : List A) :
    SourcePlane.firstTrue p (xs.map f) = (SourcePlane.firstTrue (fun a => p (f a)) xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p (f x) <;> simp only [List.map_cons, SourcePlane.firstTrue, h, ih, Option.map_some]

/-- The returned index is the first successful direction in the actual finite
query order, not merely some direction witnessing nonzero activity. -/
theorem scan_indices_exact {n k : Nat} (F : Family n) (forms : AffineMap F.length k) (q : Option (Fin k)) :
    (SourcePlane.firstTrue
      (fun j : Fin n => weightedActivity F (mapEval forms (SourceCandidateMapInstructions.parameter q)) (unitPoint n j))
      (List.finRange n)).map Fin.val =
        if (scan (active F forms q) n 0).2 then some (scan (active F forms q) n 0).1 else none := by
  have predicate : (fun j : Fin n => active F forms q j.val) =
      (fun j : Fin n => weightedActivity F (mapEval forms (SourceCandidateMapInstructions.parameter q)) (unitPoint n j)) :=
    funext (active_fin F forms q)
  rw [← scan_first, ← SourceMatrixSchedule.finite_range_values n, firstTrue_map, predicate]

theorem scan_success (p : Nat → Bool) (count j : Nat) (found : (scan p count j).2 = true) :
    (scan p count j).1 ∈ List.range' j count ∧ p (scan p count j).1 = true := by
  have first : SourcePlane.firstTrue p (List.range' j count) = some (scan p count j).1 := by
    rw [scan_first, found]
    rfl
  exact SourcePlane.firstTrue_sound p (List.range' j count) _ first

end PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch
