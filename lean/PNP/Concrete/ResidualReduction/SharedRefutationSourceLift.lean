import PNP.Concrete.ResidualReduction.SharedRefutationAlgebra
import PNP.Concrete.ResidualReduction.SharedRefutationCircuit

/-! One checked source-connected refutation lift. Selection bits and cofactors
come from the retained source rows, and the substitution tail is a concrete
quadratic coefficient vector. The old residual refutation remains an explicit
invariant; this module neither searches for it nor asserts that an elimination
trace exists. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationSourceLift
open PNP.Concrete.ResidualReduction.FactoredContraction

structure HeadRow (n : Nat) where
  source : Row (n + 1)
  root : Nat

def sourceFamily {n : Nat} (rows : List (HeadRow n)) : Family (n + 1) :=
  rows.map (fun r => r.source)

def inputRow {n : Nat} (r : HeadRow n) : SharedRefutationCircuit.InputRow n :=
  ⟨r.root, r.source.selected, (qProduct r.source.left r.source.right).1⟩

def inputRows {n : Nat} (rows : List (HeadRow n)) : List (SharedRefutationCircuit.InputRow n) :=
  rows.map inputRow

def oldRoots {n : Nat} (rows : List (HeadRow n)) : List Nat :=
  rows.map (fun r => r.root)

def guardPolynomial {n : Nat} (tail : Quadratic n) : Quadratic (n + 1) :=
  (aConst n true, tail)

/-- Check the actual selected source polynomial before compiling any lift. -/
def liftChecked {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) : Option (SharedRefutationCircuit.Code n × List Nat) :=
  if qEq (scalar (sourceFamily rows)) (guardPolynomial tail) then
    SharedRefutationCircuit.compileChecked (inputRows rows) oldCode
  else none

/-- Pairing rejects either kind of length mismatch, including nonempty tails. -/
def pairedSum : List Bool → List Bool → Option Bool
  | [], [] => some false
  | a :: as, b :: bs => (pairedSum as bs).map (fun t => Bool.xor (a && b) t)
  | _, _ => none

private theorem map_false_pair (a : Bool) (o : Option Bool) :
    o.map (fun t => Bool.xor (a && false) t) = o := by
  cases o with
  | none => rfl
  | some b => cases a <;> cases b <;> rfl

/-- All-false values cannot give a refutation sum. There is no length premise:
either kind of mismatch is still rejected by `pairedSum`. -/
theorem pairedSum_ne_true_of_zero (coefficients : List Bool) :
    ∀ values : List Bool, (∀ b ∈ values, b = false) →
      pairedSum coefficients values ≠ some true := by
  induction coefficients with
  | nil =>
    intro values _
    cases values with
    | nil => intro impossible; cases impossible
    | cons b bs => intro impossible; cases impossible
  | cons a coefficients ih =>
    intro values zero
    cases values with
    | nil => intro impossible; cases impossible
    | cons b values =>
      have head : b = false := zero b List.mem_cons_self
      have tail : ∀ t ∈ values, t = false := by
        intro t ht
        exact zero t (List.mem_cons_of_mem b ht)
      subst b
      change (pairedSum coefficients values).map
        (fun t => Bool.xor (a && false) t) ≠ some true
      rw [map_false_pair]
      exact ih values tail

def originalValues {n : Nat} (rows : List (HeadRow n)) (s : Bool) (z : Point n) :
    List Bool := rows.map (fun r => r.source.eval (s, z))

/-- Exact row-wise substitution, without assuming a factored residual family. -/
def restrictedValues {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (z : Point n) : List Bool :=
  rows.map (fun r => r.source.eval (qEval tail z, z))

def originalSum {n : Nat} (rows : List (HeadRow n)) (code : SharedRefutationCircuit.Code n)
    (roots : List Nat) (s : Bool) (z : Point n) : Option Bool :=
  pairedSum (SharedRefutationCircuit.outputs code z roots) (originalValues rows s z)

def residualSum {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (code : SharedRefutationCircuit.Code n) (z : Point n) : Option Bool :=
  pairedSum (SharedRefutationCircuit.outputs code z (oldRoots rows)) (restrictedValues rows tail z)

theorem liftChecked_checks {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (checked : liftChecked rows tail oldCode = some result) :
    scalar (sourceFamily rows) = guardPolynomial tail ∧
      SharedRefutationCircuit.compileChecked (inputRows rows) oldCode = some result := by
  cases guard : qEq (scalar (sourceFamily rows)) (guardPolynomial tail) with
  | false =>
    simp only [liftChecked, guard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at checked
  | true =>
    refine ⟨(qEq_true_iff _ _).mp guard, ?_⟩
    simpa only [liftChecked, guard, ↓reduceIte] using checked

/-- The returned graph is valid, every output root exists, and row count is
preserved. All graph guarantees are reused from the checked circuit compiler. -/
theorem liftChecked_contract {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (checked : liftChecked rows tail oldCode = some result) :
    scalar (sourceFamily rows) = guardPolynomial tail ∧
      SharedRefutationCircuit.RootsBounded (inputRows rows) oldCode ∧
      SharedRefutationCircuit.codeValid result.1 = true ∧
      (∀ i ∈ result.2, i < result.1.length) ∧ result.2.length = rows.length := by
  obtain ⟨guard, compiled⟩ := liftChecked_checks rows tail oldCode result checked
  obtain ⟨_, bounds, valid, roots, count⟩ :=
    SharedRefutationCircuit.compileChecked_contract (inputRows rows) oldCode result compiled
  refine ⟨guard, bounds, valid, roots, ?_⟩
  simpa only [inputRows, List.length_map] using count

theorem liftChecked_growth {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (checked : liftChecked rows tail oldCode = some result) :
    result.1.length ≤ oldCode.length + 4 * rows.length + 1 := by
  have compiled := (liftChecked_checks rows tail oldCode result checked).2
  simpa only [inputRows, List.length_map] using
    SharedRefutationCircuit.compileChecked_growth (inputRows rows) oldCode result compiled

/- The following pointwise records are only the bridge to the finite-row
algebra theorem. The public evaluators above use one circuit table per sum. -/
private def evaluatedRow {n : Nat} (tail : Quadratic n) (code : SharedRefutationCircuit.Code n)
    (s : Bool) (z : Point n) (r : HeadRow n) : SharedRefutationAlgebra.LiftRow :=
  ⟨r.source.selected, r.source.eval (s, z), r.source.eval (qEval tail z, z),
    aEval (qProduct r.source.left r.source.right).1 z,
    SharedRefutationCircuit.value code z r.root⟩

private def evaluatedRows {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) : List SharedRefutationAlgebra.LiftRow :=
  rows.map (evaluatedRow tail code s z)

private theorem pairedSum_rowSum (rows : List SharedRefutationAlgebra.LiftRow)
    (f g : SharedRefutationAlgebra.LiftRow → Bool) :
    pairedSum (rows.map f) (rows.map g) =
      some (SharedRefutationAlgebra.rowSum (fun r => f r && g r) rows) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, pairedSum, ih, Option.map, SharedRefutationAlgebra.rowSum]

private theorem evaluatedRows_sources {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) :
    (evaluatedRows rows tail code s z).map (fun r => r.source) =
      originalValues rows s z := by
  simp only [evaluatedRows, originalValues, List.map_map, Function.comp_def, evaluatedRow]

private theorem evaluatedRows_restricted {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) :
    (evaluatedRows rows tail code s z).map (fun r => r.restricted) =
      restrictedValues rows tail z := by
  simp only [evaluatedRows, restrictedValues, List.map_map, Function.comp_def, evaluatedRow]

private theorem evaluatedRows_multipliers {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) :
    (evaluatedRows rows tail code s z).map (fun r => r.multiplier) =
      SharedRefutationCircuit.outputs code z (oldRoots rows) := by
  simp only [evaluatedRows, evaluatedRow, oldRoots,
    SharedRefutationCircuit.outputs_eq_map_value, List.map_map, Function.comp_def]

private theorem evaluatedRows_correction {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) :
    SharedRefutationAlgebra.correctionValue (evaluatedRows rows tail code s z) =
      SharedRefutationCircuit.productSum (inputRows rows) code z := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    change Bool.xor (SharedRefutationCircuit.value code z r.root &&
        aEval (qProduct r.source.left r.source.right).1 z)
        (SharedRefutationAlgebra.correctionValue (evaluatedRows rows tail code s z)) =
      Bool.xor (SharedRefutationCircuit.value code z r.root &&
        aEval (qProduct r.source.left r.source.right).1 z)
        (SharedRefutationCircuit.productSum (inputRows rows) code z)
    rw [ih]

private theorem evaluatedRows_guard {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) :
    SharedRefutationAlgebra.guardValue (evaluatedRows rows tail code s z) =
      qEval (scalar (sourceFamily rows)) (s, z) := by
  induction rows with
  | nil =>
    simp only [evaluatedRows, List.map_nil, SharedRefutationAlgebra.guardValue, SharedRefutationAlgebra.rowSum,
      sourceFamily, scalar, qOfAffine_eval, aConst_eval]
  | cons r rows ih =>
    change Bool.xor (r.source.selected && r.source.eval (s, z))
        (SharedRefutationAlgebra.guardValue (evaluatedRows rows tail code s z)) =
      qEval (scalar (r.source :: sourceFamily rows)) (s, z)
    rw [ih]
    cases selected : r.source.selected <;>
      simp only [scalar, selected, Bool.false_eq_true, ↓reduceIte,
        qAdd_eval, qProduct_eval, Row.eval, Bool.false_and, Bool.true_and, Bool.false_xor]

private theorem compiled_outputs {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (compiled : SharedRefutationCircuit.compileChecked (inputRows rows) code = some result)
    (s : Bool) (z : Point n) :
    SharedRefutationCircuit.outputs result.1 z result.2 =
      (evaluatedRows rows tail code s z).map
        (SharedRefutationAlgebra.liftedMultiplier (evaluatedRows rows tail code s z)) := by
  rw [SharedRefutationCircuit.compileChecked_outputs (inputRows rows) code result compiled z]
  change (inputRows rows).map (fun r => Bool.xor (SharedRefutationCircuit.value code z r.root)
      (r.coefficient && SharedRefutationCircuit.productSum (inputRows rows) code z)) =
    (evaluatedRows rows tail code s z).map (fun r => Bool.xor r.multiplier
      (r.weight && SharedRefutationAlgebra.correctionValue (evaluatedRows rows tail code s z)))
  rw [evaluatedRows_correction]
  simp only [inputRows, evaluatedRows, List.map_map, Function.comp_def, inputRow, evaluatedRow]

private theorem originalSum_eq {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (compiled : SharedRefutationCircuit.compileChecked (inputRows rows) code = some result)
    (s : Bool) (z : Point n) :
    originalSum rows result.1 result.2 s z =
      some (SharedRefutationAlgebra.liftedValue (evaluatedRows rows tail code s z)) := by
  unfold originalSum
  rw [compiled_outputs rows tail code result compiled s z,
    ← evaluatedRows_sources rows tail code s z]
  exact pairedSum_rowSum (evaluatedRows rows tail code s z)
    (SharedRefutationAlgebra.liftedMultiplier (evaluatedRows rows tail code s z)) (fun r => r.source)

private theorem residualSum_eq {n : Nat} (rows : List (HeadRow n))
    (tail : Quadratic n) (code : SharedRefutationCircuit.Code n) (s : Bool) (z : Point n) :
    residualSum rows tail code z =
      some (SharedRefutationAlgebra.restrictedValue (evaluatedRows rows tail code s z)) := by
  unfold residualSum
  rw [← evaluatedRows_multipliers rows tail code s z,
    ← evaluatedRows_restricted rows tail code s z]
  exact pairedSum_rowSum (evaluatedRows rows tail code s z)
    (fun r => r.multiplier) (fun r => r.restricted)

/-- The checked source guard makes the compiled coefficient update preserve
the whole scalar identity, at every original head bit and remaining point. -/
theorem liftChecked_sum {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (checked : liftChecked rows tail oldCode = some result) (s : Bool) (z : Point n) :
    originalSum rows result.1 result.2 s z = residualSum rows tail oldCode z := by
  obtain ⟨guard, compiled⟩ := liftChecked_checks rows tail oldCode result checked
  have guardValue : SharedRefutationAlgebra.guardValue (evaluatedRows rows tail oldCode s z) =
      Bool.xor s (qEval tail z) := by
    rw [evaluatedRows_guard, guard]
    simp only [guardPolynomial, qEval, aConst_eval, Bool.true_and]
  have quotients : ∀ r ∈ evaluatedRows rows tail oldCode s z,
      r.source = Bool.xor r.restricted ((Bool.xor s (qEval tail z)) && r.quotient) := by
    intro r hr
    obtain ⟨head, _, rfl⟩ := List.mem_map.mp hr
    simpa only [evaluatedRow, qProduct_eval, Row.eval] using
      SharedRefutationAlgebra.quadratic_head_quotient
        (qProduct head.source.left head.source.right) s (qEval tail z) z
  rw [originalSum_eq rows tail oldCode result compiled s z,
    residualSum_eq rows tail oldCode s z]
  exact congrArg (fun b : Bool => some b)
    (SharedRefutationAlgebra.refutation_lift_sum (evaluatedRows rows tail oldCode s z)
      (Bool.xor s (qEval tail z)) guardValue quotients)

/-- This preserves an actual old refutation invariant; it does not supply or
discover that invariant and has no completeness conclusion. -/
theorem liftChecked_refutes {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (checked : liftChecked rows tail oldCode = some result)
    (oldInvariant : ∀ z, residualSum rows tail oldCode z = some true) :
    ∀ s z, originalSum rows result.1 result.2 s z = some true := by
  intro s z
  exact (liftChecked_sum rows tail oldCode result checked s z).trans (oldInvariant z)

private theorem model_cons_parts : ∀ a b : Bool,
    ((!a) && b) = true → a = false ∧ b = true := by decide

private theorem models_rows_false {n : Nat} (rs : Family n) (x : Point n) :
    models rs x = true → ∀ r ∈ rs, r.eval x = false := by
  induction rs with
  | nil =>
    intro _ r hr
    cases hr
  | cons r rs ih =>
    intro model
    obtain ⟨head, tail⟩ := model_cons_parts (r.eval x) (models rs x) model
    intro row member
    rcases List.mem_cons.mp member with equal | member
    · subst row
      exact head
    · exact ih tail row member

private theorem originalValues_zero_of_models {n : Nat} (rows : List (HeadRow n))
    (s : Bool) (z : Point n) (model : models (sourceFamily rows) (s, z) = true) :
    ∀ b ∈ originalValues rows s z, b = false := by
  intro b member
  change b ∈ rows.map (fun r => r.source.eval (s, z)) at member
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
  exact models_rows_false (sourceFamily rows) (s, z) model row.source
    (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

/-- A checked lift of an actual residual refutation rules out every model of
the original source family. No coefficient/value length equality is assumed. -/
theorem liftChecked_unsatisfiable {n : Nat} (rows : List (HeadRow n)) (tail : Quadratic n)
    (oldCode : SharedRefutationCircuit.Code n) (result : SharedRefutationCircuit.Code n × List Nat)
    (checked : liftChecked rows tail oldCode = some result)
    (oldInvariant : ∀ z, residualSum rows tail oldCode z = some true) :
    ¬ ∃ x : Point (n + 1), models (sourceFamily rows) x = true := by
  rintro ⟨⟨s, z⟩, model⟩
  have one := liftChecked_refutes rows tail oldCode result checked oldInvariant s z
  exact pairedSum_ne_true_of_zero
    (SharedRefutationCircuit.outputs result.1 z result.2)
    (originalValues rows s z) (originalValues_zero_of_models rows s z model) one

end PNP.Concrete.ResidualReduction.SharedRefutationSourceLift
