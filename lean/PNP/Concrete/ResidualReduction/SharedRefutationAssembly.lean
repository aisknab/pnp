import PNP.Concrete.ResidualReduction.SharedRefutationGlobalStep
import PNP.Concrete.ResidualReduction.SharedRefutationSourceLift
import PNP.Concrete.ResidualReduction.SharedRefutationTransport

/-! Assemble a checked coefficient lift for an actual saved source step.
Row/root attachment rejects both length mismatches. This is not a new selector:
it uses the source step already returned by the existing reduction. -/

namespace PNP.Concrete.ResidualReduction.SharedRefutationAssembly
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SharedRefutationCircuit
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

abbrev Certificate (n : Nat) := Code n × List Nat

def WellFormed {n : Nat} (F : Family n) (p : Certificate n) : Prop :=
  codeValid p.1 = true ∧ (∀ i ∈ p.2, i < p.1.length) ∧ p.2.length = F.length

def Refutes {n : Nat} (F : Family n) (p : Certificate n) : Prop :=
  ∀ x, SharedRefutationSourceLift.pairedSum (outputs p.1 x p.2)
    (F.map (fun r => r.eval x)) = some true

def attach {n : Nat} : Family (n + 1) → List Nat →
    Option (List (SharedRefutationSourceLift.HeadRow n))
  | [], [] => some []
  | r :: rs, i :: is => (attach rs is).map (fun rows => ⟨r, i⟩ :: rows)
  | _, _ => none

theorem attach_contract {n : Nat} (F : Family (n + 1)) (roots : List Nat)
    (rows : List (SharedRefutationSourceLift.HeadRow n))
    (checked : attach F roots = some rows) :
    SharedRefutationSourceLift.sourceFamily rows = F ∧
      SharedRefutationSourceLift.oldRoots rows = roots := by
  induction F generalizing roots rows with
  | nil =>
    cases roots with
    | nil =>
      have same : [] = rows := by
        simpa only [attach, Option.some.injEq] using checked
      cases same
      exact ⟨rfl, rfl⟩
    | cons i is => simp only [attach, reduceCtorEq] at checked
  | cons r rs ih =>
    cases roots with
    | nil => simp only [attach, reduceCtorEq] at checked
    | cons i is =>
      cases tail : attach rs is with
      | none => simp only [attach, tail, Option.map, reduceCtorEq] at checked
      | some rest =>
        have same : (⟨r, i⟩ : SharedRefutationSourceLift.HeadRow n) :: rest = rows := by
          simpa only [attach, tail, Option.map, Option.some.injEq] using checked
        cases same
        obtain ⟨sources, indices⟩ := ih is rest tail
        constructor
        · change r :: SharedRefutationSourceLift.sourceFamily rest = r :: rs
          rw [sources]
        · change i :: SharedRefutationSourceLift.oldRoots rest = i :: is
          rw [indices]

theorem attach_exists {n : Nat} (F : Family (n + 1)) (roots : List Nat)
    (count : roots.length = F.length) :
    ∃ rows, attach F roots = some rows := by
  induction F generalizing roots with
  | nil =>
    cases roots with
    | nil => exact ⟨[], rfl⟩
    | cons i is => cases count
  | cons r rs ih =>
    cases roots with
    | nil => cases count
    | cons i is =>
      have tailCount : is.length = rs.length := Nat.succ.inj count
      obtain ⟨rows, checked⟩ := ih is tailCount
      exact ⟨⟨r, i⟩ :: rows, by simp only [attach, checked, Option.map]⟩

private theorem bounded_all {n : Nat} (rows : List (InputRow n)) (code : Code n)
    (bounds : RootsBounded rows code) :
    rows.all (fun r => decide (r.root < code.length)) = true := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have head : r.root < code.length := bounds r List.mem_cons_self
    have tail := ih (fun t ht => bounds t (List.mem_cons_of_mem r ht))
    simp [head, tail]

def liftRecorded {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length)
    (p : Certificate n) : Option (Certificate (n + 1)) :=
  (attach (SharedRefutationGlobalStep.charted F s) p.2).bind (fun rows =>
    (SharedRefutationSourceLift.liftChecked rows
      (SharedRefutationGlobalStep.tailPolynomial F s) p.1).map (fun q =>
        (SharedRefutationTransport.chartCode s.pivot s.tail q.1, q.2)))

/-- A valid source-generated step always admits this mechanical lift of a
well-formed old certificate. The logical refutation implication is separate
from graph validity, so a well-formed graph alone is never claimed to refute. -/
theorem liftRecorded_exists {n : Nat} (F : Family (n + 1))
    (s : ConstructedStep n F.length) (selected : globalStep F = some s)
    (p : Certificate n) (wellFormed : WellFormed s.output p) :
    ∃ q, liftRecorded F s p = some q ∧ WellFormed F q ∧
      (Refutes s.output p → Refutes F q) ∧
      q.1.length ≤ p.1.length + 4 * F.length + 1 := by
  have stepCount := (globalStep_sound F s selected).1
  have rootCount : p.2.length = (SharedRefutationGlobalStep.charted F s).length := by
    rw [SharedRefutationGlobalStep.charted_length]
    exact wellFormed.2.2.trans stepCount
  obtain ⟨rows, attached⟩ := attach_exists (SharedRefutationGlobalStep.charted F s) p.2 rootCount
  obtain ⟨sources, roots⟩ := attach_contract _ _ rows attached
  have rowCount : rows.length = F.length := by
    have h := congrArg List.length sources
    simpa only [SharedRefutationSourceLift.sourceFamily, List.length_map,
      SharedRefutationGlobalStep.charted_length] using h
  have bounds : RootsBounded (SharedRefutationSourceLift.inputRows rows) p.1 := by
    intro input member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    change row.root < p.1.length
    apply wellFormed.2.1
    rw [← roots]
    exact List.mem_map.mpr ⟨row, rowMember, rfl⟩
  let raw := compile (SharedRefutationSourceLift.inputRows rows) p.1
  have compiled : compileChecked (SharedRefutationSourceLift.inputRows rows) p.1 = some raw := by
    simp only [compileChecked, wellFormed.1, bounded_all _ _ bounds, Bool.true_and, ↓reduceIte]
    rfl
  have guard : qEq (scalar (SharedRefutationSourceLift.sourceFamily rows))
      (SharedRefutationSourceLift.guardPolynomial
        (SharedRefutationGlobalStep.tailPolynomial F s)) = true := by
    apply (qEq_true_iff _ _).mpr
    rw [sources]
    exact SharedRefutationGlobalStep.globalStep_guard F s selected
  have lifted : SharedRefutationSourceLift.liftChecked rows
      (SharedRefutationGlobalStep.tailPolynomial F s) p.1 = some raw := by
    simp only [SharedRefutationSourceLift.liftChecked, guard, ↓reduceIte, compiled]
  let q : Certificate (n + 1) :=
    (SharedRefutationTransport.chartCode s.pivot s.tail raw.1, raw.2)
  obtain ⟨_, _, valid, range, count⟩ := SharedRefutationSourceLift.liftChecked_contract
    rows (SharedRefutationGlobalStep.tailPolynomial F s) p.1 raw lifted
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · simp only [liftRecorded, attached, Option.bind, lifted, Option.map]
    rfl
  · refine ⟨?_, ?_, count.trans rowCount⟩
    · exact (SharedRefutationTransport.chartCode_valid s.pivot s.tail raw.1).trans valid
    · intro i member
      simpa only [q, SharedRefutationTransport.chartCode_length] using range i member
  · intro oldRefutation x
    have residual : ∀ z, SharedRefutationSourceLift.residualSum rows
        (SharedRefutationGlobalStep.tailPolynomial F s) p.1 z = some true := by
      intro z
      have values : SharedRefutationSourceLift.restrictedValues rows
          (SharedRefutationGlobalStep.tailPolynomial F s) z =
          s.output.map (fun r => r.eval z) := by
        calc
          _ = (SharedRefutationSourceLift.sourceFamily rows).map
              (fun r => r.eval (qEval (SharedRefutationGlobalStep.tailPolynomial F s) z, z)) := by
                simp only [SharedRefutationSourceLift.restrictedValues,
                  SharedRefutationSourceLift.sourceFamily, List.map_map, Function.comp_def]
          _ = _ := by rw [sources, ← SharedRefutationGlobalStep.globalStep_values F s selected z]
      unfold SharedRefutationSourceLift.residualSum
      rw [roots, values]
      exact oldRefutation z
    have one := SharedRefutationSourceLift.liftChecked_refutes rows
      (SharedRefutationGlobalStep.tailPolynomial F s) p.1 raw lifted residual
      (chart s.pivot s.tail x).1 (chart s.pivot s.tail x).2
    have originals : SharedRefutationSourceLift.originalValues rows
        (chart s.pivot s.tail x).1 (chart s.pivot s.tail x).2 =
        F.map (fun r => r.eval x) := by
      calc
        _ = (SharedRefutationSourceLift.sourceFamily rows).map
            (fun r => r.eval (chart s.pivot s.tail x)) := by
              simp only [SharedRefutationSourceLift.originalValues,
                SharedRefutationSourceLift.sourceFamily, List.map_map, Function.comp_def]
              rfl
        _ = _ := by rw [sources, SharedRefutationGlobalStep.charted_values]
    unfold SharedRefutationSourceLift.originalSum at one
    rw [originals] at one
    change SharedRefutationSourceLift.pairedSum
      (outputs (SharedRefutationTransport.chartCode s.pivot s.tail raw.1) x raw.2)
      (F.map (fun r => r.eval x)) = some true
    rw [SharedRefutationTransport.chartCode_outputs]
    exact one
  · have growth := SharedRefutationSourceLift.liftChecked_growth rows
      (SharedRefutationGlobalStep.tailPolynomial F s) p.1 raw lifted
    simpa only [q, SharedRefutationTransport.chartCode_length, rowCount] using growth

end PNP.Concrete.ResidualReduction.SharedRefutationAssembly
