/-
Copyright (c) 2026 PNP Labs.

A finite syntactic dependency test is exact for every natural-valued input
labelling. Singleton labels read the actual NAND wiring, including dependencies
that cancel semantically. They are not Boolean-equivalence certificates.

This decides a structural guard. It does not establish complete normalization,
global discovery, all manuscript profiles, or polynomial encoded execution.
-/

import PNP.NANDWireCausalBounds

namespace PNP.DirectWire.CausalBound

def singletonLabel {inputs : Nat} (selected : Fin inputs) : Fin inputs → Nat :=
  fun input => if selected = input then 1 else 0

private theorem source_bounded_iff_aux {inputs gates : Nat}
    (wire : Source inputs gates) (labels : Fin inputs → Nat)
    (actual : Fin gates → Nat) (singletons : Fin inputs → Fin gates → Nat)
    (gateBound : ∀ gate cap, actual gate ≤ cap ↔
      ∀ input, 0 < singletons input gate → labels input ≤ cap)
    (cap : Nat) :
    source wire labels actual ≤ cap ↔
      ∀ input, 0 < source wire (singletonLabel input) (singletons input) →
        labels input ≤ cap := by
  cases wire with
  | input index =>
      change labels index ≤ cap ↔
        ∀ input, 0 < singletonLabel input index → labels input ≤ cap
      constructor
      · intro bounded input present
        by_cases same : input = index
        · cases same
          exact bounded
        · have absent : singletonLabel input index = 0 := if_neg same
          rw [absent] at present
          omega
      · intro bounded
        apply bounded index
        change 0 < (if index = index then 1 else 0)
        rw [if_pos rfl]
        exact Nat.zero_lt_one
  | constant value =>
      constructor
      · intro _bounded input impossible
        exact False.elim (Nat.not_lt_zero 0 impossible)
      · intro _bounded
        exact Nat.zero_le cap
  | gate index => exact gateBound index cap

/-- Singleton dependencies characterize every upper bound, not just a sample. -/
theorem levels_bounded_iff {inputs gates : Nat}
    (program : Program inputs gates) (labels : Fin inputs → Nat) :
    ∀ (gate : Fin gates) (cap : Nat),
      levels program labels gate ≤ cap ↔
        ∀ input, 0 < levels program (singletonLabel input) gate →
          labels input ≤ cap := by
  induction program with
  | empty =>
      intro gate _cap
      exact Fin.elim0 gate
  | @snoc gates initial next ih =>
      intro gate cap
      rcases index_cases gate with ⟨earlier, rfl⟩ | rfl
      · simpa only [levels_snoc_castSucc] using ih earlier cap
      · simp only [levels_snoc_last]
        have leftBound := source_bounded_iff_aux next.left labels
          (levels initial labels) (fun input => levels initial (singletonLabel input)) ih cap
        have rightBound := source_bounded_iff_aux next.right labels
          (levels initial labels) (fun input => levels initial (singletonLabel input)) ih cap
        constructor
        · intro bounded input present
          have leftCap : source next.left labels (levels initial labels) ≤ cap :=
            Nat.le_trans (Nat.le_max_left _ _) bounded
          have rightCap : source next.right labels (levels initial labels) ≤ cap :=
            Nat.le_trans (Nat.le_max_right _ _) bounded
          have reaches :
              0 < source next.left (singletonLabel input)
                (levels initial (singletonLabel input)) ∨
              0 < source next.right (singletonLabel input)
                (levels initial (singletonLabel input)) := by omega
          rcases reaches with left | right
          · exact leftBound.1 leftCap input left
          · exact rightBound.1 rightCap input right
        · intro bounded
          have leftCap : source next.left labels (levels initial labels) ≤ cap :=
            leftBound.2 (fun input present =>
              bounded input (Nat.lt_of_lt_of_le present (Nat.le_max_left _ _)))
          have rightCap : source next.right labels (levels initial labels) ≤ cap :=
            rightBound.2 (fun input present =>
              bounded input (Nat.lt_of_lt_of_le present (Nat.le_max_right _ _)))
          omega

theorem source_bounded_iff {inputs gates : Nat}
    (program : Program inputs gates) (wire : Source inputs gates)
    (labels : Fin inputs → Nat) (cap : Nat) :
    source wire labels (levels program labels) ≤ cap ↔
      ∀ input, 0 < source wire (singletonLabel input)
        (levels program (singletonLabel input)) → labels input ≤ cap :=
  source_bounded_iff_aux wire labels (levels program labels)
    (fun input => levels program (singletonLabel input))
    (levels_bounded_iff program labels) cap

/-- No input may acquire a new physical path to the compared source. -/
def sourceDependencyGuard {inputs beforeGates afterGates : Nat}
    (before : Program inputs beforeGates) (beforeWire : Source inputs beforeGates)
    (after : Program inputs afterGates) (afterWire : Source inputs afterGates) : Bool :=
  (allFin inputs).all fun input => decide
    (0 < source afterWire (singletonLabel input) (levels after (singletonLabel input)) →
      0 < source beforeWire (singletonLabel input) (levels before (singletonLabel input)))

theorem sourceDependencyGuard_iff {inputs beforeGates afterGates : Nat}
    (before : Program inputs beforeGates) (beforeWire : Source inputs beforeGates)
    (after : Program inputs afterGates) (afterWire : Source inputs afterGates) :
    sourceDependencyGuard before beforeWire after afterWire = true ↔
      ∀ labels, source afterWire labels (levels after labels) ≤
        source beforeWire labels (levels before labels) := by
  constructor
  · intro checked labels
    apply (source_bounded_iff after afterWire labels _).2
    intro input present
    have row := (List.all_eq_true.mp checked) input (mem_allFin input)
    have earlier := (of_decide_eq_true row) present
    exact ((source_bounded_iff before beforeWire labels _).1 (Nat.le_refl _))
      input earlier
  · intro bounded
    apply List.all_eq_true.mpr
    intro input _member
    have valid :
        0 < source afterWire (singletonLabel input) (levels after (singletonLabel input)) →
          0 < source beforeWire (singletonLabel input) (levels before (singletonLabel input)) :=
      fun present => Nat.lt_of_lt_of_le present (bounded (singletonLabel input))
    simpa only [decide_eq_true_eq] using valid

/-- Compare each ordered output separately, including zero-output words. -/
def candidateDependencyGuard {inputs beforeGates afterGates outputs : Nat}
    (before : Candidate inputs beforeGates outputs)
    (after : Candidate inputs afterGates outputs) : Bool :=
  (allFin outputs).all fun output =>
    sourceDependencyGuard before.program (before.directWireWord.source output)
      after.program (after.directWireWord.source output)

theorem candidateDependencyGuard_iff {inputs beforeGates afterGates outputs : Nat}
    (before : Candidate inputs beforeGates outputs)
    (after : Candidate inputs afterGates outputs) :
    candidateDependencyGuard before after = true ↔
      ∀ labels output, outputLevel after labels output ≤ outputLevel before labels output := by
  constructor
  · intro checked labels output
    have row := (List.all_eq_true.mp checked) output (mem_allFin output)
    exact (sourceDependencyGuard_iff _ _ _ _).1 row labels
  · intro bounded
    apply List.all_eq_true.mpr
    intro output _member
    apply (sourceDependencyGuard_iff _ _ _ _).2
    intro labels
    exact bounded labels output

end PNP.DirectWire.CausalBound

namespace PNP.DirectWire.WireCarrier

variable {inputs outputs fields : Nat}

/-- Check every ordinary output and every hidden computational field. -/
def dependencyGuard (before after : WireCarrier inputs outputs fields) : Bool :=
  CausalBound.candidateDependencyGuard before.exposed.candidate after.exposed.candidate

theorem dependencyGuard_iff (before after : WireCarrier inputs outputs fields) :
    dependencyGuard before after = true ↔
      ∀ labels, after.CausalBounds labels
        (CausalBound.outputLevel before.implementation.candidate labels)
        (before.fieldLevel labels) := by
  constructor
  · intro checked labels
    have bounded := (CausalBound.candidateDependencyGuard_iff _ _).1 checked labels
    constructor
    · intro output
      simpa only [exposed_output_level] using bounded (Fin.castAdd fields output)
    · intro field
      simpa only [exposed_field_level] using bounded (Fin.natAdd outputs field)
  · intro bounded
    apply (CausalBound.candidateDependencyGuard_iff _ _).2
    intro labels observation
    rcases finSum_decompose observation with ⟨output, rfl⟩ | ⟨field, rfl⟩
    · simpa only [exposed_output_level] using (bounded labels).1 output
    · simpa only [exposed_field_level] using (bounded labels).2 field

end PNP.DirectWire.WireCarrier
