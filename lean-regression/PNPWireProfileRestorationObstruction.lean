import PNP

namespace PNP.DirectWire.WireProfileRestorationObstruction

open WireProfile WireProfileRestoration

private def tripleNotProgram : Program 1 3 :=
  .snoc
    (.snoc (.snoc .empty ⟨.input 0, .input 0⟩)
      ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩)
    ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩

private def tripleNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord tripleNotProgram ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨2, by decide⟩ }

private def singleNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.snoc .empty ⟨.input 0, .input 0⟩)
        ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private theorem one_gate_full_realization : FullEquivalent tripleNot singleNot :=
  equivalentBool_sound (by decide)

theorem positive_full_slack : 0 < fullSlack tripleNot := by
  have lower := full_candidate_lower_bound tripleNot singleNot one_gate_full_realization
  change fullMinimum tripleNot ≤ 1 at lower
  unfold fullSlack
  change 0 < 3 - fullMinimum tripleNot
  omega

/-- Structural quiescence is not a semantic optimum: the paid hidden program
still contains three successive negations, equivalent to one negation. -/
theorem computed_restoration_refuses :
    (checkedGain tripleNot (fun _ => false)).isSome = false := by
  decide +kernel

theorem positive_slack_does_not_force_restoration_gain :
    ¬ (∀ (carrier : WireCarrier 1 1 1) (keep : Fin 1 → Bool),
      0 < fullSlack carrier → (checkedGain carrier keep).isSome = true) := by
  intro complete
  have accepted := complete tripleNot (fun _ => false) positive_full_slack
  rw [computed_restoration_refuses] at accepted
  cases accepted

#print axioms positive_full_slack
#print axioms computed_restoration_refuses
#print axioms positive_slack_does_not_force_restoration_gain


/-- The counterexample limits restoration alone. The existing general unary
constructor already gives a smaller full word; no new special-case optimizer
is needed to handle these three gates. -/
theorem existing_unary_route_recovers :
    FullEquivalent tripleNot (WireUnaryRealization.realize tripleNot) ∧
      (WireUnaryRealization.realize tripleNot).implementation.gateCount <
        tripleNot.implementation.gateCount :=
  ⟨WireUnaryRealization.realize_full_equivalent tripleNot,
    (unary_smaller_iff_fullSlack_positive tripleNot).2 positive_full_slack⟩

#print axioms existing_unary_route_recovers

end PNP.DirectWire.WireProfileRestorationObstruction
