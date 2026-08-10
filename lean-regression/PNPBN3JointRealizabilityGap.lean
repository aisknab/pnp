/-
Copyright (c) 2026 PNP Labs.

Minimal logical boundary for the pinned manuscript's BN3 simultaneous-envelope
step.  Per-cut side-tight realizability does not, by itself, construct a
cross-cut-stable family of realizing bases.  This is a missing-premise witness,
not a counterexample to a future candidate-derived BN3 theorem.
-/

import PNP.ResidualTerminalBN2SquareLegitimacy

namespace PNP.DirectWire.BN3Gap

/-- Every cut has at least one realizing basis. -/
def PerCutRealizable {Cut Basis : Type}
    (realizes : Cut → Basis → Prop) : Prop :=
  ∀ cut, ∃ basis, realizes cut basis

/-- A realizing basis can be chosen for every cut while satisfying one
    cross-cut stability predicate. -/
def StableRealizingFamily {Cut Basis : Type}
    (realizes : Cut → Basis → Prop)
    (stable : (Cut → Basis) → Prop) : Prop :=
  ∃ choose, (∀ cut, realizes cut (choose cut)) ∧ stable choose

/-- The smallest two-cut relation in which each cut forces a different basis. -/
def twoCutRealizes (cut basis : Bool) : Prop := basis = cut

/-- The cross-cut key is stable only when both selected bases agree. -/
def constantAcrossCuts (choose : Bool → Bool) : Prop :=
  choose false = choose true

/-- Each cut in the countermodel has a side-tight analogue. -/
theorem twoCut_perCutRealizable : PerCutRealizable twoCutRealizes := by
  intro cut
  exact ⟨cut, rfl⟩

/-- No realizing selection for the two cuts is cross-cut stable. -/
theorem twoCut_noStableRealizingFamily :
    ¬StableRealizingFamily twoCutRealizes constantAcrossCuts := by
  rintro ⟨choose, realizes, stable⟩
  have falseBasis : choose false = false := realizes false
  have trueBasis : choose true = true := realizes true
  unfold constantAcrossCuts at stable
  rw [falseBasis, trueBasis] at stable
  exact Bool.noConfusion stable

/-- Consequently there is no theorem of pure logic promoting arbitrary
    per-cut witnesses to a stable joint family.  A BN3 proof must supply an
    additional candidate-derived coherence construction. -/
theorem perCutRealizable_not_uniformly_sufficient :
    ¬(∀ (Cut Basis : Type)
        (realizes : Cut → Basis → Prop)
        (stable : (Cut → Basis) → Prop),
      PerCutRealizable realizes → StableRealizingFamily realizes stable) := by
  intro promote
  exact twoCut_noStableRealizingFamily
    (promote Bool Bool twoCutRealizes constantAcrossCuts
      twoCut_perCutRealizable)

#print axioms twoCut_perCutRealizable
#print axioms twoCut_noStableRealizingFamily
#print axioms perCutRealizable_not_uniformly_sufficient

end PNP.DirectWire.BN3Gap
