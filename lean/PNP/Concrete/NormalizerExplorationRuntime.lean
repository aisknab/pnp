/-
Copyright (c) 2026 PNP Labs.

Whole exploration runtime, not merely per-call complexity. One fixed
polynomial bound covers every growing trace and shrinking unseen list,
including malformed formula and matching bytes. Early failure stops the
machine rather than requiring a well-formedness premise.
-/

import PNP.Concrete.NormalizerExplorationBounds

namespace PNP.Concrete.NormalizerBlocks.Exploration

theorem scan_fuel_bound (fuel formula matching limit : Nat)
    (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State)
    (data : Within limit unseen trace r)
    (formulaSize : r.core.parent.graph.core.formula.length ≤ formula)
    (matchingSize : r.core.parent.graph.core.matching.length ≤ matching) :
    (scan fuel r).fuel ≤ (workBound formula matching limit + 1) * fuel + 1 := by
  induction fuel generalizing r unseen trace with
  | zero => simp only [scan, Nat.mul_zero]; exact Nat.le_refl _
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simp only [scan, remaining]; omega
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          have first := bodyFuel_bound formula matching limit unseen trace r data formulaSize matchingSize
          have tailBound : (scan fuel (bodyResult r)).fuel ≤
              (workBound formula matching limit + 1) * fuel + 1 := by
            cases within_step limit unseen trace r data nonempty with
            | inl stopped =>
                rw [scan_empty fuel (bodyResult r) stopped]
                change 1 ≤ (workBound formula matching limit + 1) * fuel + 1
                omega
            | inr continuing =>
                obtain ⟨nextUnseen, nextTrace, nextData⟩ := continuing
                have stable := body_preserves r
                exact ih nextUnseen nextTrace (bodyResult r) nextData
                  (by rw [stable.1]; exact formulaSize) (by rw [stable.2]; exact matchingSize)
          simp only [scan, remaining, Nat.mul_succ]
          omega

theorem whole_fuel_bound (formula matching limit : Nat)
    (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State)
    (data : Within limit unseen trace r)
    (formulaSize : r.core.parent.graph.core.formula.length ≤ formula)
    (matchingSize : r.core.parent.graph.core.matching.length ≤ matching) :
    (whole r).fuel ≤ (workBound formula matching limit + 1) * (limit + 1) + 1 := by
  have checked := scan_fuel_bound (r.remaining.length + 1) formula matching limit
    unseen trace r data formulaSize matchingSize
  have budget : r.remaining.length ≤ limit := by have h := data.traceBudget; omega
  exact Nat.le_trans checked
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right budget 1)) 1)

end PNP.Concrete.NormalizerBlocks.Exploration
