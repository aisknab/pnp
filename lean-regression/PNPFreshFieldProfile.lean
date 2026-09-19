import PNP

namespace PNP.DirectWire.FreshFieldProfileRegression

open FreshNandCost

example {inputs outputs : Nat} (target : Implementation inputs outputs) (extra : Nat) :
    referenceMinimum (padInputs target extra) = referenceMinimum target :=
  referenceMinimum_padInputs target extra

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.fullMinimum (profile target width) = referenceMinimum target + width :=
  profile_fullMinimum target width

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.quotientMinimum (profile target width) (fun _ => false) = referenceMinimum target :=
  profile_quotientMinimum target width

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.projectionDefect (profile target width) (fun _ => false) = width :=
  profile_projectionDefect target width

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    WireProfile.fullSlack (profile target width) = target.gateCount - referenceMinimum target :=
  profile_fullSlack target width

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    width ≤ WireQuotientLift.charge (profile target width) (fun _ => false) :=
  profile_materializer_charge_lower_bound target width

private def bit : Fin 1 := ⟨0, by decide⟩
private def first : Fin 2 := ⟨0, by decide⟩
private def second : Fin 2 := ⟨1, by decide⟩
private def freeCandidate : Candidate 1 0 2 :=
  Candidate.ofDirectWireWord .empty
    ⟨fun output => if output.val = 0 then .input bit else .constant true⟩
private def free : Implementation 1 2 := freeCandidate.toImplementation

theorem free_minimum : referenceMinimum free = 0 :=
  Nat.eq_zero_of_le_zero (referenceMinimum_le_target free)

theorem full_cost_exact (width : Nat) : WireProfile.fullMinimum (profile free width) = width := by
  rw [profile_fullMinimum, free_minimum, Nat.zero_add]

theorem quotient_cost_zero (width : Nat) :
    WireProfile.quotientMinimum (profile free width) (fun _ => false) = 0 := by
  rw [profile_quotientMinimum, free_minimum]

theorem full_slack_zero (width : Nat) : WireProfile.fullSlack (profile free width) = 0 := by
  rw [profile_fullSlack]
  change 0 - referenceMinimum free = 0
  exact Nat.zero_sub _

theorem forgotten_slack_is_defect (width : Nat) :
    WireProfile.fullSlack (WireProfile.mask (profile free width) (fun _ => false)) = width := by
  rw [WireProfile.exposure_balance, full_slack_zero, profile_projectionDefect, Nat.zero_add]

theorem positive_defect_prevents_free_lift (width : Nat) (positive : 0 < width) :
    ¬ WireProfile.FullEquivalent (profile free width)
      (WireProfile.quotientWitness (profile free width) (fun _ => false)) := by
  apply WireProfile.quotient_minimum_cannot_lift_of_positive_defect
  rw [profile_projectionDefect]
  exact positive

private def current := profile free 2
private def keepFirst : Fin 2 → Bool := fun field => decide (field.val = 0)
private def empty : Implementation 0 0 :=
  (Candidate.ofDirectWireWord Program.empty ⟨Fin.elim0⟩).toImplementation

private def checks : List (String × Bool) :=
  [ ("actual physical carrier has two gates", decide (current.implementation.gateCount = 2))
  , ("fields select distinct actual gates", match current.source first, current.source second with
      | .gate left, .gate right => decide (left ≠ right)
      | _, _ => false)
  , ("ordinary outputs retain the old computation", allTrue (allBoolTuples 5) fun tuple =>
      allTrue (allFin 2) fun output => boolEqual
        (current.implementation.candidate.semantics tuple.toValuation output)
        (free.candidate.semantics (fun index => tuple.toValuation (Fin.castAdd 4 index)) output))
  , ("actual field values are independent NANDs", allTrue (allBoolTuples 5) fun tuple =>
      allTrue (allFin 2) fun field => boolEqual
        (current.fieldValue tuple.toValuation field) (freshValue tuple.toValuation field))
  , ("forgetting fields does not change ordinary outputs", equivalentBool
      (WireProfile.mask current (fun _ => false)).implementation.candidate
      current.implementation.candidate)
  , ("all forgotten field values become literal false", allTrue (allBoolTuples 5) fun tuple =>
      allTrue (allFin 2) fun field =>
        !((WireProfile.mask current (fun _ => false)).fieldValue tuple.toValuation field))
  , ("mixed mask preserves only the selected field", allTrue (allBoolTuples 5) fun tuple =>
      boolEqual ((WireProfile.mask current keepFirst).fieldValue tuple.toValuation first)
        (current.fieldValue tuple.toValuation first) &&
      !((WireProfile.mask current keepFirst).fieldValue tuple.toValuation second))
  , ("exposure recovers the exact combined computation",
      equivalentBool current.exposed.candidate (extend free 2).candidate)
  , ("input padding preserves old values across all extra valuations", allTrue (allBoolTuples 3) fun tuple =>
      allTrue (allFin 2) fun output => boolEqual
        ((padInputs free 2).candidate.semantics tuple.toValuation output)
        (free.candidate.semantics (fun index => tuple.toValuation (Fin.castAdd 2 index)) output))
  , ("empty profile has no gates", decide ((profile empty 0).implementation.gateCount = 0))
  ]

def run : IO Unit := do
  for (name, passed) in checks do
    if passed then IO.println ("fresh-profile-check-passed: " ++ name)
    else throw (IO.userError ("fresh-profile-check-failed: " ++ name))
  IO.println "fresh-profile-regressions-complete: 10 runtime checks; 6 independent general type contracts"

end PNP.DirectWire.FreshFieldProfileRegression

#print axioms PNP.DirectWire.FreshFieldProfileRegression.free_minimum
#print axioms PNP.DirectWire.FreshFieldProfileRegression.full_cost_exact
#print axioms PNP.DirectWire.FreshFieldProfileRegression.quotient_cost_zero
#print axioms PNP.DirectWire.FreshFieldProfileRegression.full_slack_zero
#print axioms PNP.DirectWire.FreshFieldProfileRegression.forgotten_slack_is_defect
#print axioms PNP.DirectWire.FreshFieldProfileRegression.positive_defect_prevents_free_lift

def main : IO Unit := PNP.DirectWire.FreshFieldProfileRegression.run
