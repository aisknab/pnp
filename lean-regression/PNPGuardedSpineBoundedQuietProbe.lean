import PNP

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.GuardedSpineBoundedQuietProbe
open GuardedSpineFamily (candidate shorter)
open GuardedSpineBoundedQuiet
open BoundedWindowSchedule (BoundedQuiet scan windowsFrom)

theorem general_proper_count {width : Nat} (n : Nat)
    (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 width))
    (small : (extractTerminalSupport (candidate n) records).gateCount < n + 2) :
    ∃ node, terminalGateSelected records node = false :=
  proper_of_small_support n records small

theorem all_records_bounded_quiet (n limit : Nat) (below : limit < n + 2) :
    ∀ (width : Nat) (records : List (TerminalPrimitiveRecord (n + 1) (n + 2) 1 width)),
      (extractTerminalSupport (candidate n) records).gateCount ≤ limit →
        ∀ offered, ¬ PhysicalWindowSearch.Valid (candidate n) records offered :=
  bounded_quiet n limit below

theorem actual_schedule_none (n limit : Nat) (below : limit < n + 2) :
    scan (candidate n) (windowsFrom (n + 2) limit 0) = none :=
  scan_none n limit below

theorem every_cap_strict_counterexample (limit : Nat) :
    BoundedQuiet (candidate (limit + 2)) limit ∧
      StrictEquivalentGain (candidate (limit + 2)).toImplementation (shorter limit).toImplementation ∧
      0 < residualSlack (candidate (limit + 2)).toImplementation :=
  quiet_with_strict_gain limit

theorem every_cap_nonminimum_exists (limit : Nat) :
    ∃ source : Candidate (limit + 3) (limit + 4) 1,
      BoundedQuiet source limit ∧ 0 < residualSlack source.toImplementation :=
  quiet_nonminimum_exists limit

theorem no_uniform_cap :
    ¬ ∃ limit : Nat, ∀ (inputs gates outputs : Nat) (source : Candidate inputs gates outputs),
      BoundedQuiet source limit → residualSlack source.toImplementation = 0 :=
  no_uniform_zero_slack_limit

theorem zero_cap_counterexample :
    BoundedQuiet (candidate 2) 0 ∧
      StrictEquivalentGain (candidate 2).toImplementation (shorter 0).toImplementation ∧
      0 < residualSlack (candidate 2).toImplementation :=
  quiet_with_strict_gain 0

theorem disconnected_support_cap
    (offered : PhysicalWindowSearch.Offered (candidate 3)
      ([.gate 0,.gate 2,.gate 4] : List (TerminalPrimitiveRecord 4 5 1 0))) :
    ¬ PhysicalWindowSearch.Valid (candidate 3)
      ([.gate 0,.gate 2,.gate 4] : List (TerminalPrimitiveRecord 4 5 1 0)) offered := by
  exact bounded_quiet 3 3 (by decide) 0 _ (by decide +kernel) offered

end PNP.DirectWire.GuardedSpineBoundedQuietProbe

#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.general_proper_count
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.all_records_bounded_quiet
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.actual_schedule_none
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.every_cap_strict_counterexample
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.every_cap_nonminimum_exists
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.no_uniform_cap
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.zero_cap_counterexample
#print axioms PNP.DirectWire.GuardedSpineBoundedQuietProbe.disconnected_support_cap
