import PNP.NANDWireProfileFieldClosed
import PNP.NANDFreshFieldProfile

/-!
Exact independent-field costs inside the computed terminal profile model.
These statements connect the model constructor to an explicit arbitrary-width
family; they do not identify arbitrary manuscript fields with fresh independent
inputs, supply a polynomial minimizer, or close global route obligations.
-/

namespace PNP.DirectWire.ComputedWireProfileCost

variable {inputs outputs : Nat}

theorem full_minimum (target : Implementation inputs outputs) (width : Nat)
    (keep : Fin width → Bool) :
    terminalFullProfileMinimum
      (WireProfileAmbient.model (FreshNandCost.profile target width) keep).profileSystem
      (FreshNandCost.profile target width).implementation =
        referenceMinimum target + width := by
  change terminalFullProfileMinimum
    (WireProfileAvailability.system (FreshNandCost.profile target width))
    (FreshNandCost.profile target width).implementation = _
  rw [WireProfileAvailability.full_minimum, FreshNandCost.profile_fullMinimum]

theorem quotient_minimum (target : Implementation inputs outputs) (width : Nat) :
    terminalQuotientProfileMinimum
      (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).profileSystem
      (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).projection
      (FreshNandCost.profile target width).implementation =
        referenceMinimum target := by
  change terminalQuotientProfileMinimum
    (WireProfileAvailability.system (FreshNandCost.profile target width))
    ⟨fun _ => false⟩ (FreshNandCost.profile target width).implementation = _
  rw [WireProfileAvailability.quotient_minimum, FreshNandCost.profile_quotientMinimum]

theorem minimum_gap (target : Implementation inputs outputs) (width : Nat) :
    terminalFullProfileMinimum
        (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).profileSystem
        (FreshNandCost.profile target width).implementation -
      terminalQuotientProfileMinimum
        (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).profileSystem
        (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).projection
        (FreshNandCost.profile target width).implementation = width := by
  rw [full_minimum, quotient_minimum,
    Nat.add_comm (referenceMinimum target) width, Nat.add_sub_cancel]

end PNP.DirectWire.ComputedWireProfileCost
