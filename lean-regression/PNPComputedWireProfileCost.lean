import PNP

open PNP PNP.DirectWire

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat)
    (keep : Fin width → Bool) :
    terminalFullProfileMinimum
      (WireProfileAmbient.model (FreshNandCost.profile target width) keep).profileSystem
      (FreshNandCost.profile target width).implementation =
        referenceMinimum target + width :=
  ComputedWireProfileCost.full_minimum target width keep

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    terminalQuotientProfileMinimum
      (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).profileSystem
      (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).projection
      (FreshNandCost.profile target width).implementation =
        referenceMinimum target :=
  ComputedWireProfileCost.quotient_minimum target width

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    terminalFullProfileMinimum
        (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).profileSystem
        (FreshNandCost.profile target width).implementation -
      terminalQuotientProfileMinimum
        (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).profileSystem
        (WireProfileAmbient.model (FreshNandCost.profile target width) (fun _ => false)).projection
        (FreshNandCost.profile target width).implementation = width :=
  ComputedWireProfileCost.minimum_gap target width
