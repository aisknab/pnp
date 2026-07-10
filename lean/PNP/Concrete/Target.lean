/-
Copyright (c) 2026 PNP Labs.

Inactive concrete target statement for the finite charged-pipeline model.
This file names the proposition; it does not assert or prove that proposition.
-/

import PNP.Concrete.Complexity

namespace PNP.Main

/-- The concrete P-versus-NP target for the finite charged-pipeline model.
This is an alias for mutual inclusion, not a released root theorem. -/
def ConcretePEqualsNP : Prop := PNP.Concrete.PEqualsNP

/-- Expansion pin for the inactive concrete target. -/
theorem concretePEqualsNP_iff :
    ConcretePEqualsNP ↔ PNP.Concrete.PEqualsNP := Iff.rfl

end PNP.Main
