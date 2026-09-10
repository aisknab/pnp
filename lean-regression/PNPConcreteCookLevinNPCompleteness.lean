/-
Copyright (c) 2026 PNP Labs.
Unbounded concrete CNFSAT hardness and NP-completeness contracts for M231.
-/
import PNP.Concrete.CookLevinNPCompleteness

open PNP.Concrete PNP.Concrete.CookLevin

example (source : Language) (sourceInNP : InNP source) :
    ReducesTo source CNFSAT :=
  cnfSAT_np_hard source sourceInNP

example : NPComplete CNFSAT :=
  cnfSAT_np_complete

example : InNP CNFSAT :=
  cnfSAT_np_complete.inNP

example (source : Language) (sourceInNP : InNP source) :
    Nonempty (PolynomialReduction source CNFSAT) :=
  cnfSAT_np_complete.hard source sourceInNP
