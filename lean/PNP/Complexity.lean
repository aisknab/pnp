/-
Copyright (c) 2026 PNP Labs.

Abstract complexity-theory layer for the first Lean bridge.

This file intentionally keeps the machine model abstract while proving the
standard implication used by the report bridge: if an NP-complete language is
in P, then P = NP, provided the standard class-closure facts are supplied.
-/

namespace PNP

/-- An abstract formal language.  This pass does not choose a concrete machine
model. -/
structure Language where
  name : String

/-- Complexity classes are represented extensionally as sets of languages. -/
def ComplexityClass := Language → Prop

/-- The standard complexity classes, left abstract in this pass. -/
constant PClass : ComplexityClass
constant NPClass : ComplexityClass

/-- The final theorem statement. -/
def PEqualsNP : Prop := PClass = NPClass

/-- Polynomial-time many-one reduction, kept abstract in this bridge layer. -/
constant ReducesToPoly : Language → Language → Prop

/-- The SAT language used by the locked-NAND reduction. -/
constant SAT : Language

/-- NP-completeness over the abstract reduction relation. -/
structure NPComplete (L : Language) : Prop where
  inNP : NPClass L
  hard : ∀ {A : Language}, NPClass A → ReducesToPoly A L

/-- Standard closure facts needed for the usual NP-complete-in-P implication.

Future passes can replace these fields by concrete machine-model proofs. -/
structure StandardComplexityAxioms : Prop where
  pSubsetNP : ∀ {A : Language}, PClass A → NPClass A
  reductionTransportsP : ∀ {A B : Language}, ReducesToPoly A B → PClass B → PClass A

/-- If an NP-complete language is in P, then P = NP, assuming only the standard
class-closure facts above. -/
theorem np_complete_in_p_implies_p_eq_np
    (H : StandardComplexityAxioms)
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP := by
  funext A
  apply propext
  constructor
  · intro hP
    exact H.pSubsetNP hP
  · intro hNP
    exact H.reductionTransportsP (hComplete.hard hNP) hInP

/-- SAT-specific form used by the report bridge. -/
theorem sat_np_complete_and_sat_in_p_implies_p_eq_np
    (H : StandardComplexityAxioms)
    (hSATComplete : NPComplete SAT)
    (hSATInP : PClass SAT) : PEqualsNP :=
  np_complete_in_p_implies_p_eq_np H hSATComplete hSATInP

end PNP
