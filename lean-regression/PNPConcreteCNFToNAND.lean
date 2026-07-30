import PNP.Concrete.CNFToNAND

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace PNP.Concrete.CNFToNANDRegression

open PNP.Concrete
open PNP.Concrete.CNFToNAND
open PNP.Concrete.LockedNAND

private def emptyFormula : CNFFormula :=
  { variableCount := 0, clauses := [] }

private def emptyClauseFormula : CNFFormula :=
  { variableCount := 0, clauses := [[]] }

private def positiveFormula : CNFFormula :=
  { variableCount := 1
    clauses := [[{ positive := true, variableIndex := 0 }]] }

private def negativeFormula : CNFFormula :=
  { variableCount := 1
    clauses := [[{ positive := false, variableIndex := 0 }]] }

private def outOfRangePositiveFormula : CNFFormula :=
  { variableCount := 0
    clauses := [[{ positive := true, variableIndex := 0 }]] }

private def outOfRangeNegativeFormula : CNFFormula :=
  { variableCount := 0
    clauses := [[{ positive := false, variableIndex := 0 }]] }

private def tautologyFormula : CNFFormula :=
  { variableCount := 1
    clauses :=
      [[ { positive := true, variableIndex := 0 }
       , { positive := false, variableIndex := 0 } ]] }

private def contradictionFormula : CNFFormula :=
  { variableCount := 1
    clauses :=
      [ [{ positive := true, variableIndex := 0 }]
      , [{ positive := false, variableIndex := 0 }] ] }

private def duplicateMultiClauseFormula : CNFFormula :=
  { variableCount := 2
    clauses :=
      [ [ { positive := true, variableIndex := 0 }
        , { positive := true, variableIndex := 0 } ]
      , [ { positive := false, variableIndex := 1 }
        , { positive := true, variableIndex := 0 } ] ] }

/-! The compiler handles the two Boolean identities at the edges of CNF:
an empty conjunction is true, while one empty disjunction is false. -/

example : emptyFormula.Satisfiable := by
  refine ⟨[], ?_⟩
  simp [CNFFormula.Satisfied, emptyFormula, ClausesSatisfied]

example : ¬ emptyClauseFormula.Satisfiable := by
  simp [CNFFormula.Satisfiable, CNFFormula.Satisfied,
    emptyClauseFormula, ClausesSatisfied, ClauseSatisfied]

example :
    (compileFormula emptyFormula).gates.length = 1 := by
  simpa [emptyFormula, literalCount, validNegativeLiteralCount] using
    compileFormula_gateCount_exact emptyFormula

example :
    (compileFormula emptyClauseFormula).gates.length = 2 := by
  simpa [emptyClauseFormula, literalCount, validNegativeLiteralCount] using
    compileFormula_gateCount_exact emptyClauseFormula

/-! Positive, negative, and both out-of-range signs exercise every literal
branch.  Out-of-range literals remain false rather than acquiring an
invented assignment bit. -/

example :
    (compileFormula positiveFormula).gates.length = 5 := by
  simpa [positiveFormula, literalCount, validNegativeLiteralCount] using
    compileFormula_gateCount_exact positiveFormula

example :
    (compileFormula negativeFormula).gates.length = 6 := by
  simpa [negativeFormula, literalCount, validNegativeLiteralCount] using
    compileFormula_gateCount_exact negativeFormula

example :
    (compileFormula outOfRangePositiveFormula).gates.length = 5 := by
  simpa [outOfRangePositiveFormula, literalCount,
    validNegativeLiteralCount] using
    compileFormula_gateCount_exact outOfRangePositiveFormula

example :
    (compileFormula outOfRangeNegativeFormula).gates.length = 5 := by
  simpa [outOfRangeNegativeFormula, literalCount,
    validNegativeLiteralCount] using
    compileFormula_gateCount_exact outOfRangeNegativeFormula

example : ¬ outOfRangePositiveFormula.Satisfiable := by
  simp [CNFFormula.Satisfiable, CNFFormula.Satisfied,
    outOfRangePositiveFormula, ClausesSatisfied, ClauseSatisfied,
    LiteralSatisfied, assignmentAt]

example : ¬ outOfRangeNegativeFormula.Satisfiable := by
  simp [CNFFormula.Satisfiable, CNFFormula.Satisfied,
    outOfRangeNegativeFormula, ClausesSatisfied, ClauseSatisfied,
    LiteralSatisfied, assignmentAt]

/-! Repetition, multiple clauses, tautologies, and contradictions all use
the same size-independent compiler. -/

example : tautologyFormula.Satisfiable := by
  exact ⟨[true], by
    simp [CNFFormula.Satisfied, tautologyFormula,
      ClausesSatisfied, ClauseSatisfied, LiteralSatisfied, assignmentAt]⟩

example : ¬ contradictionFormula.Satisfiable := by
  rintro ⟨assignment, _, clauses⟩
  change
    (assignmentAt assignment 0 = some true ∨ False) ∧
      ((assignmentAt assignment 0 = some false ∨ False) ∧ True)
    at clauses
  rcases clauses with ⟨positive, negative, _⟩
  rcases positive with positive | impossible
  · rcases negative with negative | impossible
    · exact Bool.noConfusion
        (Option.some.inj (positive.symm.trans negative))
    · exact impossible
  · exact impossible

example : duplicateMultiClauseFormula.Satisfiable := by
  exact ⟨[true, false], by
    simp [CNFFormula.Satisfied, duplicateMultiClauseFormula,
      ClausesSatisfied, ClauseSatisfied, LiteralSatisfied, assignmentAt]⟩

/-! The exact codec boundary is strict and canonical. -/

example :
    decodeEncodedCNF (encodeCNF duplicateMultiClauseFormula) =
      some duplicateMultiClauseFormula :=
  decodeEncodedCNF_canonical duplicateMultiClauseFormula

example :
    encodeCNF duplicateMultiClauseFormula =
      encodeCNF duplicateMultiClauseFormula := by
  exact encodeCNF_of_decodeEncodedCNF
    (encodeCNF duplicateMultiClauseFormula)
    duplicateMultiClauseFormula
    (decodeEncodedCNF_canonical duplicateMultiClauseFormula)

example :
    compileEncodedCNFToNAND (encodeCNF duplicateMultiClauseFormula) =
      encodeCircuit (compileFormula duplicateMultiClauseFormula) :=
  compileEncodedCNFToNAND_of_decoded
    (encodeCNF duplicateMultiClauseFormula)
    duplicateMultiClauseFormula
    (decodeEncodedCNF_canonical duplicateMultiClauseFormula)

example :
    decodeValidCircuit
        (encodeCircuit (compileFormula duplicateMultiClauseFormula)) =
      some (compileFormula duplicateMultiClauseFormula) :=
  decodeValidCircuit_encode_compileFormula duplicateMultiClauseFormula

example :
    (compileFormula duplicateMultiClauseFormula).wellFormed = true :=
  compileFormula_wellFormed duplicateMultiClauseFormula

example :
    ∃ index,
      (compileFormula duplicateMultiClauseFormula).output = .gate index :=
  compileFormula_output_is_gate duplicateMultiClauseFormula

/-! Malformed input fails closed, and the polynomial accounts for every
input string, not only canonical formula encodings. -/

example : compileEncodedCNFToNAND [] = [] := by
  exact compileEncodedCNFToNAND_of_malformed [] rfl

example : ¬ EncodedNANDSAT [] :=
  empty_not_encodedNANDSAT

example (bits : BitString) :
    BitString.size (compileEncodedCNFToNAND bits) ≤
      cnfToNANDOutputSizePolynomial.eval (BitString.size bits) :=
  compileEncodedCNFToNAND_size_le bits

example (bitLength : Nat) :
    cnfToNANDOutputSizePolynomial.eval bitLength =
      4 *
        ((5 * (bitLength + 1)) * (15 * (bitLength + 1)) +
          19 * (bitLength + 1)) :=
  cnfToNANDOutputSizePolynomial_eval bitLength

/-! The semantic theorem is universal over raw bitstrings, and its
composition reaches the already-formalized locked-NAND threshold language
without claiming a finite-machine implementation of this new compiler. -/

example (formula : CNFFormula) :
    formula.Satisfiable ↔
      EncodedNANDSAT (encodeCircuit (compileFormula formula)) :=
  formula_satisfiable_iff_encoded_compileFormula formula

example (bits : BitString) :
    CNFSAT bits ↔
      EncodedNANDSAT (compileEncodedCNFToNAND bits) :=
  compileEncodedCNFToNAND_correct bits

example (bits : BitString) :
    CNFSAT bits ↔
      EncodedLockedNANDThreshold (buildLockedNANDFromCNF bits) :=
  buildLockedNANDFromCNF_correct bits

end PNP.Concrete.CNFToNANDRegression
