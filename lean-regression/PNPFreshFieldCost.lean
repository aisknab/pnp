import PNP

namespace PNP.DirectWire.FreshNandCostRegression

open FreshNandCost

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    referenceMinimum (extend target width) = referenceMinimum target + width :=
  referenceMinimum_extend target width

example {inputs outputs gates width : Nat} (target : Implementation inputs outputs)
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (fresh : ∀ valuation index, candidate.semantics valuation (Fin.natAdd outputs index) =
      boolNand (valuation (leftInput index)) (valuation (rightInput index)))
    (old : ∀ valuation output, candidate.semantics valuation (Fin.castAdd width output) =
      target.candidate.semantics
        (fun index => valuation (Fin.castAdd (width + width) index)) output) :
    referenceMinimum target + width ≤ gates :=
  gateCount_lower_bound target candidate fresh old

example {inputs outputs gates : Nat} (candidate : Candidate inputs gates outputs)
    (width : Nat) (valuation : Valuation (inputs + (width + width))) (output : Fin outputs) :
    (extendedCandidate candidate width).semantics valuation (Fin.castAdd width output) =
      candidate.semantics (fun index => valuation (Fin.castAdd (width + width) index)) output :=
  extended_old candidate width valuation output

example {inputs outputs gates : Nat} (candidate : Candidate inputs gates outputs)
    (width : Nat) (valuation : Valuation (inputs + (width + width))) (index : Fin width) :
    (extendedCandidate candidate width).semantics valuation (Fin.natAdd outputs index) =
      boolNand (valuation (leftInput index)) (valuation (rightInput index)) :=
  extended_fresh candidate width valuation index

example {inputs outputs : Nat} (target : Implementation inputs outputs) (width : Nat) :
    (extend target width).gateCount = target.gateCount + width :=
  extend_gateCount target width

example {inputs outputs gates width : Nat}
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width))
    (matched : FreshMatches candidate) :
    width ≤ (extractTerminalSupport candidate (erased candidate matched)).gateCount :=
  erased_count_lower_bound candidate matched

private def bit : Fin 1 := ⟨0, by decide⟩
private def negProgram : Program 1 1 := .snoc .empty ⟨.input bit, .input bit⟩
private def neg : Candidate 1 1 1 := Candidate.ofDirectWireWord negProgram ⟨fun _ => .gate bit⟩
private def doubleProgram : Program 1 2 := .snoc negProgram ⟨.gate bit, .gate bit⟩
private def tripleProgram : Program 1 3 :=
  .snoc doubleProgram ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩
private def triple : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord tripleProgram ⟨fun _ => .gate ⟨2, by decide⟩⟩

private theorem neg_value (valuation : Valuation 1) (output : Fin 1) :
    neg.semantics valuation output = boolNand (valuation bit) (valuation bit) := by
  unfold neg
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

theorem neg_minimum : referenceMinimum neg.toImplementation = 1 := by
  apply referenceMinimum_eq_gateCount_of_squareBaseline neg
  constructor
  · intro output
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [neg_value, neg_value]
    decide
  · intro output input
    refine ⟨fun _ => true, ?_⟩
    rw [neg_value]
    change false ≠ true
    decide
  · intro left right different
    exact False.elim (different (Subsingleton.elim left right))

theorem arbitrary_width_exact (width : Nat) :
    referenceMinimum (extend neg.toImplementation width) = 1 + width := by
  rw [referenceMinimum_extend, neg_minimum]

theorem triple_equivalent : equivalentBool triple neg = true := by decide +kernel

theorem triple_minimum : referenceMinimum triple.toImplementation = 1 := by
  exact (referenceMinimum_invariant triple.toImplementation neg.toImplementation
    (equivalentBool_sound triple_equivalent)).trans neg_minimum

theorem redundant_extension_minimum :
    referenceMinimum (extend triple.toImplementation 2) = 3 := by
  rw [referenceMinimum_extend, triple_minimum]

theorem redundant_extension_implementation :
    (extend triple.toImplementation 2).gateCount = 5 := by decide +kernel

private def empty : Candidate 0 0 0 := Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

theorem empty_minimum : referenceMinimum empty.toImplementation = 0 :=
  Nat.eq_zero_of_le_zero (referenceMinimum_le_target empty.toImplementation)

theorem empty_extension_minimum : referenceMinimum (extend empty.toImplementation 2) = 2 := by
  rw [referenceMinimum_extend, empty_minimum]

private def duplicated : Candidate 4 1 2 :=
  Candidate.ofDirectWireWord
    (.snoc .empty ⟨.input ⟨0, by decide⟩, .input ⟨2, by decide⟩⟩)
    ⟨fun _ => .gate bit⟩
private def distinguish : Valuation 4 := fun index => decide (index.val = 1 ∨ index.val = 3)
private def second : Fin 2 := ⟨1, by decide⟩

theorem duplicate_violation :
    duplicated.semantics distinguish second ≠
      freshValue (inputs := 0) (width := 2) distinguish second := by decide +kernel

theorem duplicates_not_independent : ¬ FreshMatches (inputs := 0) (outputs := 0) (width := 2) duplicated := by
  intro matched
  exact duplicate_violation (matched distinguish second)

private def projection : Candidate 2 0 1 :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .input ⟨0, by decide⟩⟩

theorem projection_violation :
    projection.semantics (fun _ => true) bit ≠
      freshValue (inputs := 0) (width := 1) (fun _ => true) bit := by decide +kernel

theorem projection_not_fresh : ¬ FreshMatches (inputs := 0) (outputs := 0) (width := 1) projection := by
  intro matched
  exact projection_violation (matched (fun _ => true) bit)

private def extended := extendedCandidate triple 2
private def restored := retracted extended (extended_fresh triple 2)

theorem retraction_removes_only_added_gates : restored.gateCount = 3 := by decide +kernel

private def mixed : Candidate 1 0 2 := Candidate.ofDirectWireWord .empty
  ⟨fun output => if output.val = 0 then .input bit else .constant false⟩

private def extensionChecks {inputs gates outputs : Nat} (candidate : Candidate inputs gates outputs)
    (width : Nat) : Bool :=
  allTrue (allBoolTuples (inputs + (width + width))) fun tuple =>
    (allTrue (allFin outputs) fun output => boolEqual
      ((extendedCandidate candidate width).semantics tuple.toValuation (Fin.castAdd width output))
      (candidate.semantics (fun index => tuple.toValuation (Fin.castAdd (width + width) index)) output)) &&
    (allTrue (allFin width) fun index => boolEqual
      ((extendedCandidate candidate width).semantics tuple.toValuation (Fin.natAdd outputs index))
      (freshValue tuple.toValuation index))

private def freshChecks {inputs gates outputs width : Nat}
    (candidate : Candidate (inputs + (width + width)) gates (outputs + width)) : Bool :=
  allTrue (allBoolTuples (inputs + (width + width))) fun tuple =>
    allTrue (allFin width) fun index => boolEqual
      (candidate.semantics tuple.toValuation (Fin.natAdd outputs index)) (freshValue tuple.toValuation index)

private def checks : List (String × Bool) :=
  [ ("zero extension width", extensionChecks triple 0)
  , ("one independent fresh output", extensionChecks neg 1)
  , ("two independent outputs preserve redundant old circuit", extensionChecks triple 2)
  , ("three fresh outputs with no old inputs or outputs", extensionChecks empty 3)
  , ("free input and constant old outputs", extensionChecks mixed 2)
  , ("constructor adds exactly requested gates", decide ((extend triple.toImplementation 2).gateCount = 5))
  , ("canonical fresh gates are all selected", allTrue (allFin 2) fun index =>
      terminalGateSelected (erased extended (extended_fresh triple 2))
        (freshGate extended (extended_fresh triple 2) index))
  , ("canonical erased count is two", decide
      ((extractTerminalSupport extended (erased extended (extended_fresh triple 2))).gateCount = 2))
  , ("restricted reconstruction retains original gate count", decide (restored.gateCount = 3))
  , ("restricted reconstruction preserves old computation", equivalentBool
      (oldCandidate extended (extended_fresh triple 2)) triple)
  , ("duplicated fields fail independence", !(freshChecks (inputs := 0) (outputs := 0) (width := 2) duplicated))
  , ("primary-input substitute fails fresh NAND semantics",
      !(freshChecks (inputs := 0) (outputs := 0) (width := 1) projection))
  ]

def run : IO Unit := do
  for (name, passed) in checks do
    if passed then
      IO.println ("fresh-cost-check-passed: " ++ name)
    else
      throw (IO.userError ("fresh-cost-check-failed: " ++ name))
  IO.println "fresh-cost-regressions-complete: 12 runtime checks; 6 independent general type contracts"

end PNP.DirectWire.FreshNandCostRegression

#print axioms PNP.DirectWire.FreshNandCostRegression.neg_minimum
#print axioms PNP.DirectWire.FreshNandCostRegression.arbitrary_width_exact
#print axioms PNP.DirectWire.FreshNandCostRegression.triple_equivalent
#print axioms PNP.DirectWire.FreshNandCostRegression.triple_minimum
#print axioms PNP.DirectWire.FreshNandCostRegression.redundant_extension_minimum
#print axioms PNP.DirectWire.FreshNandCostRegression.redundant_extension_implementation
#print axioms PNP.DirectWire.FreshNandCostRegression.empty_minimum
#print axioms PNP.DirectWire.FreshNandCostRegression.empty_extension_minimum
#print axioms PNP.DirectWire.FreshNandCostRegression.duplicate_violation
#print axioms PNP.DirectWire.FreshNandCostRegression.duplicates_not_independent
#print axioms PNP.DirectWire.FreshNandCostRegression.projection_violation
#print axioms PNP.DirectWire.FreshNandCostRegression.projection_not_fresh
#print axioms PNP.DirectWire.FreshNandCostRegression.retraction_removes_only_added_gates

def main : IO Unit := PNP.DirectWire.FreshNandCostRegression.run
