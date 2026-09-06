import PNP.Concrete.CookLevinBuilderConstraintRegionRegisters

namespace PNP.Concrete.CookLevinBuilderConstraintRegionRegistersRegression

open CookLevin CookLevin.BuilderConstraintRegionRegisters BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside count)
open BuilderDividerSourceExecution (sourceSpan)

example {language : Language} (problem : VerifierTableauProblem language) :
    orderedLengths problem =
      [regionLength problem .shape, regionLength problem .initial, regionLength problem .control,
       regionLength problem .preservation, regionLength problem .accepting] := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    (orderedLengths problem).length = 5 := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    regionLength problem .initial = 3 + termValue problem .initialTail := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    regionLength problem .initial ≠ termValue problem .initialTail := by
  change 3 + termValue problem .initialTail ≠ termValue problem .initialTail
  omega

example {language : Language} (problem : VerifierTableauProblem language) :
    regionLength problem .accepting = 1 := rfl

example {language : Language} (problem : VerifierTableauProblem language) :
    orderedLengths problem =
      [problem.dimensions.timeCount * (problem.dimensions.tapeWidth problem.tableauInputMode + 2),
       3 + 2 * ((problem.certificateLimit + 1) * problem.dimensions.tapeWidth problem.tableauInputMode),
       9 * (problem.uniformFuel * problem.dimensions.tapeWidth problem.tableauInputMode *
         problem.dimensions.stateBound),
       3 * (problem.uniformFuel * problem.dimensions.tapeWidth problem.tableauInputMode *
         problem.dimensions.tapeWidth problem.tableauInputMode), 1] :=
  orderedLengths_match_schedule problem

example {language : Language} (problem : VerifierTableauProblem language) :
    (orderedLengths problem).sum = problem.formulaConstraintSlotCount :=
  orderedLengths_sum problem

example {language : Language} (problem : VerifierTableauProblem language) :
    count problem = (orderedLengths problem).sum * BuilderClauseDividerOperands.clauseWidth problem := by
  rw [orderedLengths_sum]
  exact BuilderClauseDividerOperands.clauseCount_product problem

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    orderedSlot problem index = problem.formulaConstraintSlotDirect index := orderedSlot_eq problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    orderedSlot problem index = problem.formulaConstraintSchedule[index]? :=
  (orderedSlot_eq problem index).trans (problem.formulaConstraintSlotDirect_eq index)

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hPadding : problem.formulaConstraintSlotDirect index = some none) :
    orderedSlot problem index = some none := (orderedSlot_eq problem index).trans hPadding

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hOutside : problem.formulaConstraintSlotDirect index = none) :
    orderedSlot problem index = none := (orderedSlot_eq problem index).trans hOutside

example : (none : Option (Option Nat)) ≠ some none := by decide

example {language : Language} (problem : VerifierTableauProblem language) (term : Term) :
    registerValues (formulaConstraintCountPolynomial problem.verifier) problem.input.length =
      constraintOlder problem term ++ [termValue problem term] ++ constraintNewer problem term :=
  constraint_selection problem term

example {language : Language} (problem : VerifierTableauProblem language) (term : Term) :
    (constraintNewer problem term).length = constraintNewerCount problem.verifier term :=
  constraintNewer_length problem term

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    constraintNewerCount verifier .initialTail = 1 := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    constraintNewerCount verifier .preservation =
      nodeCount (termPolynomial verifier .initialTail) + 4 := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    constraintNewerCount verifier .control =
      nodeCount (termPolynomial verifier .preservation) +
      nodeCount (termPolynomial verifier .initialTail) + 5 := rfl

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    constraintNewerCount verifier .shape = nodeCount (termPolynomial verifier .control) +
      nodeCount (termPolynomial verifier .preservation) +
      nodeCount (termPolynomial verifier .initialTail) + 5 := rfl

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (coordinateSuffix problem index).length = 11 := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) :
    inputValues problem index remaining appended =
      constraintOlder problem term ++ [termValue problem term] ++
        newerValues problem index remaining appended term :=
  inputValues_selection problem index remaining appended term

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) :
    (newerValues problem index remaining appended term).length =
      copyOffset problem.verifier term appended.length :=
  newerValues_length problem index remaining appended term

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderClauseCoordinateRegisters.finalConfiguration problem index remaining output).tape =
      endTape (inputValues problem index remaining []) (inside problem.input output) [] :=
  source_tape_handoff problem index remaining output

example {language : Language} (verifier : PolynomialTimeVerifier language)
    (term : Term) (appendedCount : Nat) :
    copyMachine verifier term appendedCount = RegisterCopy.machine (copyOffset verifier term appendedCount) := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) (workspace tail : List WorkSymbol) :
    workRunExact? (copyMachine problem.verifier term appended.length)
      (copySteps problem index remaining appended term)
      (workStartConfiguration (copyMachine problem.verifier term appended.length)
        (endTape (inputValues problem index remaining appended) workspace tail)) =
    some {
      state := (copyMachine problem.verifier term appended.length).acceptState
      tape := endTape (inputValues problem index remaining appended ++ [termValue problem term])
        workspace (tail.drop (termValue problem term + 1))
    } := copy_workRunExact problem index remaining appended term workspace tail

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term) (workspace tail : List WorkSymbol) :
    run (compileWorkMachine (copyMachine problem.verifier term appended.length))
      (6 * copySteps problem index remaining appended term)
      (encodeWorkConfiguration (workStartConfiguration (copyMachine problem.verifier term appended.length)
        (endTape (inputValues problem index remaining appended) workspace tail))) =
      encodeWorkConfiguration {
        state := (copyMachine problem.verifier term appended.length).acceptState
        tape := endTape (inputValues problem index remaining appended ++ [termValue problem term])
          workspace (tail.drop (termValue problem term + 1))
      } := copy_run_compile_exact problem index remaining appended term workspace tail

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let bound := 9 * (sourceSpan problem.verifier).eval problem.input.length + 11 +
      appended.length + appended.sum
    termValue problem term ≤ bound ∧
      (newerValues problem index remaining appended term).length +
        (newerValues problem index remaining appended term).sum ≤ bound :=
  source_selection_bounds problem index remaining appended term hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (appended : List Nat) (term : Term)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    let bound := 9 * (sourceSpan problem.verifier).eval problem.input.length + 11 +
      appended.length + appended.sum
    copySteps problem index remaining appended term ≤ 4 * (bound + 1) ^ 2 + 9 * (bound + 1) + 5 :=
  copySteps_le problem index remaining appended term hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) (term : Term) (extra : Nat) :
    (copyMachine verifier term extra).rules.Pairwise WorkMachineChain.QueryDistinct :=
  copy_rules_pairwise_query_distinct verifier term extra

example {language : Language} (verifier : PolynomialTimeVerifier language) (term : Term) (extra : Nat) :
    WorkMachineChain.NoRuleAtAccept (copyMachine verifier term extra) :=
  copy_noRuleAtAccept verifier term extra

example {language : Language} (verifier : PolynomialTimeVerifier language) (term : Term) (extra : Nat) :
    (copyMachine verifier term extra).acceptState ≠ (copyMachine verifier term extra).rejectState :=
  copy_acceptState_ne_rejectState verifier term extra

end PNP.Concrete.CookLevinBuilderConstraintRegionRegistersRegression
