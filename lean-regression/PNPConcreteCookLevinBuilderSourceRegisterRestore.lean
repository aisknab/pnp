import PNP.Concrete.CookLevinBuilderSourceRegisterRestore

namespace PNP.Concrete.CookLevinBuilderSourceRegisterRestoreRegression

open CookLevin CookLevin.BuilderSourceRegisterRestore PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (count width)
open BuilderDividerSourceExecution (preservedWorkspace sourceSpan)
open BuilderArbitrarySlotHeaderRouter

example : resultQuotient (.less 2 4) = 2 := by decide
example : resultCount (.less 2 4) = 7 := by decide
example : resultQuotient (.equal 5) = 5 := by decide
example : resultCount (.equal 5) = 5 := by decide
example : resultQuotient (.greater 3 4) = 8 := by decide
example : resultCount (.greater 3 4) = 3 := by decide

example : BuilderClassifierRegisterRestore.restoredValues
    (ofComparison 2 1 2 2 (RawRouter.compareResult 0 1 2)) = [2, 0, 3, 2, 1, 2] := by decide
example : BuilderClassifierRegisterRestore.restoredValues
    (ofComparison 4 0 2 2 (RawRouter.compareResult 0 2 2)) = [2, 0, 4, 2, 2, 2] := by decide
example : BuilderClassifierRegisterRestore.restoredValues
    (ofComparison 6 0 2 2 (RawRouter.compareResult 0 3 2)) = [2, 0, 6, 2, 3, 2] := by decide
example : BuilderClassifierRegisterRestore.restoredValues
    (ofComparison 0 0 0 0 (RawRouter.compareResult 0 0 0)) = [0, 0, 0, 0, 0, 0] := by decide

/-- These start on actual comparator endpoint tapes, not manufactured restoration views. -/
example :
    workRunExact? BuilderClassifierRegisterRestore.machine 34
        (workStartConfiguration BuilderClassifierRegisterRestore.machine
          (BuilderSourceClassifier.tailFinal 2 1 2 1 2 [leftMarker, unitSymbol, separatorSymbol, .blank]).tape) =
      some {
        state := BuilderClassifierRegisterRestore.machine.acceptState
        tape := BuilderDividerOperands.endTape [2, 0, 3, 2, 1, 2]
          [leftMarker, unitSymbol, separatorSymbol, .blank] []
      } := by decide

example :
    workRunExact? BuilderClassifierRegisterRestore.machine 37
        (workStartConfiguration BuilderClassifierRegisterRestore.machine
          (BuilderSourceClassifier.tailFinal 4 0 2 2 2 [rightMarker]).tape) =
      some {
        state := BuilderClassifierRegisterRestore.machine.acceptState
        tape := BuilderDividerOperands.endTape [2, 0, 4, 2, 2, 2] [rightMarker] []
      } := by decide

example :
    workRunExact? BuilderClassifierRegisterRestore.machine 43
        (workStartConfiguration BuilderClassifierRegisterRestore.machine
          (BuilderSourceClassifier.tailFinal 6 0 2 3 2 []).tape) =
      some {
        state := BuilderClassifierRegisterRestore.machine.acceptState
        tape := BuilderDividerOperands.endTape [2, 0, 6, 2, 3, 2] [] []
      } := by decide

example :
    workRunExact? BuilderClassifierRegisterRestore.machine 13
        (workStartConfiguration BuilderClassifierRegisterRestore.machine
          (BuilderSourceClassifier.tailFinal 0 0 0 0 0 []).tape) =
      some {
        state := BuilderClassifierRegisterRestore.machine.acceptState
        tape := BuilderDividerOperands.endTape [0, 0, 0, 0, 0, 0] [] []
      } := by decide

example : (RawRouter.compareResult 0 1 2).isLess = true := by decide
example : (RawRouter.compareResult 0 2 2).isLess = false := by decide
example : (RawRouter.compareResult 0 3 2).isLess = false := by decide
example : ofComparison 4 0 2 2 (RawRouter.compareResult 0 2 2) ≠
    ofComparison 6 0 2 2 (RawRouter.compareResult 0 3 2) := by decide

example (processed coordinate boundary : Nat) :
    resultQuotient (RawRouter.compareResult processed coordinate boundary) = processed + coordinate ∧
      resultCount (RawRouter.compareResult processed coordinate boundary) = processed + boundary :=
  compareResult_totals processed coordinate boundary

example (consumed remainder divisor sidecar : Nat) (result : RawRouter.ComparisonResult) :
    (ofComparison consumed remainder divisor sidecar result).countTotal = resultCount result ∧
      (ofComparison consumed remainder divisor sidecar result).quotientTotal = resultQuotient result ∧
      (ofComparison consumed remainder divisor sidecar result).dividend = remainder + consumed ∧
      (ofComparison consumed remainder divisor sidecar result).width = divisor ∧
      (ofComparison consumed remainder divisor sidecar result).sidecarCount = sidecar :=
  ofComparison_fields consumed remainder divisor sidecar result

example (consumed remainder divisor sidecar : Nat) (result : RawRouter.ComparisonResult)
    (workspace : List WorkSymbol) :
    BuilderClassifierRegisterRestore.inputTape
        (ofComparison consumed remainder divisor sidecar result) workspace [] =
      BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape
        (BuilderPostDividerRawRouteClassifier.appendExteriorTape
          (RawRouter.resultConfiguration result).tape
          (BuilderPostDividerRawRouteClassifier.preservedExterior
            consumed remainder divisor [] sidecar workspace)) :=
  inputTape_ofComparison consumed remainder divisor sidecar result workspace

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (view problem index).countTotal = count problem ∧
      (view problem index).quotientTotal = index / width problem ∧
      (view problem index).dividend = index ∧
      (view problem index).width = width problem ∧
      (view problem index).sidecarCount = count problem := view_totals problem index

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderClassifierRegisterRestore.restoredValues (view problem index) =
      [count problem, 0, index, width problem, index / width problem, count problem] :=
  restoredValues_eq problem index

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderClassifierRegisterRestore.inputTape (view problem index)
        (preservedWorkspace problem index remaining output) [] =
      (BuilderSourceClassifier.finalConfiguration problem index remaining output).tape :=
  classifier_restore_handoff problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? BuilderClassifierRegisterRestore.machine (restorationSteps problem index)
        (restorationInitial problem index remaining output) =
      some (restorationFinal problem index remaining output) :=
  restoration_workRunExact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine BuilderClassifierRegisterRestore.machine) (6 * restorationSteps problem index)
        (encodeWorkConfiguration (restorationInitial problem index remaining output)) =
      encodeWorkConfiguration (restorationFinal problem index remaining output) :=
  restoration_run_compile_exact problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (restorationFinal problem index remaining output).tape =
      {
        left := []
        head := scratchEndSymbol
        right := (registerWord
          (BuilderOperandRegisters.retainedValues problem index remaining ++ appended problem index)).reverse ++
            BuilderDividerOperands.inside problem.input output
      } := restoration_final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    restorationSteps problem index ≤ 11 * (sourceSpan problem.verifier).eval problem.input.length + 13 :=
  restoration_workSteps_le problem index remaining hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    (BuilderSourceClassifier.finalConfiguration problem index remaining output).state =
      (BuilderSourceClassifier.machine problem.verifier).acceptState :=
  classifier_accept_of_body problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hNonbody : count problem ≤ index / width problem) :
    (BuilderSourceClassifier.finalConfiguration problem index remaining output).state =
      (BuilderSourceClassifier.machine problem.verifier).rejectState :=
  classifier_reject_of_nonbody problem index remaining output hNonbody

/-- Non-body cannot be silently treated as the body's accepting endpoint. -/
example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hNonbody : count problem ≤ index / width problem) :
    (BuilderSourceClassifier.finalConfiguration problem index remaining output).state ≠
      (BuilderSourceClassifier.machine problem.verifier).acceptState := by
  rw [classifier_reject_of_nonbody problem index remaining output hNonbody]
  exact Ne.symm (BuilderSourceClassifier.machine_acceptState_ne_rejectState problem.verifier)

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    workRunExact? (bodyMachine problem.verifier) (bodySteps problem index remaining)
        (bodyInitial problem index remaining output) = some (bodyFinal problem index remaining output) :=
  body_workRunExact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (hBody : index / width problem < count problem) :
    run (compileWorkMachine (bodyMachine problem.verifier)) (6 * bodySteps problem index remaining)
        (encodeWorkConfiguration (bodyInitial problem index remaining output)) =
      encodeWorkConfiguration (bodyFinal problem index remaining output) :=
  body_run_compile_exact problem index remaining output hBody

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).state = (bodyMachine problem.verifier).acceptState :=
  body_finalConfiguration_state problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (bodyFinal problem index remaining output).tape = (restorationFinal problem index remaining output).tape :=
  body_final_tape_layout problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * bodySteps problem index remaining ≤ (bodyRawTimeBound problem.verifier).eval problem.input.length :=
  body_rawTimeBound_le problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := body_rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (bodyMachine verifier) := body_noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyMachine verifier).acceptState ≠ (bodyMachine verifier).rejectState := body_acceptState_ne_rejectState verifier

end PNP.Concrete.CookLevinBuilderSourceRegisterRestoreRegression
