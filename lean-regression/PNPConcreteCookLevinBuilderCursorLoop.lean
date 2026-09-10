/-
Copyright (c) 2026 PNP Labs.

Complete cursor-loop contracts. Exact all-count interfaces are checked with
independent finite-control, error/padding and output-growth regressions.
No runtime execution, request or completeness premise is added.
-/
import PNP.Concrete.CookLevinBuilderCursorLoop

open PNP.Concrete
open PNP.Concrete.CookLevin
open BuilderCursorLoop
open BuilderCursorOutputAdvance (nextOutput)
open WorkMachineProgramGraph (NoRuleAt)

example (request : Option CNFToken) :
    bodyClassify (BuilderCursorTokenRecovery.encodeResult (some request)).val = 0 :=
  bodyClassify_success request

example : bodyClassify (BuilderCursorTokenRecovery.encodeResult none).val = 1 :=
  bodyClassify_missing

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyProgram verifier).rules.Pairwise WorkMachineChain.QueryDistinct ∧
      NoRuleAt (bodyProgram verifier) (bodyProgram verifier).acceptState ∧
      NoRuleAt (bodyProgram verifier) (bodyProgram verifier).rejectState ∧
      (bodyProgram verifier).acceptState ≠ (bodyProgram verifier).rejectState :=
  body_control verifier

example :
    finishProgram.rules.Pairwise WorkMachineChain.QueryDistinct ∧
      NoRuleAt finishProgram finishProgram.acceptState ∧
      NoRuleAt finishProgram finishProgram.rejectState ∧
      finishProgram.acceptState ≠ finishProgram.rejectState :=
  finish_control

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 3 :=
  graph_nodes_length verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed :=
  graph_wellFormed verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    NoRuleAt (machine verifier) (machine verifier).acceptState :=
  noRuleAtAccept verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    NoRuleAt (machine verifier) (machine verifier).rejectState :=
  noRuleAtReject verifier

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  acceptState_ne_rejectState verifier

example (output : List CNFToken) (request : Option CNFToken) :
    (nextOutput output request).length ≤ output.length + 1 :=
  nextOutput_length_le output request

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (completeOutput problem index remaining output).length ≤ output.length + remaining + 1 :=
  completeOutput_length_le problem index remaining output

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + (remaining + 2) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem :=
  body_domain_of_balance problem index remaining hBalance

example {language : Language} (verifier : PolynomialTimeVerifier language) (n : Nat) :
    (stepPolynomial verifier).eval n = (BuilderCursorRemainingOne.rawTimeBound verifier).eval n +
      (BuilderCursorOutputAdvance.rawTimeBound verifier).eval n + 24 :=
  stepPolynomial_eval verifier n

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps
        (initialConfiguration problem index (remaining + 1) output) = some final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + remaining + 1) 0
          (completeOutput problem index remaining output)) ∧
      6 * steps ≤ (remaining + 1) * ((stepPolynomial problem.verifier).eval problem.input.length +
        12 * (output.length + remaining + 1)) :=
  workRun_complete problem index remaining output hBalance

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBalance : index + (remaining + 1) = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (remaining + 1) * ((stepPolynomial problem.verifier).eval problem.input.length +
        12 * (output.length + remaining + 1)) ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index (remaining + 1) output)) =
        encodeWorkConfiguration final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (index + remaining + 1) 0
          (completeOutput problem index remaining output)) :=
  uniform_raw_complete problem index remaining output hBalance

example : bodyClassify 2 = 0 ∧ bodyClassify 5 = 1 := by decide

example (state : Nat) (h : 5 ≤ state) : bodyClassify state = 1 := by
  have hNot : ¬ state < 5 := by omega
  simp only [bodyClassify, if_neg hNot]

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (bodyNode verifier).onAccept = .node guardReference ∧
      (bodyNode verifier).onReject = .reject ∧
      (guardNode verifier).onAccept = .node finishNode.reference ∧
      (guardNode verifier).onReject = .node (bodyNode verifier).reference ∧
      finishNode.onAccept = .accept := ⟨rfl, rfl, rfl, rfl, rfl⟩

example {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).entry = (guardNode verifier).reference ∧
      (graph verifier).nodes = [guardNode verifier, bodyNode verifier, finishNode] := ⟨rfl, rfl⟩

example (output : List CNFToken) :
    BuilderCursorOutputAdvance.nextOutput output none = output := rfl

example (output : List CNFToken) (token : CNFToken) :
    (BuilderCursorOutputAdvance.nextOutput output (some token)).length = output.length + 1 := by
  simp only [BuilderCursorOutputAdvance.nextOutput, List.length_append, List.length_cons, List.length_nil]

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat) (output : List CNFToken) :
    completeOutput problem index 0 output = output ++ [.finish] := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    completeOutput problem index (remaining + 1) output =
      completeOutput problem (index + 1) remaining
        (BuilderCursorOutputAdvance.nextOutput output
          ((BuilderCursorTokenLookup.canonicalResult problem index).getD none)) := rfl

example : finishProgram.rules = BuilderCursorOutputAdvance.continuation.rules ∧
    finishProgram.startState = BuilderCursorOutputAdvance.entry 4 := ⟨rfl, rfl⟩
