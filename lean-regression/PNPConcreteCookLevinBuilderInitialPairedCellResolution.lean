/-
Copyright (c) 2026 PNP Labs.
The complete source-to-resolution theorem derives its own canonical request.
No caller-supplied request, bit, history or size certificate is a premise.
Prefix/exhaustion rejection, actual input and prior output preservation, and
full encoded-source execution bounds are checked independently of local cases.
-/
import PNP.Concrete.CookLevinBuilderInitialPairedCellResolution

namespace PNP.Concrete.CookLevin.BuilderInitialPairedCellResolution.Regression
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialPairedCellSource (metadata coordinate selection sourceFrame sourceBound)

variable {language : Language} (problem : VerifierTableauProblem language)
variable (index remaining : Nat) (output : List CNFToken)
variable (length : Fin (problem.certificateLimit + 1)) (offset : Nat)

example : (frame problem length offset).length = 9 := frame_length problem length offset
example : (resultFrame problem length offset).length = 10 := resultFrame_length problem length offset
example : resultFrame problem length offset ≠ frame problem length offset := by
  intro h
  have hLength := congrArg List.length h
  rw [resultFrame_length, frame_length] at hLength
  omega
example : resultFrame problem length offset = frame problem length offset ++
    [BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2] := resultFrame_values problem length offset
example : BuilderInitialPairedCellSource.requestCode problem length.val offset =
    BuilderInitialPairedRequest.encodeRequest (request problem length offset) :=
  request_derived problem length offset
example : BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
    (cell problem length offset).2 ≤ 2 := resolved_symbol_bound problem length offset
example (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    BuilderInitialPairedCellSource.finalValues problem index remaining =
      sourcePrefix problem index remaining ++ frame problem length offset :=
  source_suffix problem index remaining length offset hPrefix hFound

example : (graph problem.verifier).nodes.length = 2 := graph_nodes_length problem.verifier
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : (sourceNode problem.verifier).program = BuilderInitialPairedCellSource.machine problem.verifier := rfl
example : resolveNode.program = BuilderInitialRequestResolution.machine := rfl
example : (sourceNode problem.verifier).onAccept = .node resolveNode.reference := rfl
example : (sourceNode problem.verifier).onReject = .reject := rfl
example : resolveNode.onAccept = .accept := rfl
example : resolveNode.onReject = .dead := rfl
example : (graph problem.verifier).entry = (sourceNode problem.verifier).reference := rfl
example : (initialConfiguration problem index remaining output).tape =
    endTape (sourceFrame problem index remaining) (inside problem.input output) [] := rfl
example (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output hMode
example (hMode : problem.tableauInputMode = .paired) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compile_exact problem index remaining output hMode
example : (finalConfiguration problem index remaining output).tape =
    endTape (finalValues problem index remaining) (inside problem.input output) [] :=
  final_tape problem index remaining output
example : (finalConfiguration problem index remaining output).tape.left = [] :=
  final_frontier problem index remaining output
example : BuilderInitialPairedCellSource.endpoint problem index =
    if coordinate problem index < 3 then .reject
    else match selection problem index with | none => .reject | some _ => .accept :=
  endpoint_selection problem index
example : (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState ↔
    (BuilderInitialPairedCellSource.decodedCoordinate problem index).isSome = true :=
  final_accept_iff problem index remaining output
example : (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState ↔
    BuilderInitialPairedCellSource.decodedCoordinate problem index = none :=
  final_reject_iff problem index remaining output
example (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    finalValues problem index remaining = resolvedValues problem index remaining length offset :=
  found_output problem index remaining length offset hPrefix hFound
example (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining = history ++ resultFrame problem length offset :=
  found_suffix problem index remaining length offset hPrefix hFound
example : if coordinate problem index < 3 then True
    else match selection problem index with
      | none => True
      | some found => ∃ history : List Nat, finalValues problem index remaining =
          history ++ resultFrame problem found.1 found.2 :=
  final_uniform_suffix problem index remaining
example (hPrefix : coordinate problem index < 3) :
    finalValues problem index remaining = BuilderInitialPairedCellSource.finalValues problem index remaining :=
  prefix_output problem index remaining hPrefix
example (hFound : selection problem index = none) :
    finalValues problem index remaining = BuilderInitialPairedCellSource.finalValues problem index remaining :=
  exhausted_output problem index remaining hFound
example (hPrefix : coordinate problem index < 3) :
    workSteps problem index remaining = BuilderInitialPairedCellSource.workSteps problem index remaining + 1 := by
  simp only [workSteps, if_pos hPrefix, Nat.add_zero]
example (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = none) :
    workSteps problem index remaining = BuilderInitialPairedCellSource.workSteps problem index remaining + 1 := by
  simp only [workSteps, if_neg hPrefix, hFound, Nat.add_zero]
example (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    workSteps problem index remaining = BuilderInitialPairedCellSource.workSteps problem index remaining + 1 +
      (resolutionSteps problem index remaining length offset + 1) := by
  simp only [workSteps, if_neg hPrefix, hFound]

example : (machine problem.verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).acceptState :=
  noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState :=
  noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState :=
  acceptState_ne_rejectState problem.verifier
example (bound : NatPolynomial) (inputSize : Nat) (hMode : problem.tableauInputMode = .paired)
    (hSpan : (registerWord (sourceFrame problem index remaining)).length ≤ bound.eval inputSize) :
    (registerWord (finalValues problem index remaining)).length ≤ (spanPolynomial problem.verifier bound).eval inputSize ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier bound).eval inputSize :=
  packet_polynomial_bounds problem index remaining bound inputSize hMode hSpan
example (hMode : problem.tableauInputMode = .paired)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanPolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤
        (rawTimePolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hMode hBody hBalance hRegion

example (requestedIndex : Nat) (hRequest : request problem length offset = .sourceBit requestedIndex) :
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2 = BuilderIndexedInputRead.resultCode problem.input[requestedIndex]? := by
  rw [hRequest]
  rfl
example (hRequest : request problem length offset = .blank) :
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2 = 0 := by
  rw [hRequest]
  rfl
example (value : Bool) (hRequest : request problem length offset = .fixed value) :
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2 = (if value then 2 else 1) := by
  rw [hRequest]
  rfl

example (bitIndex : Fin problem.certificateLimit)
    (hRequest : request problem length offset = .certificate bitIndex)
    (hOffset : (cell problem length offset).2 = 0) :
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2 = 2 := by
  rw [hRequest, hOffset]
  rfl
example (bitIndex : Fin problem.certificateLimit)
    (hRequest : request problem length offset = .certificate bitIndex)
    (hOffset : (cell problem length offset).2 = 1) :
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset)
      (cell problem length offset).2 = 1 := by
  rw [hRequest, hOffset]
  rfl

end PNP.Concrete.CookLevin.BuilderInitialPairedCellResolution.Regression
