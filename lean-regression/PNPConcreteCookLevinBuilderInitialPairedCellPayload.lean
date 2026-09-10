/-
Copyright (c) 2026 PNP Labs.
The complete source-to-payload stage derives requests, symbols, dimensions,
literal indices and payloads from actual source input and selection. These
contracts preserve the exact canonical payload and reject the non-cell prefix
and exhaustion without claiming that the remaining formula families are built.
-/
import PNP.Concrete.CookLevinBuilderInitialPairedCellPayload

namespace PNP.Concrete.CookLevin.BuilderInitialPairedCellPayload.Regression
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)
open BuilderInitialPairedCellSource (coordinate selection sourceFrame sourceBound)
open BuilderInitialPairedCellResolution (cell request)

variable {language : Language} (problem : VerifierTableauProblem language)
variable (index remaining : Nat) (output : List CNFToken)
variable (length : Fin (problem.certificateLimit + 1)) (offset : Nat)

example : BuilderInitialPairedLiteralPayload.dataValues (data problem length offset) =
    BuilderInitialPairedCellResolution.resultFrame problem length offset := data_values problem length offset
example : (data problem length offset).code =
    BuilderInitialRequestResolution.symbolCode problem.input (request problem length offset) (cell problem length offset).2 := rfl
example : (data problem length offset).position = (cell problem length offset).1 := rfl
example : (data problem length offset).offset = (cell problem length offset).2 := rfl
example (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    BuilderInitialPairedCellResolution.finalValues problem index remaining =
      sourceHistory problem index remaining ++ BuilderInitialPairedLiteralPayload.dataValues (data problem length offset) :=
  source_suffix problem index remaining length offset hPrefix hFound

example : (graph problem.verifier).nodes.length = 2 := graph_nodes_length problem.verifier
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : (sourceNode problem.verifier).program = BuilderInitialPairedCellResolution.machine problem.verifier := rfl
example : (payloadNode problem.verifier).program =
    BuilderInitialPairedLiteralPayload.machine (BuilderInitialPairedLiteralPayload.stateCount problem.verifier) := rfl
example : (sourceNode problem.verifier).onAccept = .node (payloadNode problem.verifier).reference := rfl
example : (sourceNode problem.verifier).onReject = .reject := rfl
example : (payloadNode problem.verifier).onAccept = .accept := rfl
example : (payloadNode problem.verifier).onReject = .dead := rfl
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
    finalValues problem index remaining = writtenValues problem index remaining length offset :=
  found_output problem index remaining length offset hPrefix hFound
example (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining = history ++ payloadValues problem length offset :=
  found_suffix problem index remaining length offset hPrefix hFound
example (hMode : problem.tableauInputMode = .paired)
    (hFound : selection problem index = some (length, offset)) :
    ∃ position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode),
      position.val = (cell problem length offset).1 ∧
      BuilderInitialConstraintPayload.pairedCellValues problem hMode length position (cell problem length offset).2 =
        some (payloadValues problem length offset) :=
  selected_payload_canonical problem index hMode length offset hFound
example (hMode : problem.tableauInputMode = .paired)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    ∃ (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (payload history : List Nat),
      position.val = (cell problem length offset).1 ∧
      BuilderInitialConstraintPayload.pairedCellValues problem hMode length position (cell problem length offset).2 =
        some payload ∧ finalValues problem index remaining = history ++ payload :=
  found_canonical_suffix problem index remaining hMode length offset hPrefix hFound
example (hMode : problem.tableauInputMode = .paired)
    (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    ∃ (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (payload history : List Nat),
      position.val = (cell problem length offset).1 ∧
      BuilderInitialConstraintPayload.pairedCellValues problem hMode length position (cell problem length offset).2 =
        some payload ∧
      workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
        some
          {state := (machine problem.verifier).acceptState,
           tape := endTape (history ++ payload) (inside problem.input output) []} :=
  source_canonical_payload problem index remaining output hMode length offset hPrefix hFound
example (hMode : problem.tableauInputMode = .paired) :
    if coordinate problem index < 3 then True
    else match selection problem index with
      | none => True
      | some found => ∃ (position : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) (payload history : List Nat),
          position.val = (cell problem found.1 found.2).1 ∧
          BuilderInitialConstraintPayload.pairedCellValues problem hMode found.1 position (cell problem found.1 found.2).2 =
            some payload ∧ finalValues problem index remaining = history ++ payload :=
  final_uniform_suffix problem index remaining hMode

example (hPrefix : coordinate problem index < 3) :
    finalValues problem index remaining = BuilderInitialPairedCellResolution.finalValues problem index remaining :=
  prefix_output problem index remaining hPrefix
example (hFound : selection problem index = none) :
    finalValues problem index remaining = BuilderInitialPairedCellResolution.finalValues problem index remaining :=
  exhausted_output problem index remaining hFound
example (hPrefix : coordinate problem index < 3) :
    workSteps problem index remaining = BuilderInitialPairedCellResolution.workSteps problem index remaining + 1 := by
  simp only [workSteps, if_pos hPrefix, Nat.add_zero]
example (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = none) :
    workSteps problem index remaining = BuilderInitialPairedCellResolution.workSteps problem index remaining + 1 := by
  simp only [workSteps, if_neg hPrefix, hFound, Nat.add_zero]
example (hPrefix : ¬ coordinate problem index < 3) (hFound : selection problem index = some (length, offset)) :
    workSteps problem index remaining = BuilderInitialPairedCellResolution.workSteps problem index remaining + 1 +
      (payloadSteps problem length offset + 1) := by
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

end PNP.Concrete.CookLevin.BuilderInitialPairedCellPayload.Regression
