/-
Copyright (c) 2026 PNP Labs.
The physical paired-cell branch reads the actual source packet. The three
prefix constraints, finite-family exhaustion, carried metadata and decoded
coordinate are distinct boundaries. All nine final fields must come from the
actual source, selected row and physical request dispatch, including the
remaining-length count and canonical request kind/index.
No supplied selection premise belongs to the complete execution theorem.
-/
import PNP.Concrete.CookLevinBuilderInitialPairedCellSource

namespace PNP.Concrete.CookLevin.BuilderInitialPairedCellSource.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private def data (values : List Nat) {arity : Nat} (i : Fin arity) : Nat := values.getD i.val 0

example : (BuilderRegisterPack.values prefixFields (data [7, 11, 0, 31, 19, 5])) = [19, 3] := by decide
example : (BuilderRegisterPack.values rowFields (data [7, 11, 0, 31, 19, 5, 3, 13, 3, 3, 16])) =
    [7, 11, 0, 31, 16, 5] := by decide
example : (BuilderRegisterPack.values rowFields (data [7, 11, 0, 31, 19, 5, 3, 13, 3, 3, 16])) ≠
    [7, 11, 0, 31, 19, 5] := by decide
example : BuilderRegisterExpression.eval startExpression (data [7, 11, 2, 33, 19, 2]) = 29 := by decide
example : BuilderRegisterExpression.eval startExpression (data [7, 11, 2, 33, 19, 2]) ≠ 22 := by decide
example (n fuel length width offset remaining : Nat) :
    BuilderRegisterExpression.eval startExpression (data [n, fuel, length, width, offset, remaining]) =
      fuel + 2 * n + length + 2 := rfl
example : BuilderRegisterExpression.nodeCount startExpression = 9 := rfl
example : prefixFields.length = 2 := rfl
example : rowFields.length = 6 := rfl
example : decoderFields.length = 7 := rfl
example : BuilderRegisterPack.values decoderFields
    (data [7, 11, 2, 33, 19, 2, 11, 2, 7, 14, 25, 2, 27, 2, 29]) = [7, 11, 2, 33, 2, 29, 19] := by decide
example : BuilderRegisterPack.values decoderFields
    (data [7, 11, 2, 33, 19, 2, 11, 2, 7, 14, 25, 2, 27, 2, 29]) ≠ [7, 11, 2, 33, 19, 29, 2] := by decide

section Source
variable {language : Language} (problem : VerifierTableauProblem language)

example : (graph problem.verifier).nodes.length = 10 := graph_nodes_length problem.verifier
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : (budgetValues problem).length = 3 := budgetValues_length problem
example (index : Nat) : (preparedFrame problem index).length = 6 := preparedFrame_length problem index
example (index : Nat) : (prefixStage problem index).length = 11 := prefixStage_length problem index
example (length offset : Nat) : (decoderFrame problem length offset).length = 15 :=
  decoderFrame_length problem length offset
example : rowCount problem = problem.certificateLimit + 1 := rfl
example : rowCount problem ≠ problem.certificateLimit := by unfold rowCount; omega
example (index : Nat) : preparedFrame problem index =
    [problem.input.length, problem.uniformFuel, 0, problem.dimensions.tapeWidth problem.tableauInputMode,
     coordinate problem index, problem.certificateLimit + 1] := rfl
example (length : Nat) : startValue problem length =
    problem.uniformFuel + 2 * problem.input.length + length + 2 := rfl
example (index remaining : Nat) (hMode : problem.tableauInputMode = .paired) :
    BuilderRegisterExpression.values (budgetExpression problem.verifier)
      (BuilderLiteralArgumentSource.environment problem index remaining .initial 0 []) = budgetValues problem :=
  budget_values problem index remaining hMode
example (index remaining : Nat) :
    BuilderRegisterPack.values (prepareFields problem.verifier)
      (BuilderLiteralArgumentSource.environment problem index remaining .initial 3 (budgetValues problem)) =
      preparedFrame problem index := prepare_values problem index remaining

example (index remaining : Nat) (inside : List WorkSymbol) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) =
      some (finalConfiguration problem index remaining inside) :=
  workRunExact problem index remaining inside hMode
example (index remaining : Nat) (inside : List WorkSymbol) (hMode : problem.tableauInputMode = .paired) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compile_exact problem index remaining inside hMode
example (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape =
      endTape (finalValues problem index remaining) inside [] := final_tape problem index remaining inside
example (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left = [] := final_frontier problem index remaining inside
example (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).state = (machine problem.verifier).acceptState ↔
      (decodedCoordinate problem index).isSome = true := final_accept_iff problem index remaining inside
example (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).state = (machine problem.verifier).rejectState ↔
      decodedCoordinate problem index = none := final_reject_iff problem index remaining inside
example (index : Nat) (hPrefix : coordinate problem index < 3) :
    decodedCoordinate problem index = none := prefix_rejected problem index hPrefix
example (index : Nat) (hZero : coordinate problem index = 0) :
    decodedCoordinate problem index = none := prefix_rejected problem index (by omega)
example (index : Nat) (hOne : coordinate problem index = 1) :
    decodedCoordinate problem index = none := prefix_rejected problem index (by omega)
example (index : Nat) (hTwo : coordinate problem index = 2) :
    decodedCoordinate problem index = none := prefix_rejected problem index (by omega)
example (index : Nat) (hMode : problem.tableauInputMode = .paired)
    (hPadding : problem.pairedCellsWidthDirect ≤ coordinate problem index - 3) :
    decodedCoordinate problem index = none := padding_rejected problem index hMode hPadding
example (index : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, rowFinish problem index = history ++ selectedFrame problem length.val offset :=
  row_found_suffix problem index length offset hFound
example (index remaining : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    finalValues problem index remaining =
      prefixBase problem index remaining ++ rowFinish problem index ++ startValues problem length.val ++
        handoffHistory problem length.val offset ++ requestOutput problem length.val offset :=
  found_output problem index remaining length offset hPrefix hFound
example (index : Nat) (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selection problem index = some (length, offset)) :
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1 <
        problem.dimensions.tapeWidth problem.tableauInputMode ∧
      (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).2 <
        BuilderInitialCellCoordinates.intervalWidth (startValue problem length.val) length.val
          (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1 :=
  decoded_bounds problem index hMode length offset hFound
example (index : Nat) : endpoint problem index =
    if coordinate problem index < 3 then .reject
    else match selection problem index with | none => .reject | some _ => .accept :=
  endpoint_selection problem index

example : (machine problem.verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  rules_pairwise_query_distinct problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).acceptState :=
  noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState :=
  noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState :=
  acceptState_ne_rejectState problem.verifier

example (index remaining : Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (hSpan : (registerWord (sourceFrame problem index remaining)).length ≤ bound.eval inputSize) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanPolynomial problem.verifier bound).eval inputSize ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier bound).eval inputSize :=
  packet_polynomial_bounds problem index remaining bound inputSize hMode hSpan
example (index remaining : Nat) (hMode : problem.tableauInputMode = .paired)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanPolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤
        (rawTimePolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hMode hBody hBalance hRegion

example (length offset : Nat) :
    BuilderRegisterPack.values decoderFields
      (fun i : Fin 15 => (decoderFrame problem length offset)[i.val]?.getD 0) =
      BuilderInitialCellHandoff.frame (metadata problem length) (startValue problem length) offset :=
  decoder_values problem length offset
example (length : Nat) : (metadata problem length).values =
    [problem.input.length, problem.uniformFuel, length,
     problem.dimensions.tapeWidth problem.tableauInputMode + length,
     problem.certificateLimit - length] := metadata_values problem length
example (length : Fin (problem.certificateLimit + 1)) :
    length.val + (metadata problem length.val).remaining = problem.certificateLimit :=
  metadata_certificate_limit problem length
example (length offset : Nat) : (payloadFrame problem length offset).length = 7 :=
  payloadFrame_length problem length offset
example (length offset : Nat) : payloadFrame problem length offset =
    [problem.input.length, problem.uniformFuel, length,
     problem.dimensions.tapeWidth problem.tableauInputMode + length,
     rowCount problem - (length + 1),
     (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1,
     (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2] :=
  payloadFrame_values problem length offset
example (index remaining : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining = history ++ requestFrame problem length.val offset :=
  found_suffix problem index remaining length offset hPrefix hFound
example (index remaining : Nat) :
    match decodedCoordinate problem index with
    | none => True
    | some (length, position, offset) =>
        ∃ history : List Nat, finalValues problem index remaining =
          history ++ [problem.input.length, problem.uniformFuel, length,
            problem.dimensions.tapeWidth problem.tableauInputMode + length,
            rowCount problem - (length + 1), position, offset,
            (BuilderInitialPairedRequest.requestCode (metadata problem length) position).1,
            (BuilderInitialPairedRequest.requestCode (metadata problem length) position).2] :=
  final_uniform_suffix problem index remaining

example : decoderNode.onAccept = .node requestNode.reference := rfl
example : requestNode.onAccept = .accept := rfl
example : requestNode.onReject = .dead := rfl
example : requestNode.program = BuilderInitialPairedRequest.machine := rfl
example (length offset : Nat) : payloadFrame problem length offset =
    BuilderInitialPairedRequest.inputValues (metadata problem length)
      (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1
      (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2 := rfl
example (length offset : Nat) : (requestFrame problem length offset).length = 9 :=
  requestFrame_length problem length offset
example (length offset : Nat) : requestFrame problem length offset =
    [problem.input.length, problem.uniformFuel, length,
     problem.dimensions.tapeWidth problem.tableauInputMode + length,
     rowCount problem - (length + 1),
     (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1,
     (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2,
     (requestCode problem length offset).1, (requestCode problem length offset).2] :=
  requestFrame_values problem length offset
example (length offset : Nat) : requestFrame problem length offset ≠ payloadFrame problem length offset := by
  intro h
  have hLengths := congrArg List.length h
  rw [requestFrame_length, payloadFrame_length] at hLengths
  omega
example (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    requestCode problem length.val offset =
      BuilderInitialPairedRequest.encodeRequest
        (BuilderInitialCellCoordinates.pairedRequest problem.input.length length problem.uniformFuel
          (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1) :=
  request_canonical problem length offset
example (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hCertificate : (requestCode problem length.val offset).1 = 3) :
    (requestCode problem length.val offset).2 < problem.certificateLimit :=
  request_certificate_index_bound problem length offset hCertificate
example (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hZero : problem.certificateLimit = 0) : (requestCode problem length.val offset).1 ≠ 3 := by
  intro hCertificate
  have hBound := request_certificate_index_bound problem length offset hCertificate
  omega
example (index remaining : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining =
      history ++ BuilderInitialPairedRequest.requestValues (metadata problem length.val)
        (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1
        (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).2
        (BuilderInitialPairedRequest.encodeRequest
          (BuilderInitialCellCoordinates.pairedRequest problem.input.length length problem.uniformFuel
            (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1)) :=
  found_canonical_suffix problem index remaining length offset hPrefix hFound

end Source
end PNP.Concrete.CookLevin.BuilderInitialPairedCellSource.Regression
