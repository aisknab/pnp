/-
Copyright (c) 2026 PNP Labs.

Actual paired initial-region packet to canonical row, cell and request fields.
The finite program reads source metadata, removes the three non-cell prefix
entries, runs the complete row selector and metadata-preserving cell handoff,
then physically derives the paired request. Every success leaves nine uniform
source-derived fields, including the request kind and index rather than a
supplied source bit. No runtime length, offset, family, history size or branch
answer builds control. Indexed reads, payloads and formula integration remain
downstream.
-/

import PNP.Concrete.CookLevinBuilderLiteralArgumentSource
import PNP.Concrete.CookLevinBuilderInitialPairedRequest
import PNP.Concrete.CookLevinBuilderInitialRowCarry

namespace PNP.Concrete.CookLevin.BuilderInitialPairedCellSource

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)
open BuilderLiteralArgumentSource
  (field field_eval inputValues inputCount environment environment_values referenceValue)

private def view {arity : Nat} (data : List Nat) (index : Fin arity) : Nat :=
  data[index.val]?.getD 0

private theorem view_ofFn {arity : Nat} (data : List Nat) (hLength : data.length = arity) :
    List.ofFn (view data : Fin arity → Nat) = data := by
  subst arity
  have h : (view data : Fin data.length → Nat) = fun index => data[index.val] := by
    funext index
    simp only [view, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

def coordinate {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderConstraintRegionSource.localCoordinate problem index .initial

def rowCount {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.certificateLimit + 1

def sourceFrame {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  inputValues problem index remaining .initial []

def budgetExpression {language : Language} (verifier : PolynomialTimeVerifier language) :
    BuilderRegisterExpression.Expr (inputCount verifier .initial 0) :=
  .binary .add (field verifier .initial 0 (.source .certificateWidth)).expression (.constant 1)

def budgetValues {language : Language} (problem : VerifierTableauProblem language) : List Nat :=
  [problem.certificateLimit, 1, rowCount problem]

def prepareFields {language : Language} (verifier : PolynomialTimeVerifier language) :
    List (BuilderRegisterPack.Field (inputCount verifier .initial 3)) :=
  [field verifier .initial 3 (.source .inputLength),
   field verifier .initial 3 (.source .fuel),
   .constant 0,
   field verifier .initial 3 (.source .tapeWidth),
   field verifier .initial 3 .quotient,
   field verifier .initial 3 (.retained ⟨2, by decide⟩)]

def preparedFrame {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderInitialRowCarry.frame problem.input.length problem.uniformFuel 0
    (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index) (rowCount problem)

def prefixFields : List (BuilderRegisterPack.Field 6) :=
  [.argument ⟨4, by decide⟩, .constant 3]

def prefixStage {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  preparedFrame problem index ++ BuilderInitialCellDecoder.comparisonValues (coordinate problem index) 3

def rowFields : List (BuilderRegisterPack.Field 11) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨10, by decide⟩, .argument ⟨5, by decide⟩]

def prefixBase {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  sourceFrame problem index remaining ++ budgetValues problem ++ prefixStage problem index

def selection {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Fin (problem.certificateLimit + 1) × Nat) :=
  BuilderInitialLengthSelection.selectedLength problem (coordinate problem index - 3)

def rowFinish {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  BuilderInitialRowCarry.finishValues (rowCount problem) problem.input.length problem.uniformFuel 0
    (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3)

def selectedFrame {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : List Nat :=
  BuilderInitialRowCarry.frame problem.input.length problem.uniformFuel length
    (problem.dimensions.tapeWidth problem.tableauInputMode + length) offset (rowCount problem - (length + 1))

def startExpression : BuilderRegisterExpression.Expr 6 :=
  .binary .add
    (.binary .add
      (.binary .add (.argument ⟨1, by decide⟩)
        (.binary .mul (.constant 2) (.argument ⟨0, by decide⟩)))
      (.argument ⟨2, by decide⟩))
    (.constant 2)

def startValue {language : Language} (problem : VerifierTableauProblem language) (length : Nat) : Nat :=
  BuilderInitialCellCoordinates.certificateStart problem.input.length length problem.uniformFuel

def startValues {language : Language} (problem : VerifierTableauProblem language) (length : Nat) : List Nat :=
  [problem.uniformFuel, 2, problem.input.length, 2 * problem.input.length,
   problem.uniformFuel + 2 * problem.input.length, length,
   problem.uniformFuel + 2 * problem.input.length + length, 2, startValue problem length]

def metadata {language : Language} (problem : VerifierTableauProblem language)
    (length : Nat) : BuilderInitialCellHandoff.Metadata :=
  {inputLength := problem.input.length, fuel := problem.uniformFuel, length := length,
   rowWidth := problem.dimensions.tapeWidth problem.tableauInputMode + length,
   remaining := rowCount problem - (length + 1)}

def payloadFrame {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : List Nat :=
  BuilderInitialCellHandoff.carriedValues (metadata problem length) (startValue problem length) offset

def handoffHistory {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : List Nat :=
  BuilderInitialCellHandoff.resultFrame
    (BuilderInitialCellHandoff.selectedBranch (metadata problem length) (startValue problem length) offset)
    (metadata problem length) (startValue problem length) offset

def requestCode {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : Nat × Nat :=
  BuilderInitialPairedRequest.requestCode (metadata problem length)
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1

def requestFrame {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : List Nat :=
  BuilderInitialPairedRequest.requestValues (metadata problem length)
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2
    (requestCode problem length offset)

def requestOutput {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : List Nat :=
  BuilderInitialPairedRequest.outputValues (metadata problem length)
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2

private theorem handoff_request_frame {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) :
    BuilderInitialCellHandoff.carriedValues (metadata problem length) (startValue problem length) offset =
      BuilderInitialPairedRequest.inputValues (metadata problem length)
        (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1
        (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2 := rfl

/-- The handoff pack reads the actual fifteen-register row/start frame. -/
def decoderFields : List (BuilderRegisterPack.Field 15) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨5, by decide⟩, .argument ⟨14, by decide⟩,
   .argument ⟨4, by decide⟩]

def decoderFrame {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : List Nat :=
  selectedFrame problem length offset ++ startValues problem length

theorem budgetValues_length {language : Language} (problem : VerifierTableauProblem language) :
    (budgetValues problem).length = 3 := rfl

theorem preparedFrame_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (preparedFrame problem index).length = 6 := rfl

theorem prefixStage_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (prefixStage problem index).length = 11 := rfl

theorem decoderFrame_length {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) :
    (decoderFrame problem length offset).length = 15 := rfl

private theorem certificate_width {language : Language} (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    problem.layout.certificateBitWidth = problem.certificateLimit := by
  simp only [VerifierTableauProblem.layout, VariableLayout.certificateBitWidth, hMode]
  rfl

theorem budget_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hMode : problem.tableauInputMode = .paired) :
    BuilderRegisterExpression.values (budgetExpression problem.verifier)
      (environment problem index remaining .initial 0 []) = budgetValues problem := by
  have hWidth := certificate_width problem hMode
  have hEval : BuilderRegisterExpression.eval
      (field problem.verifier .initial 0 (.source .certificateWidth)).expression
      (environment problem index remaining .initial 0 []) = problem.certificateLimit :=
    (field_eval problem index remaining .initial 0 [] (.source .certificateWidth)).trans hWidth
  simp only [budgetExpression, BuilderRegisterExpression.values, BuilderRegisterPack.Field.expression_values,
    BuilderRegisterExpression.eval, RegisterBinary.value, hEval, BuilderRegisterPack.Field.eval,
    field_eval, referenceValue, BuilderLiteralArgumentSource.sourceValue, hWidth,
    budgetValues, rowCount, List.cons_append, List.nil_append]

theorem prepare_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterPack.values (prepareFields problem.verifier)
      (environment problem index remaining .initial 3 (budgetValues problem)) = preparedFrame problem index := by
  simp only [prepareFields, BuilderRegisterPack.values, List.map_cons, List.map_nil, field_eval]
  rfl

private theorem prefix_values {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    BuilderRegisterPack.values prefixFields (view (preparedFrame problem index)) = [coordinate problem index, 3] := rfl

private theorem row_values {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hPrefix : ¬ coordinate problem index < 3) :
    BuilderRegisterPack.values rowFields (view (prefixStage problem index)) =
      BuilderInitialRowCarry.frame problem.input.length problem.uniformFuel 0
        (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3) (rowCount problem) := by
  change [problem.input.length, problem.uniformFuel, 0, problem.dimensions.tapeWidth problem.tableauInputMode,
    BuilderInitialCellDecoder.residual (coordinate problem index) 3, rowCount problem] = _
  simp only [BuilderInitialCellDecoder.residual, if_neg hPrefix, BuilderInitialRowCarry.frame]

private theorem start_values {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) :
    BuilderRegisterExpression.values startExpression (view (selectedFrame problem length offset)) =
      startValues problem length := rfl

theorem decoder_values {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) :
    BuilderRegisterPack.values decoderFields (view (decoderFrame problem length offset)) =
      BuilderInitialCellHandoff.frame (metadata problem length) (startValue problem length) offset := rfl

theorem payloadFrame_length {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : (payloadFrame problem length offset).length = 7 := rfl

theorem payloadFrame_values {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) :
    payloadFrame problem length offset =
      [problem.input.length, problem.uniformFuel, length,
       problem.dimensions.tapeWidth problem.tableauInputMode + length,
       rowCount problem - (length + 1),
       (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1,
       (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2] := rfl

theorem requestFrame_length {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) : (requestFrame problem length offset).length = 9 := rfl

theorem requestFrame_values {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) :
    requestFrame problem length offset =
      [problem.input.length, problem.uniformFuel, length,
       problem.dimensions.tapeWidth problem.tableauInputMode + length,
       rowCount problem - (length + 1),
       (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1,
       (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2,
       (requestCode problem length offset).1, (requestCode problem length offset).2] := rfl

theorem request_canonical {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat) :
    requestCode problem length.val offset =
      BuilderInitialPairedRequest.encodeRequest
        (BuilderInitialCellCoordinates.pairedRequest problem.input.length length problem.uniformFuel
          (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1) :=
  BuilderInitialPairedRequest.request_canonical (metadata problem length.val) length _ rfl

theorem request_certificate_index_bound {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hCertificate : (requestCode problem length.val offset).1 = 3) :
    (requestCode problem length.val offset).2 < problem.certificateLimit :=
  BuilderInitialPairedRequest.certificate_index_bound (metadata problem length.val) length _ rfl hCertificate

theorem metadata_values {language : Language} (problem : VerifierTableauProblem language) (length : Nat) :
    (metadata problem length).values =
      [problem.input.length, problem.uniformFuel, length,
       problem.dimensions.tapeWidth problem.tableauInputMode + length,
       problem.certificateLimit - length] := by
  have hRemaining : rowCount problem - (length + 1) = problem.certificateLimit - length := by
    unfold rowCount
    omega
  simp only [metadata, BuilderInitialCellHandoff.Metadata.values, hRemaining]

theorem metadata_certificate_limit {language : Language} (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) :
    length.val + (metadata problem length.val).remaining = problem.certificateLimit := by
  have hLength := length.isLt
  change length.val + (rowCount problem - (length.val + 1)) = problem.certificateLimit
  unfold rowCount
  omega

theorem row_found_suffix {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, rowFinish problem index = history ++ selectedFrame problem length.val offset := by
  obtain ⟨history, h⟩ := BuilderInitialRowCarry.found_suffix (rowCount problem) problem.input.length
    problem.uniformFuel 0 (problem.dimensions.tapeWidth problem.tableauInputMode)
    (coordinate problem index - 3) length offset hFound
  exact ⟨history, by simpa only [Nat.zero_add, rowFinish, selectedFrame] using h⟩

def decodedCoordinate {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Nat × Nat × Nat) :=
  if coordinate problem index < 3 then none
  else (selection problem index).map (fun found =>
    (found.1.val, BuilderInitialCellSelection.cellCoordinate (startValue problem found.1.val) found.1.val found.2))

def endpoint {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Endpoint :=
  if coordinate problem index < 3 then .reject
  else BuilderInitialRowLoop.endpoint (rowCount problem)
    (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3)

def tailValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  match selection problem index with
  | none => []
  | some found => startValues problem found.1.val ++ handoffHistory problem found.1.val found.2 ++
      requestOutput problem found.1.val found.2

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  prefixBase problem index remaining ++
    if coordinate problem index < 3 then [] else rowFinish problem index ++ tailValues problem index

def requestNode : Node :=
  {name := 9, program := BuilderInitialPairedRequest.machine, onAccept := .accept, onReject := .dead}

def decoderNode : Node :=
  {name := 8, program := BuilderInitialCellHandoff.machine, onAccept := .node requestNode.reference, onReject := .dead}

def decoderPrepareNode : Node :=
  {name := 7, program := BuilderRegisterPack.machine decoderFields 0, onAccept := .node decoderNode.reference, onReject := .dead}

def startNode : Node :=
  {name := 6, program := BuilderRegisterExpression.machine startExpression 0, onAccept := .node decoderPrepareNode.reference, onReject := .dead}

def rowNode : Node :=
  {name := 5, program := BuilderInitialRowCarry.machine, onAccept := .node startNode.reference, onReject := .reject}

def rowPrepareNode : Node :=
  {name := 4, program := BuilderRegisterPack.machine rowFields 0, onAccept := .node rowNode.reference, onReject := .dead}

def compareNode : Node :=
  {name := 3, program := BuilderRegisterCompareResidual.machine, onAccept := .reject, onReject := .node rowPrepareNode.reference}

def prefixNode : Node :=
  {name := 2, program := BuilderRegisterPack.machine prefixFields 0, onAccept := .node compareNode.reference, onReject := .dead}

def prepareNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 1, program := BuilderRegisterPack.machine (prepareFields verifier) 0, onAccept := .node prefixNode.reference, onReject := .dead}

def budgetNode {language : Language} (verifier : PolynomialTimeVerifier language) : Node :=
  {name := 0, program := BuilderRegisterExpression.machine (budgetExpression verifier) 0, onAccept := .node (prepareNode verifier).reference, onReject := .dead}

def graph {language : Language} (verifier : PolynomialTimeVerifier language) : Graph :=
  {nodes := [budgetNode verifier, prepareNode verifier, prefixNode, compareNode, rowPrepareNode,
    rowNode, startNode, decoderPrepareNode, decoderNode, requestNode], entry := (budgetNode verifier).reference}
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph verifier)

theorem graph_nodes_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).nodes.length = 10 := rfl

private theorem budget_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    budgetNode verifier ∈ (graph verifier).nodes := List.Mem.head _

private theorem prepare_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    prepareNode verifier ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.head _)

private theorem prefix_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    prefixNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

private theorem compare_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    compareNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem rowPrepare_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    rowPrepareNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private theorem row_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    rowNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private theorem start_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    startNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private theorem decoderPrepare_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    decoderPrepareNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

private theorem decoder_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    decoderNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

private theorem request_mem {language : Language} (verifier : PolynomialTimeVerifier language) :
    requestNode ∈ (graph verifier).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0,
    BuilderRegisterPack.noRuleAtAccept fields 0, BuilderRegisterPack.noRuleAtReject fields 0,
    BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩

private theorem expression_good {arity : Nat} (expression : BuilderRegisterExpression.Expr arity) :
    Good (BuilderRegisterExpression.machine expression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression 0,
    BuilderRegisterExpression.noRuleAtAccept expression 0, BuilderRegisterExpression.noRuleAtReject expression 0,
    BuilderRegisterExpression.acceptState_ne_rejectState expression 0⟩

private theorem comparison_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct,
    BuilderRegisterCompareResidual.noRuleAtAccept, BuilderRegisterCompareResidual.noRuleAtReject,
    BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩

private theorem row_good : Good BuilderInitialRowCarry.machine :=
  ⟨BuilderInitialRowCarry.rules_pairwise_query_distinct, BuilderInitialRowCarry.noRuleAtAccept,
    BuilderInitialRowCarry.noRuleAtReject, BuilderInitialRowCarry.acceptState_ne_rejectState⟩
private theorem decoder_good : Good BuilderInitialCellHandoff.machine :=
  ⟨BuilderInitialCellHandoff.rules_pairwise_query_distinct, BuilderInitialCellHandoff.noRuleAtAccept,
    BuilderInitialCellHandoff.noRuleAtReject, BuilderInitialCellHandoff.acceptState_ne_rejectState⟩

private theorem request_good : Good BuilderInitialPairedRequest.machine :=
  ⟨BuilderInitialPairedRequest.rules_pairwise_query_distinct, BuilderInitialPairedRequest.noRuleAtAccept,
    BuilderInitialPairedRequest.noRuleAtReject, BuilderInitialPairedRequest.acceptState_ne_rejectState⟩

theorem graph_wellFormed {language : Language} (verifier : PolynomialTimeVerifier language) :
    (graph verifier).WellFormed := by
  have hNames : ((graph verifier).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact expression_good (budgetExpression verifier)
    · exact pack_good (prepareFields verifier)
    · exact pack_good prefixFields
    · exact comparison_good
    · exact pack_good rowFields
    · exact row_good
    · exact expression_good startExpression
    · exact pack_good decoderFields
    · exact decoder_good
    · exact request_good
  · exact ⟨budgetNode verifier, budget_mem verifier, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨prepareNode verifier, prepare_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨prefixNode, prefix_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨compareNode, compare_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨rowPrepareNode, rowPrepare_mem verifier, rfl, rfl⟩⟩
    · exact ⟨⟨rowNode, row_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨startNode, start_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨decoderPrepareNode, decoderPrepare_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨decoderNode, decoder_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨requestNode, request_mem verifier, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private theorem pack_run {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterPack.machine fields 0)
      (BuilderRegisterPack.workSteps fields (view data) [])
      (workStartConfiguration (BuilderRegisterPack.machine fields 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterPack.machine fields 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterPack.values fields (view data)) inside [] } := by
  have h := BuilderRegisterPack.workRunExact fields 0 older (view data) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    view_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem expression_run {arity : Nat} (expression : BuilderRegisterExpression.Expr arity)
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterExpression.machine expression 0)
      (BuilderRegisterExpression.workSteps expression (view data) [])
      (workStartConfiguration (BuilderRegisterExpression.machine expression 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine expression 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterExpression.values expression (view data)) inside [] } := by
  have h := BuilderRegisterExpression.workRunExact expression 0 older (view data) [] inside [] rfl
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    view_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem pack_bounds {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterPack.values fields (view data))).length ≤
        (BuilderRegisterPack.spanPolynomial fields bound).eval inputLength ∧
      6 * BuilderRegisterPack.workSteps fields (view data) [] ≤
        (BuilderRegisterPack.rawTimePolynomial fields bound).eval inputLength := by
  have h := BuilderRegisterPack.source_polynomial_bounds fields bound inputLength older (view data) [] (by
    simpa only [view_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [view_ofFn data hLength, List.append_nil] using h

private theorem expression_bounds {arity : Nat} (expression : BuilderRegisterExpression.Expr arity)
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterExpression.values expression (view data))).length ≤
        (BuilderRegisterExpression.spanPolynomial expression bound).eval inputLength ∧
      6 * BuilderRegisterExpression.workSteps expression (view data) [] ≤
        (BuilderRegisterExpression.rawTimePolynomial expression bound).eval inputLength := by
  have h := BuilderRegisterExpression.source_polynomial_bounds expression bound inputLength older (view data) [] (by
    simpa only [view_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [view_ofFn data hLength, List.append_nil] using h

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

private theorem comparison_run (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? BuilderRegisterCompareResidual.machine
      (BuilderRegisterCompareResidual.workSteps coordinate boundary)
      (workStartConfiguration BuilderRegisterCompareResidual.machine (endTape (older ++ [coordinate, boundary]) inside [])) =
      some {
        state := if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
          else BuilderRegisterCompareResidual.machine.rejectState
        tape := endTape (older ++ BuilderInitialCellDecoder.comparisonValues coordinate boundary) inside [] } := by
  have hState : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).state =
      if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
      else BuilderRegisterCompareResidual.machine.rejectState := by
    by_cases hLess : coordinate < boundary
    · rw [if_pos hLess]
      exact (BuilderRegisterCompareResidual.final_accept_iff coordinate boundary older inside []).mpr hLess
    · rw [if_neg hLess]
      exact (BuilderRegisterCompareResidual.final_reject_iff coordinate boundary older inside []).mpr (by omega)
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).tape =
      endTape (older ++ BuilderInitialCellDecoder.comparisonValues coordinate boundary) inside [] := by
    rw [BuilderRegisterCompareResidual.final_tape, BuilderInitialCellDecoder.comparisonValues_eq]
    simp only [BuilderRegisterCompareResidual.outputValues, BuilderRegisterCompareResidual.resultBoundary_eq,
      BuilderRegisterCompareResidual.resultCoordinate_eq, List.drop_nil, List.append_assoc]
  have h := BuilderRegisterCompareResidual.workRunExact coordinate boundary older inside []
  rw [configuration_eq_of_fields _ _ _ hState hTape] at h
  exact h

def budgetSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterExpression.workSteps (budgetExpression problem.verifier)
    (environment problem index remaining .initial 0 []) []
def prepareSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterPack.workSteps (prepareFields problem.verifier)
    (environment problem index remaining .initial 3 (budgetValues problem)) []
def prefixSteps {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderRegisterPack.workSteps prefixFields (view (preparedFrame problem index)) []
def rowPrepareSteps {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderRegisterPack.workSteps rowFields (view (prefixStage problem index)) []
def rowSteps {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  BuilderInitialRowCarry.workSteps (rowCount problem) problem.input.length problem.uniformFuel 0
    (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3)
def startSteps {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) : Nat :=
  BuilderRegisterExpression.workSteps startExpression (view (selectedFrame problem length offset)) []
def decoderPrepareSteps {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) : Nat :=
  BuilderRegisterPack.workSteps decoderFields (view (decoderFrame problem length offset)) []
def requestSteps {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) : Nat :=
  BuilderInitialPairedRequest.workSteps (metadata problem length)
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2
def decodeSteps {language : Language} (problem : VerifierTableauProblem language) (length offset : Nat) : Nat :=
  startSteps problem length offset + 1 +
    (decoderPrepareSteps problem length offset + 1 +
      (BuilderInitialCellHandoff.workSteps (metadata problem length) (startValue problem length) offset + 1 +
        (requestSteps problem length offset + 1)))
def selectedSteps {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  match selection problem index with
  | none => 0
  | some found => decodeSteps problem found.1.val found.2
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  budgetSteps problem index remaining + 1 +
    (prepareSteps problem index remaining + 1 +
      (prefixSteps problem index + 1 +
        (BuilderRegisterCompareResidual.workSteps (coordinate problem index) 3 + 1 +
          if coordinate problem index < 3 then 0 else
            rowPrepareSteps problem index + 1 + (rowSteps problem index + 1 + selectedSteps problem index))))

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (sourceFrame problem index remaining) inside [])
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration (endpoint problem index)
    (endTape (finalValues problem index remaining) inside [])

private theorem budget_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (BuilderRegisterExpression.machine (budgetExpression problem.verifier) 0)
      (budgetSteps problem index remaining)
      (workStartConfiguration (BuilderRegisterExpression.machine (budgetExpression problem.verifier) 0)
        (endTape (sourceFrame problem index remaining) inside [])) =
      some {
        state := (BuilderRegisterExpression.machine (budgetExpression problem.verifier) 0).acceptState
        tape := endTape (sourceFrame problem index remaining ++ budgetValues problem) inside [] } := by
  have h := BuilderRegisterExpression.workRunExact (budgetExpression problem.verifier) 0 []
    (environment problem index remaining .initial 0 []) [] inside [] rfl
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    environment_values problem index remaining .initial 0 [] rfl, budget_values problem index remaining hMode,
    List.nil_append, List.append_nil, List.drop_nil, sourceFrame, budgetSteps] using h

private theorem prepare_run {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    workRunExact? (BuilderRegisterPack.machine (prepareFields problem.verifier) 0)
      (prepareSteps problem index remaining)
      (workStartConfiguration (BuilderRegisterPack.machine (prepareFields problem.verifier) 0)
        (endTape (sourceFrame problem index remaining ++ budgetValues problem) inside [])) =
      some {
        state := (BuilderRegisterPack.machine (prepareFields problem.verifier) 0).acceptState
        tape := endTape (sourceFrame problem index remaining ++ budgetValues problem ++ preparedFrame problem index) inside [] } := by
  have h := BuilderRegisterPack.workRunExact (prepareFields problem.verifier) 0 []
    (environment problem index remaining .initial 3 (budgetValues problem)) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_values problem index remaining .initial 3 (budgetValues problem) rfl,
    prepare_values, List.nil_append, List.append_nil, List.drop_nil, sourceFrame, inputValues, prepareSteps] using h

private theorem decoder_path {language : Language} (problem : VerifierTableauProblem language)
    (length offset : Nat) (older : List Nat) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node startNode.reference) .accept (decodeSteps problem length offset)
      (endTape (older ++ selectedFrame problem length offset) inside [])
      (endTape (older ++ selectedFrame problem length offset ++ startValues problem length ++
        handoffHistory problem length offset ++ requestOutput problem length offset) inside []) := by
  have hRequest := BuilderInitialPairedRequest.workRunExact (metadata problem length)
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).1
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length) length offset).2
    (older ++ decoderFrame problem length offset ++ handoffHistory problem length offset) inside
  simp only [BuilderInitialPairedRequest.initialConfiguration, BuilderInitialPairedRequest.finalConfiguration,
    handoffHistory, List.append_assoc] at hRequest
  have hR := AcceptPath.step requestNode .accept _ 0 _ _ _ (request_mem problem.verifier) hRequest (.terminal .accept _)
  have hDecoder := BuilderInitialCellHandoff.workRunExact (metadata problem length) (startValue problem length) offset
    (older ++ decoderFrame problem length offset) inside
  simp only [BuilderInitialCellHandoff.initialConfiguration, BuilderInitialCellHandoff.finalConfiguration,
    BuilderInitialCellHandoff.outputValues, handoff_request_frame, List.append_assoc] at hDecoder
  have hD := AcceptPath.step decoderNode .accept _ _ _ _ _ (decoder_mem problem.verifier) hDecoder hR
  have hPack := pack_run decoderFields (decoderFrame problem length offset) older inside rfl
  rw [decoder_values] at hPack
  simp only [List.append_assoc] at hPack
  have hP := AcceptPath.step decoderPrepareNode .accept _ _ _ _ _ (decoderPrepare_mem problem.verifier) hPack hD
  have hStart := expression_run startExpression (selectedFrame problem length offset) older inside rfl
  rw [start_values] at hStart
  simp only [List.append_assoc] at hStart
  have hS := AcceptPath.step startNode .accept _ _ _ _ _ (start_mem problem.verifier) hStart hP
  simpa only [decodeSteps, startSteps, decoderPrepareSteps, requestSteps, decoderFrame,
    handoffHistory, requestOutput, List.append_assoc, Nat.add_zero] using hS

private theorem selection_eq_locate {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    selection problem index = BuilderInitialLengthSelection.locate (rowCount problem)
      (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3) := by
  unfold selection BuilderInitialLengthSelection.selectedLength rowCount
  rfl

private theorem row_path {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    AcceptPath (graph problem.verifier) (.node rowNode.reference)
      (BuilderInitialRowLoop.endpoint (rowCount problem) (problem.dimensions.tapeWidth problem.tableauInputMode)
        (coordinate problem index - 3))
      (rowSteps problem index + 1 + selectedSteps problem index)
      (endTape (prefixBase problem index remaining ++
        BuilderInitialRowCarry.frame problem.input.length problem.uniformFuel 0
          (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3) (rowCount problem)) inside [])
      (endTape (prefixBase problem index remaining ++ rowFinish problem index ++ tailValues problem index) inside []) := by
  have hRow : workRunExact? BuilderInitialRowCarry.machine (rowSteps problem index)
      (workStartConfiguration BuilderInitialRowCarry.machine
        (endTape (prefixBase problem index remaining ++
          BuilderInitialRowCarry.frame problem.input.length problem.uniformFuel 0
            (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3) (rowCount problem)) inside [])) =
      some (WorkMachineProgramGraph.endpointConfiguration
        (match selection problem index with | none => .reject | some _ => .accept)
        (endTape (prefixBase problem index remaining ++ rowFinish problem index) inside [])) := by
    have h := BuilderInitialRowCarry.workRunExact (rowCount problem) problem.input.length
      problem.uniformFuel 0 (problem.dimensions.tapeWidth problem.tableauInputMode)
      (coordinate problem index - 3) (prefixBase problem index remaining) inside
    simp only [BuilderInitialRowCarry.initialConfiguration, BuilderInitialRowCarry.finalConfiguration,
      BuilderInitialRowLoop.endpoint_eq_locate, rowSteps, rowFinish, ← selection_eq_locate] at h ⊢
    cases hFound : selection problem index <;> simpa only [hFound] using h
  rw [BuilderInitialRowLoop.endpoint_eq_locate, ← selection_eq_locate]
  cases hFound : selection problem index with
  | none =>
      simp only [hFound, selectedSteps, tailValues, List.append_nil] at hRow ⊢
      have h := AcceptPath.stepReject rowNode .reject _ 0 _ _ _ (row_mem problem.verifier) hRow (.terminal .reject _)
      simpa only [Nat.add_zero] using h
  | some found =>
      rcases found with ⟨length, offset⟩
      obtain ⟨history, hHistory⟩ := row_found_suffix problem index length offset hFound
      simp only [hFound, selectedSteps, tailValues] at hRow ⊢
      have hTail := decoder_path problem length.val offset (prefixBase problem index remaining ++ history) inside
      rw [hHistory] at hRow ⊢
      simp only [List.append_assoc] at hRow hTail ⊢
      have h := AcceptPath.step rowNode .accept _ _ _ _ _ (row_mem problem.verifier) hRow hTail
      simpa only [List.append_assoc] using h

/-- Every runtime selection is performed by the fixed program from written source cells. -/
theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) (hMode : problem.tableauInputMode = .paired) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside) =
      some (finalConfiguration problem index remaining inside) := by
  have hCompare : workRunExact? BuilderRegisterCompareResidual.machine
      (BuilderRegisterCompareResidual.workSteps (coordinate problem index) 3)
      (workStartConfiguration BuilderRegisterCompareResidual.machine
        (endTape (sourceFrame problem index remaining ++ budgetValues problem ++
          preparedFrame problem index ++ [coordinate problem index, 3]) inside [])) =
      some {
        state := if coordinate problem index < 3 then BuilderRegisterCompareResidual.machine.acceptState
          else BuilderRegisterCompareResidual.machine.rejectState
        tape := endTape (prefixBase problem index remaining) inside [] } := by
    simpa only [prefixBase, prefixStage, List.append_assoc] using
      comparison_run (coordinate problem index) 3
        (sourceFrame problem index remaining ++ budgetValues problem ++ preparedFrame problem index) inside
  have hC : AcceptPath (graph problem.verifier) (.node compareNode.reference) (endpoint problem index)
      (BuilderRegisterCompareResidual.workSteps (coordinate problem index) 3 + 1 +
        if coordinate problem index < 3 then 0 else
          rowPrepareSteps problem index + 1 + (rowSteps problem index + 1 + selectedSteps problem index))
      (endTape (sourceFrame problem index remaining ++ budgetValues problem ++
        preparedFrame problem index ++ [coordinate problem index, 3]) inside [])
      (endTape (finalValues problem index remaining) inside []) := by
    by_cases hPrefix : coordinate problem index < 3
    · simp only [if_pos hPrefix] at hCompare ⊢
      have h := AcceptPath.step compareNode .reject _ 0 _ _ _ (compare_mem problem.verifier) hCompare (.terminal .reject _)
      simpa only [endpoint, if_pos hPrefix, finalValues, prefixBase, prefixStage, List.append_nil,
        List.append_assoc, Nat.add_zero] using h
    · simp only [if_neg hPrefix] at hCompare ⊢
      have hPack : workRunExact? (BuilderRegisterPack.machine rowFields 0) (rowPrepareSteps problem index)
          (workStartConfiguration (BuilderRegisterPack.machine rowFields 0)
            (endTape (prefixBase problem index remaining) inside [])) =
          some {
            state := (BuilderRegisterPack.machine rowFields 0).acceptState
            tape := endTape (prefixBase problem index remaining ++
              BuilderInitialRowCarry.frame problem.input.length problem.uniformFuel 0
                (problem.dimensions.tapeWidth problem.tableauInputMode) (coordinate problem index - 3) (rowCount problem)) inside [] } := by
        have h := pack_run rowFields (prefixStage problem index)
          (sourceFrame problem index remaining ++ budgetValues problem) inside rfl
        rw [row_values problem index hPrefix] at h
        simpa only [prefixBase, rowPrepareSteps, List.append_assoc] using h
      have hTail := row_path problem index remaining inside
      have hR := AcceptPath.step rowPrepareNode _ _ _ _ _ _ (rowPrepare_mem problem.verifier) hPack hTail
      have h := AcceptPath.stepReject compareNode _ _ _ _ _ _ (compare_mem problem.verifier) hCompare hR
      simpa only [endpoint, if_neg hPrefix, finalValues, prefixBase, prefixStage, rowPrepareSteps,
        List.append_assoc] using h
  have hPrefix := pack_run prefixFields (preparedFrame problem index)
    (sourceFrame problem index remaining ++ budgetValues problem) inside rfl
  rw [prefix_values] at hPrefix
  simp only [List.append_assoc] at hPrefix hC
  have hP := AcceptPath.step prefixNode _ _ _ _ _ _ (prefix_mem problem.verifier) hPrefix hC
  have hPrepare := prepare_run problem index remaining inside
  simp only [List.append_assoc] at hPrepare
  have hA := AcceptPath.step (prepareNode problem.verifier) _ _ _ _ _ _ (prepare_mem problem.verifier) hPrepare hP
  have hBudget := budget_run problem index remaining inside hMode
  have hB := AcceptPath.step (budgetNode problem.verifier) _ _ _ _ _ _ (budget_mem problem.verifier) hBudget hA
  have h := WorkMachineProgramPath.runExact (graph problem.verifier) _ _ _ _ _
    (graph_wellFormed problem.verifier) hB
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node (budgetNode problem.verifier).reference) tape =
        workStartConfiguration (machine problem.verifier) tape := rfl
  have hMachine : WorkMachineProgramGraph.machine (graph problem.verifier) = machine problem.verifier := rfl
  rw [hStart, hMachine] at h
  simpa only [workSteps, prefixSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) (hMode : problem.tableauInputMode = .paired) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside hMode)

theorem final_tape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape =
      endTape (finalValues problem index remaining) inside [] := rfl

theorem final_frontier {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).tape.left = [] := rfl

theorem endpoint_selection {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    endpoint problem index = if coordinate problem index < 3 then .reject
      else match selection problem index with | none => .reject | some _ => .accept := by
  simp only [endpoint, BuilderInitialRowLoop.endpoint_eq_locate, ← selection_eq_locate]
  by_cases hPrefix : coordinate problem index < 3
  · simp only [if_pos hPrefix]
  · simp only [if_neg hPrefix]
    cases selection problem index <;> rfl

theorem final_accept_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).state = (machine problem.verifier).acceptState ↔
      (decodedCoordinate problem index).isSome = true := by
  change WorkMachineProgramGraph.endpointState (endpoint problem index) = 0 ↔ _
  rw [endpoint_selection]
  by_cases hPrefix : coordinate problem index < 3
  · simp only [hPrefix, ite_true, decodedCoordinate, if_pos hPrefix]
    decide
  · simp only [if_neg hPrefix, decodedCoordinate]
    cases selection problem index <;>
      simp only [Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
        WorkMachineProgramGraph.endpointState, reduceCtorEq] <;> decide

theorem final_reject_iff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside).state = (machine problem.verifier).rejectState ↔
      decodedCoordinate problem index = none := by
  change WorkMachineProgramGraph.endpointState (endpoint problem index) = 1 ↔ _
  rw [endpoint_selection]
  by_cases hPrefix : coordinate problem index < 3
  · simp only [hPrefix, ite_true, decodedCoordinate, if_pos hPrefix]
    decide
  · simp only [if_neg hPrefix, decodedCoordinate]
    cases selection problem index <;>
      simp only [Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
        WorkMachineProgramGraph.endpointState, reduceCtorEq] <;> decide

theorem prefix_rejected {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hPrefix : coordinate problem index < 3) : decodedCoordinate problem index = none := by
  simp only [decodedCoordinate, if_pos hPrefix]

theorem padding_rejected {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (hPadding : problem.pairedCellsWidthDirect ≤ coordinate problem index - 3) :
    decodedCoordinate problem index = none := by
  have hNone := (BuilderInitialLengthSelection.selectedLength_none_iff problem hMode
    (coordinate problem index - 3)).mpr hPadding
  by_cases hPrefix : coordinate problem index < 3
  · exact prefix_rejected problem index hPrefix
  · simp only [decodedCoordinate, if_neg hPrefix, selection, hNone, Option.map_none]

theorem found_output {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    finalValues problem index remaining =
      prefixBase problem index remaining ++ rowFinish problem index ++ startValues problem length.val ++
        handoffHistory problem length.val offset ++ requestOutput problem length.val offset := by
  simp only [finalValues, if_neg hPrefix, tailValues, hFound, List.append_assoc]

theorem found_suffix {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining = history ++ requestFrame problem length.val offset := by
  obtain ⟨history, hOutput⟩ := BuilderInitialPairedRequest.output_suffix (metadata problem length.val)
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).2
  refine ⟨prefixBase problem index remaining ++ rowFinish problem index ++ startValues problem length.val ++
    handoffHistory problem length.val offset ++ history, ?_⟩
  rw [found_output problem index remaining length offset hPrefix hFound]
  simp only [requestOutput, hOutput, requestFrame, requestCode, List.append_assoc]

/-- Every successful run returns the actual source metadata, cell and physically derived request. -/
theorem final_uniform_suffix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    match decodedCoordinate problem index with
    | none => True
    | some (length, position, offset) =>
        ∃ history : List Nat, finalValues problem index remaining =
          history ++ [problem.input.length, problem.uniformFuel, length,
            problem.dimensions.tapeWidth problem.tableauInputMode + length,
            rowCount problem - (length + 1), position, offset,
            (BuilderInitialPairedRequest.requestCode (metadata problem length) position).1,
            (BuilderInitialPairedRequest.requestCode (metadata problem length) position).2] := by
  unfold decodedCoordinate
  by_cases hPrefix : coordinate problem index < 3
  · simp only [if_pos hPrefix]
  · rw [if_neg hPrefix]
    cases hFound : selection problem index with
    | none => trivial
    | some found =>
        rcases found with ⟨length, offset⟩
        simp only [Option.map_some]
        obtain ⟨history, hOutput⟩ := found_suffix problem index remaining length offset hPrefix hFound
        exact ⟨history, by simpa only [requestFrame_values, requestCode] using hOutput⟩

theorem found_canonical_suffix {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hPrefix : ¬ coordinate problem index < 3)
    (hFound : selection problem index = some (length, offset)) :
    ∃ history : List Nat, finalValues problem index remaining =
      history ++ BuilderInitialPairedRequest.requestValues (metadata problem length.val)
        (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1
        (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).2
        (BuilderInitialPairedRequest.encodeRequest
          (BuilderInitialCellCoordinates.pairedRequest problem.input.length length problem.uniformFuel
            (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1)) := by
  obtain ⟨history, h⟩ := found_suffix problem index remaining length offset hPrefix hFound
  exact ⟨history, by simpa only [requestFrame, request_canonical] using h⟩

theorem decoded_bounds {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (offset : Nat)
    (hFound : selection problem index = some (length, offset)) :
    (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1 <
        problem.dimensions.tapeWidth problem.tableauInputMode ∧
      (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).2 <
        BuilderInitialCellCoordinates.intervalWidth (startValue problem length.val) length.val
          (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1 := by
  have hOffset := (BuilderInitialLengthSelection.selectedLength_bounds problem (coordinate problem index - 3)
    length offset hFound).1
  have h := BuilderInitialCellDecoder.decoded_bounds _ _ _ _
    (BuilderInitialCellCoordinates.certificate_interval_within_tape problem hMode length) hOffset
  exact ⟨h.1, h.2.1⟩

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph verifier) (graph_wellFormed verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph verifier)
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph verifier)
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  change (0 : Nat) ≠ 1
  decide

def budgetSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (budgetExpression verifier) bound
def preparedSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (prepareFields verifier) (budgetSpan verifier bound)
def prefixPackedSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial prefixFields (preparedSpan verifier bound)
def prefixSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterCompareResidual.spanPolynomial (prefixPackedSpan verifier bound)
def rowPackedSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial rowFields (prefixSpan verifier bound)
def rowSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialRowCarry.spanPolynomial (rowPackedSpan verifier bound)
def startSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial startExpression (rowSpan verifier bound)
def decoderPackedSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial decoderFields (startSpan verifier bound)
def decodedSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialCellHandoff.spanPolynomial (decoderPackedSpan verifier bound)

def requestSpan {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  BuilderInitialPairedRequest.spanPolynomial (decodedSpan verifier bound)

def spanPolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  .add (prefixSpan verifier bound) (.add (rowSpan verifier bound) (requestSpan verifier bound))
def rawTimePolynomial {language : Language} (verifier : PolynomialTimeVerifier language) (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.rawTimePolynomial (budgetExpression verifier) bound)
    (.add (BuilderRegisterPack.rawTimePolynomial (prepareFields verifier) (budgetSpan verifier bound))
    (.add (BuilderRegisterPack.rawTimePolynomial prefixFields (preparedSpan verifier bound))
    (.add (BuilderRegisterCompareResidual.rawTimePolynomial (prefixPackedSpan verifier bound))
    (.add (BuilderRegisterPack.rawTimePolynomial rowFields (prefixSpan verifier bound))
    (.add (BuilderInitialRowCarry.rawTimePolynomial (rowPackedSpan verifier bound))
    (.add (BuilderRegisterExpression.rawTimePolynomial startExpression (rowSpan verifier bound))
    (.add (BuilderRegisterPack.rawTimePolynomial decoderFields (startSpan verifier bound))
    (.add (BuilderInitialCellHandoff.rawTimePolynomial (decoderPackedSpan verifier bound))
    (.add (BuilderInitialPairedRequest.rawTimePolynomial (decodedSpan verifier bound)) (.constant 60))))))))))

/-- Complete source selection, handoff, request dispatch, retained history and all ten bridges are charged. -/
theorem packet_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hMode : problem.tableauInputMode = .paired)
    (hSpan : (registerWord (sourceFrame problem index remaining)).length ≤ bound.eval inputSize) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanPolynomial problem.verifier bound).eval inputSize ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier bound).eval inputSize := by
  have hBudget := BuilderRegisterExpression.source_polynomial_bounds (budgetExpression problem.verifier)
    bound inputSize [] (environment problem index remaining .initial 0 []) [] (by
      simpa only [environment_values problem index remaining .initial 0 [] rfl, sourceFrame,
        List.nil_append, List.append_nil] using hSpan)
  simp only [environment_values problem index remaining .initial 0 [] rfl,
    budget_values problem index remaining hMode, List.nil_append, List.append_nil] at hBudget
  have hPrepare := BuilderRegisterPack.source_polynomial_bounds (prepareFields problem.verifier)
    (budgetSpan problem.verifier bound) inputSize []
    (environment problem index remaining .initial 3 (budgetValues problem)) [] (by
      simpa only [environment_values problem index remaining .initial 3 (budgetValues problem) rfl,
        inputValues, budgetSpan, List.nil_append, List.append_nil] using hBudget.1)
  simp only [environment_values problem index remaining .initial 3 (budgetValues problem) rfl,
    prepare_values, List.nil_append, List.append_nil] at hPrepare
  have hPrepared : (registerWord (sourceFrame problem index remaining ++ budgetValues problem ++
      preparedFrame problem index)).length ≤ (preparedSpan problem.verifier bound).eval inputSize := by
    simpa only [preparedSpan, sourceFrame, inputValues, List.append_nil] using hPrepare.1
  have hPrefixPack := pack_bounds prefixFields (preparedFrame problem index)
    (sourceFrame problem index remaining ++ budgetValues problem) (preparedSpan problem.verifier bound)
    inputSize rfl hPrepared
  rw [prefix_values] at hPrefixPack
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds (coordinate problem index) 3
    (sourceFrame problem index remaining ++ budgetValues problem ++ preparedFrame problem index)
    (prefixPackedSpan problem.verifier bound) inputSize hPrefixPack.1
  have hPrefix : (registerWord (prefixBase problem index remaining)).length ≤
      (prefixSpan problem.verifier bound).eval inputSize := by
    rw [prefixBase, prefixStage, BuilderInitialCellDecoder.comparisonValues_eq]
    simpa only [prefixSpan, List.append_assoc] using hCompare.1
  by_cases hEarly : coordinate problem index < 3
  · constructor
    · simp only [finalValues, if_pos hEarly, List.append_nil, spanPolynomial, NatPolynomial.eval_add]
      omega
    · simp only [workSteps, if_pos hEarly, budgetSteps, prepareSteps, prefixSteps, rawTimePolynomial,
        NatPolynomial.eval_add, NatPolynomial.eval_constant]
      omega
  · have hRowPack := pack_bounds rowFields (prefixStage problem index)
      (sourceFrame problem index remaining ++ budgetValues problem) (prefixSpan problem.verifier bound)
      inputSize rfl (by simpa only [prefixBase, List.append_assoc] using hPrefix)
    rw [row_values problem index hEarly] at hRowPack
    have hCarry := BuilderInitialRowCarry.source_polynomial_bounds (rowCount problem) problem.input.length
      problem.uniformFuel 0 (problem.dimensions.tapeWidth problem.tableauInputMode)
      (coordinate problem index - 3) (prefixBase problem index remaining)
      (rowPackedSpan problem.verifier bound) inputSize (by
        simpa only [prefixBase, rowPackedSpan, List.append_assoc] using hRowPack.1)
    have hRow : (registerWord (prefixBase problem index remaining ++ rowFinish problem index)).length ≤
        (rowSpan problem.verifier bound).eval inputSize := by
      simpa only [rowSpan, rowFinish] using hCarry.1
    cases hFound : selection problem index with
    | none =>
        constructor
        · simp only [finalValues, if_neg hEarly, tailValues, hFound, List.append_nil,
            spanPolynomial, NatPolynomial.eval_add]
          omega
        · simp only [workSteps, if_neg hEarly, selectedSteps, hFound, budgetSteps, prepareSteps, prefixSteps,
            rowPrepareSteps, rowSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega
    | some found =>
        rcases found with ⟨length, offset⟩
        obtain ⟨history, hHistory⟩ := row_found_suffix problem index length offset hFound
        have hStart := expression_bounds startExpression (selectedFrame problem length.val offset)
          (prefixBase problem index remaining ++ history) (rowSpan problem.verifier bound) inputSize rfl (by
            simpa only [hHistory, List.append_assoc] using hRow)
        rw [start_values] at hStart
        have hDecoderPack := pack_bounds decoderFields (decoderFrame problem length.val offset)
          (prefixBase problem index remaining ++ history) (startSpan problem.verifier bound) inputSize rfl (by
            simpa only [decoderFrame, startSpan, List.append_assoc] using hStart.1)
        rw [decoder_values] at hDecoderPack
        have hDecoder := BuilderInitialCellHandoff.source_polynomial_bounds (metadata problem length.val)
          (startValue problem length.val) offset
          (prefixBase problem index remaining ++ history ++ decoderFrame problem length.val offset)
          (decoderPackedSpan problem.verifier bound) inputSize hDecoderPack.1
        have hRequest := BuilderInitialPairedRequest.source_polynomial_bounds (metadata problem length.val)
          (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).1
          (BuilderInitialCellSelection.cellCoordinate (startValue problem length.val) length.val offset).2
          (prefixBase problem index remaining ++ history ++ decoderFrame problem length.val offset ++
            handoffHistory problem length.val offset)
          (decodedSpan problem.verifier bound) inputSize (by
            simpa only [decodedSpan, BuilderInitialCellHandoff.outputValues, handoff_request_frame,
              handoffHistory, List.append_assoc] using hDecoder.1)
        constructor
        · have hFinal : (registerWord (finalValues problem index remaining)).length ≤
              (requestSpan problem.verifier bound).eval inputSize := by
            simpa only [finalValues, if_neg hEarly, tailValues, hFound, hHistory, requestSpan,
              requestOutput, decoderFrame, List.append_assoc] using hRequest.1
          simp only [spanPolynomial, NatPolynomial.eval_add]
          omega
        · simp only [workSteps, if_neg hEarly, selectedSteps, hFound, decodeSteps,
            budgetSteps, prepareSteps, prefixSteps, rowPrepareSteps, rowSteps, startSteps, decoderPrepareSteps,
            requestSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega

def sourceBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.inputBound verifier .initial (.constant 0)

/-- The actual source-coordinate invariants provide a bound in encoded source input size. -/
theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (hMode : problem.tableauInputMode = .paired)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanPolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤
        (rawTimePolynomial problem.verifier (sourceBound problem.verifier)).eval problem.input.length := by
  apply packet_polynomial_bounds problem index remaining _ _ hMode
  exact BuilderLiteralArgumentSource.input_span_le problem index remaining .initial [] (.constant 0)
    hBody hBalance hRegion (Nat.le_refl 0)

end PNP.Concrete.CookLevin.BuilderInitialPairedCellSource
