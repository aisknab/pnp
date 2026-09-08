/-
Copyright (c) 2026 PNP Labs.
The complete fixed paired-request dispatcher must preserve source metadata,
distinguish every encoding boundary, derive indices from physical residuals,
and agree with the canonical request for all positions and certificate lengths.
-/
import PNP.Concrete.CookLevinBuilderInitialPairedRequest

namespace PNP.Concrete.CookLevin.BuilderInitialPairedRequest.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

private def fixture : Metadata := ⟨3, 2, 2, 17, 4⟩
private def noInput : Metadata := {fixture with inputLength := 0}
private def noCertificate : Metadata := {fixture with length := 0}
private def empty : Metadata := ⟨0, 0, 0, 2, 0⟩
private def data (values : List Nat) {arity : Nat} (i : Fin arity) : Nat := values[i.val]?.getD 0

example : entries.length = 7 := entries_length
example : entries.map Entry.width = [.fuel, .input, .one, .input, .certificate, .one, .certificate] := rfl
example : entries.map Entry.payload =
    [.blank, .fixed true, .fixed false, .source, .fixed true, .fixed false, .certificate] := rfl
example : requestCode fixture 0 = (0, 0) := by decide
example : requestCode fixture 1 = (0, 0) := by decide
example : requestCode fixture 2 = (1, 1) := by decide
example : requestCode fixture 4 = (1, 1) := by decide
example : requestCode fixture 5 = (1, 0) := by decide
example : requestCode fixture 6 = (2, 0) := by decide
example : requestCode fixture 7 = (2, 1) := by decide
example : requestCode fixture 8 = (2, 2) := by decide
example : requestCode fixture 9 = (1, 1) := by decide
example : requestCode fixture 10 = (1, 1) := by decide
example : requestCode fixture 11 = (1, 0) := by decide
example : requestCode fixture 12 = (3, 0) := by decide
example : requestCode fixture 13 = (3, 1) := by decide
example : requestCode fixture 14 = (0, 0) := by decide
example : requestCode fixture 99 = (0, 0) := by decide
example : requestCode noInput 2 = (1, 0) := by decide
example : requestCode noInput 3 = (1, 1) := by decide
example : requestCode noInput 5 = (1, 0) := by decide
example : requestCode noInput 6 = (3, 0) := by decide
example : requestCode noInput 7 = (3, 1) := by decide
example : requestCode noInput 8 = (0, 0) := by decide
example : requestCode noCertificate 8 = (2, 2) := by decide
example : requestCode noCertificate 9 = (1, 0) := by decide
example : requestCode noCertificate 10 = (0, 0) := by decide
example : requestCode empty 0 = (1, 0) := by decide
example : requestCode empty 1 = (1, 0) := by decide
example : requestCode empty 2 = (0, 0) := by decide

example : requestCode fixture 7 ≠ (2, 7) := by decide
example : requestCode fixture 12 ≠ (3, 12) := by decide
example : requestCode fixture 5 ≠ (1, 1) := by decide
example : requestCode fixture 14 ≠ (3, 2) := by decide
example : requestCode noInput 2 ≠ (2, 0) := by decide
example : requestCode noCertificate 10 ≠ (3, 0) := by decide
example : BuilderRegisterPack.values initialFields (data (inputValues fixture 7 1)) =
    [3, 2, 2, 17, 4, 7, 1, 7] := by decide
example : BuilderRegisterPack.values (comparisonFields .input) (data (frame fixture 7 1 4)) = [4, 3] := by decide
example : BuilderRegisterPack.values (comparisonFields .certificate) (data (frame fixture 7 1 4)) = [4, 2] := by decide
example : BuilderRegisterPack.values carryFields (data (comparisonFrame .input fixture 7 1 4)) =
    [3, 2, 2, 17, 4, 7, 1, 1] := by decide
example : BuilderRegisterPack.values carryFields (data (comparisonFrame .input fixture 7 1 4)) ≠
    [3, 2, 2, 17, 4, 7, 1, 4] := by decide
example : BuilderRegisterPack.values (reportFields .source) (data (comparisonFrame .input fixture 7 1 1)) =
    [3, 2, 2, 17, 4, 7, 1, 2, 1] := by decide
example : BuilderRegisterPack.values (reportFields .certificate) (data (comparisonFrame .certificate fixture 12 0 0)) =
    [3, 2, 2, 17, 4, 12, 0, 3, 0] := by decide
example : BuilderRegisterPack.values (reportFields (.fixed false)) (data (comparisonFrame .one fixture 5 0 0)) =
    [3, 2, 2, 17, 4, 5, 0, 1, 0] := by decide
example : BuilderRegisterPack.values baseFields (data (frame fixture 14 0 0)) =
    [3, 2, 2, 17, 4, 14, 0, 0, 0] := by decide

example : graph.WellFormed := graph_wellFormed
example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

section General
variable (metadata : Metadata) (position offset : Nat)

example : (inputValues metadata position offset).length = 7 := inputValues_length metadata position offset
example (cursor : Nat) : (frame metadata position offset cursor).length = 8 := frame_length metadata position offset cursor
example (width : Width) (cursor : Nat) : (comparisonFrame width metadata position offset cursor).length = 13 :=
  comparisonFrame_length width metadata position offset cursor
example (request : Nat × Nat) : (requestValues metadata position offset request).length = 9 :=
  requestValues_length metadata position offset request
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps metadata position offset)
      (initialConfiguration metadata position offset older inside) =
      some (finalConfiguration metadata position offset older inside) :=
  workRunExact metadata position offset older inside
example (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps metadata position offset)
      (encodeWorkConfiguration (initialConfiguration metadata position offset older inside)) =
      encodeWorkConfiguration (finalConfiguration metadata position offset older inside) :=
  run_compile_exact metadata position offset older inside
example (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration metadata position offset older inside).tape =
      endTape (older ++ outputValues metadata position offset) inside [] := final_tape metadata position offset older inside
example (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration metadata position offset older inside).tape.left = [] := final_frontier metadata position offset older inside
example (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration metadata position offset older inside).state = machine.acceptState :=
  final_accept metadata position offset older inside
example :
    ∃ history : List Nat, outputValues metadata position offset =
      history ++ requestValues metadata position offset (requestCode metadata position) :=
  output_suffix metadata position offset
example {certificateWidth : Nat} (length : Fin (certificateWidth + 1)) (hLength : metadata.length = length.val) :
    requestCode metadata position =
      encodeRequest (BuilderInitialCellCoordinates.pairedRequest metadata.inputLength length metadata.fuel position) :=
  request_canonical metadata length position hLength
example {certificateWidth : Nat} (length : Fin (certificateWidth + 1)) (hLength : metadata.length = length.val) :
    ∃ history : List Nat, outputValues metadata position offset =
      history ++ requestValues metadata position offset
        (encodeRequest (BuilderInitialCellCoordinates.pairedRequest metadata.inputLength length metadata.fuel position)) :=
  canonical_output_suffix metadata length position offset hLength
example {certificateWidth : Nat} (length : Fin (certificateWidth + 1)) (hLength : metadata.length = length.val)
    (hCertificate : (requestCode metadata position).1 = 3) :
    (requestCode metadata position).2 < certificateWidth :=
  certificate_index_bound metadata length position hLength hCertificate
example (older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ inputValues metadata position offset)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues metadata position offset)).length ≤
        (spanPolynomial bound).eval inputSize ∧
      6 * workSteps metadata position offset ≤ (rawTimePolynomial bound).eval inputSize :=
  source_polynomial_bounds metadata position offset older bound inputSize hSpan
example :
    (registerWord (requestValues metadata position offset (requestCode metadata position))).length ≤
      (registerWord (outputValues metadata position offset)).length := request_span_le_output metadata position offset

end General

example (position : Nat) : (requestCode noCertificate position).1 ≠ 3 := by
  intro hCertificate
  have h := certificate_index_bound noCertificate (⟨0, by decide⟩ : Fin 1) position rfl hCertificate
  omega

end PNP.Concrete.CookLevin.BuilderInitialPairedRequest.Regression
