import PNP.Concrete.CookLevinBuilderRegionRadixDecoder

namespace PNP.Concrete.CookLevinBuilderRegionRadixDecoderRegression

open CookLevin PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

namespace Single
open BuilderRegionCoordinateDivision

example : inputValues [42] [5, 6] 17 3 = [42, 3, 5, 6, 17] := rfl

example (offset : Nat) :
    copyMachine offset = WorkMachineChain.machine (RegisterCopy.machine 2)
      (RegisterCopy.machine (offset + 4)) := rfl

example (values : List Nat) (workspace : List WorkSymbol) :
    workRunExact? zerosMachine 5 (workStartConfiguration zerosMachine (endTape values workspace [])) =
      some { state := zerosMachine.acceptState, tape := endTape (values ++ [0, 0]) workspace [] } :=
  zeros_workRunExact values workspace

example (offset : Nat) (older newer : List Nat) (coordinate width : Nat) (workspace : List WorkSymbol)
    (hLength : newer.length = offset) :
    workRunExact? (prepareMachine offset) (prepareSteps newer coordinate width)
      (workStartConfiguration (prepareMachine offset) (endTape (inputValues older newer coordinate width) workspace [])) =
      some {
        state := (prepareMachine offset).acceptState
        tape := endTape (inputValues older newer coordinate width ++ [0, 0, coordinate, width]) workspace []
      } := prepare_workRunExact offset older newer coordinate width workspace hLength

example (offset : Nat) (older newer : List Nat) (coordinate width : Nat) (workspace : List WorkSymbol)
    (hLength : newer.length = offset) (hPositive : 0 < width) :
    workRunExact? (machine offset) (workSteps newer coordinate width)
      (initialConfiguration offset older newer coordinate width workspace) =
      some (finalConfiguration offset older newer coordinate width workspace) :=
  workRunExact offset older newer coordinate width workspace hLength hPositive

example (offset : Nat) (older newer : List Nat) (coordinate width : Nat) (workspace : List WorkSymbol)
    (hLength : newer.length = offset) (hPositive : 0 < width) :
    run (compileWorkMachine (machine offset)) (6 * workSteps newer coordinate width)
      (encodeWorkConfiguration (initialConfiguration offset older newer coordinate width workspace)) =
      encodeWorkConfiguration (finalConfiguration offset older newer coordinate width workspace) :=
  run_compile_exact offset older newer coordinate width workspace hLength hPositive

example (offset : Nat) (older newer : List Nat) (coordinate width : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration offset older newer coordinate width workspace).tape =
      endTape (inputValues older newer coordinate width ++ scratchValues coordinate width) workspace [] :=
  final_tape offset older newer coordinate width workspace

example : scratchValues 17 3 = [0, 0, 15, 2, 3, 5] := rfl
example : scratchValues 0 7 = [0, 0, 0, 0, 7, 0] := rfl
example : scratchValues 5 1 = [0, 0, 5, 0, 1, 5] := rfl
example : scratchValues 16 4 = [0, 0, 16, 0, 4, 4] := rfl
example : finalValues [42] [] 17 3 = [42, 3, 17, 0, 0, 15, 2, 3, 5] := rfl

example (coordinate width : Nat) : (scratchValues coordinate width)[5]? = some (coordinate / width) :=
  scratch_quotient coordinate width
example (coordinate width : Nat) : (scratchValues coordinate width)[3]? = some (coordinate % width) :=
  scratch_remainder coordinate width
example (coordinate width : Nat) : (coordinate / width) * width + coordinate % width = coordinate :=
  quotient_remainder_reconstruct coordinate width
example (coordinate width : Nat) (hPositive : 0 < width) : coordinate % width < width :=
  remainder_lt coordinate width hPositive
example (coordinate width : Nat) : coordinate / width ≤ coordinate := quotient_le coordinate width

example (newer : List Nat) (coordinate width : Nat) :
    workSteps newer coordinate width =
      (5 + 1 + (RegisterCopy.steps [0, 0] coordinate + 1 +
        RegisterCopy.steps (newer ++ [coordinate, 0, 0, coordinate]) width)) + 1 +
      (BuilderClauseDividerExecution.divisionSteps 0 coordinate width + 1 +
        BuilderDividerCoordinateRegisters.workSteps (resultView coordinate width)) := rfl

example (offset : Nat) : (machine offset).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct offset
example (offset : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset) := noRuleAtAccept offset
example (offset : Nat) : WorkMachineProgramGraph.NoRuleAt (machine offset) (machine offset).rejectState :=
  noRuleAtReject offset
example (offset : Nat) : (machine offset).acceptState ≠ (machine offset).rejectState :=
  acceptState_ne_rejectState offset

example (newer : List Nat) (coordinate width bound : Nat) (hCoordinate : coordinate ≤ bound)
    (hWidth : width ≤ bound) (hNewer : newer.length + newer.sum ≤ bound) (hPositive : 0 < width) :
    workSteps newer coordinate width ≤ workBound bound :=
  workSteps_le newer coordinate width bound hCoordinate hWidth hNewer hPositive
example (coordinate width bound : Nat) (hCoordinate : coordinate ≤ bound) (hWidth : width ≤ bound) :
    (scratchValues coordinate width).length + (scratchValues coordinate width).sum ≤ 3 * bound + 6 :=
  scratch_span_le coordinate width bound hCoordinate hWidth
example (older newer : List Nat) (coordinate width bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hWidth : width ≤ bound) :
    (registerWord (finalValues older newer coordinate width)).length ≤
      (registerWord (inputValues older newer coordinate width)).length + (3 * bound + 6) :=
  final_register_span_le older newer coordinate width bound hCoordinate hWidth
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rawTimePolynomial_eval bound input
example (newer : List Nat) (coordinate width input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hWidth : width ≤ bound.eval input)
    (hNewer : newer.length + newer.sum ≤ bound.eval input) (hPositive : 0 < width) :
    6 * workSteps newer coordinate width ≤ (rawTimePolynomial bound).eval input :=
  rawTimePolynomial_le newer coordinate width input bound hCoordinate hWidth hNewer hPositive

example (count coordinate width : Nat) :
    (if coordinate < count * width then
      some ((scratchValues coordinate width)[5]?.getD 0, (scratchValues coordinate width)[3]?.getD 0)
    else none) =
      (BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate? count width coordinate).map
        (fun pair => (pair.1.val, pair.2.val)) := written_pair_matches_rectangle count coordinate width

example : ClauseOccupancy.rectanglePair? 3 5 14 = some (2, 4) := rfl
example : ClauseOccupancy.rectanglePair? 3 5 15 = none := rfl
example : ClauseOccupancy.rectanglePair? 0 5 0 = none := rfl
example : ClauseOccupancy.rectanglePair? 3 0 0 = none := rfl

-- A malformed entry takes the literal first-stage rejection, not global success.
example :
    workRunExact? zerosMachine 1
      (workStartConfiguration zerosMachine { left := [], head := unitSymbol, right := [] }) =
      some {
        state := WorkMachineChain.firstState BuilderDividerOperands.Delimiter.machine.rejectState
        tape := { left := [], head := unitSymbol, right := [] }
      } := rfl

end Single

namespace Repeated
open BuilderRegionRadixDecoder

example (offset : Nat) : machine 0 offset = doneMachine := rfl
example (count offset : Nat) :
    machine (count + 1) offset = WorkMachineChain.machine (BuilderRegionCoordinateDivision.machine offset)
      (machine count (offset + 7)) := rfl
example : inputValues [99] [3, 5] [9] 41 = [99, 5, 3, 9, 41] := rfl
example : nextNewer [9] 17 3 = [3, 9, 17, 0, 0, 15, 2, 3] := rfl
example (newer : List Nat) (coordinate radix : Nat) :
    (nextNewer newer coordinate radix).length = newer.length + 7 := nextNewer_length newer coordinate radix

example (offset : Nat) (older radices newer : List Nat) (coordinate : Nat) (workspace : List WorkSymbol)
    (hLength : newer.length = offset) (hPositive : ∀ radix ∈ radices, 0 < radix) :
    workRunExact? (machine radices.length offset) (workSteps radices newer coordinate)
      (initialConfiguration offset older radices newer coordinate workspace) =
      some (finalConfiguration offset older radices newer coordinate workspace) :=
  workRunExact offset older radices newer coordinate workspace hLength hPositive

example (offset : Nat) (older radices newer : List Nat) (coordinate : Nat) (workspace : List WorkSymbol)
    (hLength : newer.length = offset) (hPositive : ∀ radix ∈ radices, 0 < radix) :
    run (compileWorkMachine (machine radices.length offset)) (6 * workSteps radices newer coordinate)
      (encodeWorkConfiguration (initialConfiguration offset older radices newer coordinate workspace)) =
      encodeWorkConfiguration (finalConfiguration offset older radices newer coordinate workspace) :=
  run_compile_exact offset older radices newer coordinate workspace hLength hPositive

example (older radices newer : List Nat) (coordinate : Nat) :
    finalValues older radices newer coordinate =
      inputValues older radices newer coordinate ++ extraValues radices coordinate :=
  finalValues_eq older radices newer coordinate
example (offset : Nat) (older radices newer : List Nat) (coordinate : Nat) (workspace : List WorkSymbol) :
    (finalConfiguration offset older radices newer coordinate workspace).tape =
      endTape (inputValues older radices newer coordinate ++ extraValues radices coordinate) workspace [] :=
  final_tape offset older radices newer coordinate workspace
example : digits [3, 5, 7] 277 = [1, 2, 4] := rfl
example : finalQuotient [3, 5, 7] 277 = 2 := rfl
example : extraValues [3, 5] 41 = [0, 0, 39, 2, 3, 13, 0, 0, 10, 3, 5, 2] := rfl
example (radices : List Nat) (coordinate : Nat) :
    (digits radices coordinate).length = radices.length := digits_length radices coordinate
example (radices : List Nat) (coordinate : Nat) :
    reconstruct radices (digits radices coordinate) (finalQuotient radices coordinate) = coordinate :=
  reconstruct_eq radices coordinate
example (radices : List Nat) (coordinate : Nat) :
    (extraValues radices coordinate).length = 6 * radices.length := extraValues_length radices coordinate
example (count offset : Nat) : (machine count offset).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct count offset
example (count offset : Nat) : WorkMachineChain.NoRuleAtAccept (machine count offset) := noRuleAtAccept count offset
example (count offset : Nat) : WorkMachineProgramGraph.NoRuleAt (machine count offset) (machine count offset).rejectState :=
  noRuleAtReject count offset
example (count offset : Nat) : (machine count offset).acceptState ≠ (machine count offset).rejectState :=
  acceptState_ne_rejectState count offset
example (newer : List Nat) (coordinate radix bound : Nat)
    (hNewer : newer.length + newer.sum ≤ bound) (hCoordinate : coordinate ≤ bound) (hRadix : radix ≤ bound) :
    (nextNewer newer coordinate radix).length + (nextNewer newer coordinate radix).sum ≤ 5 * bound + 7 :=
  nextNewer_span_le newer coordinate radix bound hNewer hCoordinate hRadix
example (radices newer : List Nat) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hNewer : newer.length + newer.sum ≤ bound)
    (hRadices : ∀ radix ∈ radices, radix ≤ bound) (hPositive : ∀ radix ∈ radices, 0 < radix) :
    workSteps radices newer coordinate ≤ workBound radices.length bound :=
  workSteps_le radices newer coordinate bound hCoordinate hNewer hRadices hPositive
example (radices : List Nat) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hRadices : ∀ radix ∈ radices, radix ≤ bound) :
    (extraValues radices coordinate).length + (extraValues radices coordinate).sum ≤
      radices.length * (3 * bound + 6) := extraValues_span_le radices coordinate bound hCoordinate hRadices
example (older radices newer : List Nat) (coordinate bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hRadices : ∀ radix ∈ radices, radix ≤ bound) :
    (registerWord (finalValues older radices newer coordinate)).length ≤
      (registerWord (inputValues older radices newer coordinate)).length + radices.length * (3 * bound + 6) :=
  final_register_span_le older radices newer coordinate bound hCoordinate hRadices
example (count : Nat) (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial count bound).eval input = 6 * workBound count (bound.eval input) :=
  rawTimePolynomial_eval count bound input
example (radices newer : List Nat) (coordinate input : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval input) (hNewer : newer.length + newer.sum ≤ bound.eval input)
    (hRadices : ∀ radix ∈ radices, radix ≤ bound.eval input) (hPositive : ∀ radix ∈ radices, 0 < radix) :
    6 * workSteps radices newer coordinate ≤ (rawTimePolynomial radices.length bound).eval input :=
  rawTimePolynomial_le radices newer coordinate input bound hCoordinate hNewer hRadices hPositive

-- Zero width is not covered by the positive-width execution theorem.
example : ¬ (∀ radix ∈ ([0] : List Nat), 0 < radix) := by
  intro h
  exact Nat.lt_irrefl 0 (h 0 List.mem_cons_self)

example (offset : Nat) (older newer : List Nat) (coordinate : Nat) (workspace : List WorkSymbol) :
    workRunExact? (machine 0 offset) 0
      (initialConfiguration offset older [] newer coordinate workspace) =
      some (finalConfiguration offset older [] newer coordinate workspace) := by
  simp only [BuilderRegionRadixDecoder.initialConfiguration,
    BuilderRegionRadixDecoder.finalConfiguration, inputValues, finalValues,
    List.length_nil, List.reverse_nil, List.append_nil, BuilderRegionRadixDecoder.machine,
    doneMachine, workStartConfiguration, workRunExact?]

example (radices : List Nat) (coordinate : Nat) :
    packetDigits (extraValues radices coordinate) = digits radices coordinate :=
  packetDigits_extraValues radices coordinate
example (older radices newer : List Nat) (coordinate : Nat) :
    (finalValues older radices newer coordinate).reverse.headD 0 = finalQuotient radices coordinate :=
  final_quotient older radices newer coordinate
example (older radices newer : List Nat) (coordinate : Nat) :
    reconstruct radices (packetDigits (extraValues radices coordinate))
      ((finalValues older radices newer coordinate).reverse.headD 0) = coordinate :=
  reconstruct_written_packets older radices newer coordinate
example : packetDigits [0, 0, 39, 2, 3, 13, 0, 0, 10, 3, 5, 2] = [2, 3] := rfl

end Repeated
end PNP.Concrete.CookLevinBuilderRegionRadixDecoderRegression
