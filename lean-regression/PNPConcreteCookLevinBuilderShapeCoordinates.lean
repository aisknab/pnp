/-
Copyright (c) 2026 PNP Labs.
Prepared all-input shape-coordinate contracts. The prepared-machine boundary
must remain distinct from the still-open physical source-field producer.
-/
import PNP.Concrete.CookLevinBuilderShapeCoordinates

namespace PNP.Concrete.CookLevin.BuilderShapeCoordinates.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionRegisters.regionLength problem .shape =
      problem.dimensions.timeCount * (Width problem + 2) := regionLength_eq problem
example {language : Language} (problem : VerifierTableauProblem language) :
    BuilderRegionRadixSource.radices problem .shape = [Width problem + 2] := radices_eq problem
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem) :
    coordinates.index < slotCount problem := coordinates.index_lt
example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).index = coordinate := decode_index problem coordinate hCoordinate
example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).time.val = coordinate / (Width problem + 2) := rfl
example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).row.val = coordinate % (Width problem + 2) := rfl

example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem)
    (hSymbol : coordinates.row.val < Width problem) : kind coordinates = .symbol := by
  simp only [kind, if_pos hSymbol]
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem)
    (hHead : coordinates.row.val = Width problem) : kind coordinates = .head := by
  have hNot : ¬ coordinates.row.val < Width problem := by omega
  simp only [kind, if_neg hNot, if_pos hHead]
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem)
    (hState : coordinates.row.val = Width problem + 1) : kind coordinates = .state := by
  have hNot : ¬ coordinates.row.val < Width problem := by omega
  have hHead : ¬ coordinates.row.val = Width problem := by omega
  simp only [kind, if_neg hNot, if_neg hHead]
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem) :
    problem.shapeConstraintSlotDirect coordinates.index = slot coordinates := slot_at coordinates
example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate : coordinate < slotCount problem) :
    problem.shapeConstraintSlotDirect coordinate = slot (decode problem coordinate hCoordinate) :=
  decode_slot problem coordinate hCoordinate

example (base count : Nat) :
    BuilderRegisterDescendingRange.values (base + count) count =
      ((finiteIndices count).map (fun index => base + index.val)).reverse :=
  descending_eq_reverse_finiteIndices base count
example (base : Nat) : BuilderRegisterDescendingRange.values (base + 0) 0 = ([] : List Nat) := rfl
example {width : Nat} (variables : List (Fin width)) :
    BuilderLocalConstraintPayload.values (some (some (.exactlyOne variables))) =
      (variables.map Fin.val).reverse ++ [variables.length, 4] := exactlyOne_values variables
example {width : Nat} :
    BuilderLocalConstraintPayload.values (some (some (.exactlyOne ([] : List (Fin width))))) = [0, 4] := rfl

example {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) (position : Fin (Width problem)) :
    (problem.symbolVariables time position).map Fin.val =
      [symbolBase problem time.val position.val, symbolBase problem time.val position.val + 1,
        symbolBase problem time.val position.val + 2] := symbol_variables problem time position
example {language : Language} (problem : VerifierTableauProblem language) (time : Fin problem.dimensions.timeCount) :
    (problem.headVariables time).map Fin.val =
      (finiteIndices (Width problem)).map (fun position => headBase problem time.val + position.val) :=
  head_variables problem time
example {language : Language} (problem : VerifierTableauProblem language) (time : Fin problem.dimensions.timeCount) :
    (problem.stateVariables time).map Fin.val =
      (finiteIndices problem.dimensions.stateBound).map (fun state => stateBase problem time.val + state.val) :=
  state_variables problem time
example {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) (position : Fin (Width problem)) :
    BuilderLocalConstraintPayload.values (some (some (problem.symbolShapeAt time position))) =
      BuilderRegisterExactlyOnePayload.payloadValues 3 (symbolBase problem time.val position.val + 3) :=
  symbol_payload problem time position
example {language : Language} (problem : VerifierTableauProblem language) (time : Fin problem.dimensions.timeCount) :
    BuilderLocalConstraintPayload.values (some (some (problem.headShapeAt time))) =
      BuilderRegisterExactlyOnePayload.payloadValues (Width problem) (headBase problem time.val + Width problem) :=
  head_payload problem time
example {language : Language} (problem : VerifierTableauProblem language) (time : Fin problem.dimensions.timeCount) :
    BuilderLocalConstraintPayload.values (some (some (problem.stateShapeAt time))) =
      BuilderRegisterExactlyOnePayload.payloadValues problem.dimensions.stateBound
        (stateBase problem time.val + problem.dimensions.stateBound) := state_payload problem time
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem) :
    BuilderLocalConstraintPayload.values (slot coordinates) =
      BuilderRegisterExactlyOnePayload.payloadValues (count coordinates) (upper coordinates) := payload_eq coordinates
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem) :
    count coordinates ≤ upper coordinates := count_le_upper coordinates
example {language : Language} {problem : VerifierTableauProblem language} (coordinates : Coordinates problem) :
    upper coordinates ≤ problem.FormulaWidth := upper_le_formulaWidth coordinates

example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderConstraintRegionSource.localCoordinate problem index .shape < slotCount problem :=
  source_coordinate_lt problem index hRegion
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape) =
      slot (ofSource problem index hRegion) := source_slot problem index hRegion
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .shape)
        (BuilderConstraintRegionSource.localCoordinate problem index .shape) =
      [(ofSource problem index hRegion).row.val] := (source_radix_coordinates problem index hRegion).1
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .shape)
        (BuilderConstraintRegionSource.localCoordinate problem index .shape) =
      (ofSource problem index hRegion).time.val := (source_radix_coordinates problem index hRegion).2
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderRegisterExactlyOnePayload.payloadValues
        (count (ofSource problem index hRegion)) (upper (ofSource problem index hRegion)) =
      BuilderLocalConstraintPayload.values
        (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  source_payload problem index hRegion
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderRegisterExactlyOnePayload.payloadValues
        (count (ofSource problem index hRegion)) (upper (ofSource problem index hRegion))) =
      some (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) :=
  payload_decode problem index hRegion

-- The following entry explicitly contains the prepared source-derived count and upper.
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (older : List Nat) (inside : List WorkSymbol) :
    let coordinates := ofSource problem index hRegion
    workRunExact? BuilderRegisterExactlyOnePayload.machine
      (BuilderRegisterExactlyOnePayload.workSteps (count coordinates) (upper coordinates))
      (workStartConfiguration BuilderRegisterExactlyOnePayload.machine
        (endTape (older ++ [count coordinates, upper coordinates]) inside [])) =
      some {
        state := BuilderRegisterExactlyOnePayload.machine.acceptState
        tape := endTape
          (older ++ [count coordinates] ++ BuilderLocalConstraintPayload.values
            (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside ((List.replicate (upper coordinates - count coordinates + 1) .blank).drop (count coordinates + 6)) } :=
  prepared_workRunExact problem index hRegion older inside
example {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
    (older : List Nat) (inside : List WorkSymbol) :
    let coordinates := ofSource problem index hRegion
    run (compileWorkMachine BuilderRegisterExactlyOnePayload.machine)
      (6 * BuilderRegisterExactlyOnePayload.workSteps (count coordinates) (upper coordinates))
      (encodeWorkConfiguration
        (workStartConfiguration BuilderRegisterExactlyOnePayload.machine
          (endTape (older ++ [count coordinates, upper coordinates]) inside []))) =
      encodeWorkConfiguration {
        state := BuilderRegisterExactlyOnePayload.machine.acceptState
        tape := endTape
          (older ++ [count coordinates] ++ BuilderLocalConstraintPayload.values
            (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)))
          inside ((List.replicate (upper coordinates - count coordinates + 1) .blank).drop (count coordinates + 6)) } :=
  prepared_run_compile_exact problem index hRegion older inside
example {language : Language} (problem : VerifierTableauProblem language)
    (coordinates : Coordinates problem) (bound : NatPolynomial) (older : List Nat) (inside : List WorkSymbol)
    (hWidth : problem.FormulaWidth ≤ bound.eval problem.input.length)
    (hOlder : (registerWord older).length ≤ bound.eval problem.input.length) :
    (registerWord (older ++ [count coordinates] ++ BuilderLocalConstraintPayload.values (slot coordinates))).length +
        (BuilderRegisterExactlyOnePayload.finalConfiguration
          (count coordinates) (upper coordinates) older inside).tape.left.length ≤
      (BuilderRegisterExactlyOnePayload.spanPolynomial bound).eval problem.input.length ∧
    6 * BuilderRegisterExactlyOnePayload.workSteps (count coordinates) (upper coordinates) ≤
      (BuilderRegisterExactlyOnePayload.rawTimePolynomial bound).eval problem.input.length :=
  prepared_polynomial_bounds problem coordinates bound older inside hWidth hOlder

end PNP.Concrete.CookLevin.BuilderShapeCoordinates.Regression
