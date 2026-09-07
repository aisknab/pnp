/-
Copyright (c) 2026 PNP Labs.

All-input shape coordinates and exactly-one payload identities for the canonical
Cook-Levin row order. Counts and exclusive upper bounds are functions of the
actual source-derived row quotient/remainder, not a supplied variable list.
The complete fixed range machine is linked to every canonical shape payload.

Physical preparation of these fields and runtime branch dispatch remain separate
obligations. Prepared-field runs below do not claim that source-to-field work.
-/
import PNP.Concrete.CookLevinBuilderLiteralArgumentSource
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload
import PNP.Concrete.CookLevinBuilderRegisterExactlyOnePayload

namespace PNP.Concrete.CookLevin.BuilderShapeCoordinates

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

abbrev Width {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.dimensions.tapeWidth problem.tableauInputMode

def slotCount {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.dimensions.timeCount * (Width problem + 2)

theorem regionLength_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionRegisters.regionLength problem .shape = slotCount problem := by
  change (formulaTimeCountPolynomial problem.verifier).eval (BitString.size problem.input) *
      ((formulaTapeWidthPolynomial problem.verifier).eval (BitString.size problem.input) + 2) =
    problem.dimensions.timeCount * (Width problem + 2)
  rw [problem.formulaTimeCountPolynomial_eval, problem.formulaTapeWidthPolynomial_eval]

theorem radices_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderRegionRadixSource.radices problem .shape = [Width problem + 2] :=
  BuilderRegionRadixSource.shape_radices problem

structure Coordinates {language : Language} (problem : VerifierTableauProblem language) where
  time : Fin problem.dimensions.timeCount
  row : Fin (Width problem + 2)

def Coordinates.index {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Nat :=
  coordinates.row.val + (Width problem + 2) * coordinates.time.val

theorem Coordinates.index_lt {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : coordinates.index < slotCount problem := by
  have h := Nat.mul_le_mul_right (Width problem + 2) (Nat.succ_le_of_lt coordinates.time.isLt)
  rw [Nat.succ_mul] at h
  have hRow := coordinates.row.isLt
  unfold Coordinates.index slotCount
  rw [Nat.mul_comm (Width problem + 2) coordinates.time.val]
  omega

def decode {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) : Coordinates problem :=
  { time := ⟨coordinate / (Width problem + 2),
      (Nat.div_lt_iff_lt_mul (by omega : 0 < Width problem + 2)).2 hCoordinate⟩
    row := ⟨coordinate % (Width problem + 2), Nat.mod_lt _ (by omega)⟩ }

theorem decode_index {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).index = coordinate := by
  have h := BuilderRegionRadixDecoder.reconstruct_eq [Width problem + 2] coordinate
  simpa only [decode, Coordinates.index, BuilderRegionRadixDecoder.reconstruct,
    BuilderRegionRadixDecoder.digits, BuilderRegionRadixDecoder.finalQuotient, Nat.mul_zero, Nat.add_zero] using h

inductive Kind where
  | symbol | head | state
  deriving DecidableEq, Repr

def kind {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Kind :=
  if coordinates.row.val < Width problem then .symbol
  else if coordinates.row.val = Width problem then .head else .state

def count {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Nat :=
  match kind coordinates with
  | .symbol => 3
  | .head => Width problem
  | .state => problem.dimensions.stateBound

def symbolBase {language : Language} (problem : VerifierTableauProblem language) (time position : Nat) : Nat :=
  (time * Width problem + position) * 3

def headBase {language : Language} (problem : VerifierTableauProblem language) (time : Nat) : Nat :=
  problem.layout.symbolWidth + time * Width problem

def stateBase {language : Language} (problem : VerifierTableauProblem language) (time : Nat) : Nat :=
  problem.layout.symbolWidth + problem.layout.headWidth + time * problem.dimensions.stateBound

def base {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Nat :=
  match kind coordinates with
  | .symbol => symbolBase problem coordinates.time.val coordinates.row.val
  | .head => headBase problem coordinates.time.val
  | .state => stateBase problem coordinates.time.val

def upper {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Nat := base coordinates + count coordinates

def slot {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLocalConstraintPayload.Slot problem.FormulaWidth :=
  if h : coordinates.row.val < Width problem then
    some (some (problem.symbolShapeAt coordinates.time ⟨coordinates.row.val, h⟩))
  else if coordinates.row.val = Width problem then some (some (problem.headShapeAt coordinates.time))
  else some (some (problem.stateShapeAt coordinates.time))

private theorem rectangle_at (count width : Nat)
    (block : Fin count → Nat → Option α) (outer : Fin count) (inner : Nat) (hInner : inner < width) :
    DirectSlot.rectangle count width block (outer.val * width + inner) = block outer inner := by
  induction count with
  | zero => exact Fin.elim0 outer
  | succ count ih =>
      rcases outer with ⟨outer, hOuter⟩
      cases outer with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, DirectSlot.rectangle, DirectSlot.flatFinite,
            if_pos hInner]
      | succ outer =>
          have hNot : ¬ (outer + 1) * width + inner < width := by
            rw [Nat.succ_mul]
            omega
          rw [DirectSlot.rectangle, DirectSlot.flatFinite, if_neg hNot]
          have hSub : (outer + 1) * width + inner - width = outer * width + inner := by
            rw [Nat.succ_mul]
            omega
          change DirectSlot.rectangle count width (fun i => block i.succ)
            ((outer + 1) * width + inner - width) = _
          rw [hSub]
          exact ih (fun i => block i.succ) ⟨outer, by omega⟩

theorem slot_at {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    problem.shapeConstraintSlotDirect coordinates.index = slot coordinates := by
  have hIndex : coordinates.index = coordinates.time.val * (Width problem + 2) + coordinates.row.val := by
    simp only [Coordinates.index, Nat.add_comm, Nat.mul_comm]
  rw [hIndex]
  unfold VerifierTableauProblem.shapeConstraintSlotDirect
  rw [rectangle_at _ _ _ coordinates.time _ coordinates.row.isLt]
  simp only [VerifierTableauProblem.shapeRowSlotDirect, DirectSlot.append]
  by_cases hSymbol : coordinates.row.val < Width problem
  · rw [if_pos hSymbol]
    simp only [DirectSlot.finiteMap, slot, dif_pos hSymbol]
  · rw [if_neg hSymbol]
    unfold slot
    rw [dif_neg hSymbol]
    by_cases hHead : coordinates.row.val = Width problem
    · rw [if_pos hHead]
      have hZero : coordinates.row.val - Width problem = 0 := by omega
      rw [hZero]
      rfl
    · rw [if_neg hHead]
      have hRow := coordinates.row.isLt
      have hOne : coordinates.row.val - Width problem = 1 := by omega
      rw [hOne]
      rfl

theorem decode_slot {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    problem.shapeConstraintSlotDirect coordinate = slot (decode problem coordinate hCoordinate) := by
  calc
    problem.shapeConstraintSlotDirect coordinate =
        problem.shapeConstraintSlotDirect (decode problem coordinate hCoordinate).index :=
      congrArg problem.shapeConstraintSlotDirect (decode_index problem coordinate hCoordinate).symm
    _ = slot (decode problem coordinate hCoordinate) := slot_at (decode problem coordinate hCoordinate)

private theorem descending_snoc (upper count : Nat) :
    BuilderRegisterDescendingRange.values upper (count + 1) =
      BuilderRegisterDescendingRange.values upper count ++ [upper - (count + 1)] := by
  induction count generalizing upper with
  | zero => rfl
  | succ count ih =>
      change (upper - 1) :: BuilderRegisterDescendingRange.values (upper - 1) (count + 1) =
        ((upper - 1) :: BuilderRegisterDescendingRange.values (upper - 1) count) ++ [upper - (count + 1 + 1)]
      rw [ih]
      have hSub : upper - 1 - (count + 1) = upper - (count + 1 + 1) := by omega
      simp only [hSub, List.cons_append]

/-- Uniform finite-index identity, including zero width. No list is an execution premise. -/
theorem descending_eq_reverse_finiteIndices (base count : Nat) :
    BuilderRegisterDescendingRange.values (base + count) count =
      ((finiteIndices count).map (fun index => base + index.val)).reverse := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      rw [descending_snoc]
      simp only [finiteIndices, List.map_cons, List.map_map, Function.comp_def,
        Fin.val_succ, List.reverse_cons, Nat.add_zero]
      have hMap : (fun index : Fin count => base + (index.val + 1)) =
          (fun index : Fin count => (base + 1) + index.val) := by
        funext index
        omega
      rw [hMap, ← ih (base + 1)]
      have hLast : base + (count + 1) - (count + 1) = base := by omega
      have hUpper : base + (count + 1) = base + 1 + count := by omega
      rw [hLast, hUpper]

theorem exactlyOne_values {width : Nat} (variables : List (Fin width)) :
    BuilderLocalConstraintPayload.values (some (some (.exactlyOne variables))) =
      (variables.map Fin.val).reverse ++ [variables.length, 4] := by
  simp only [BuilderLocalConstraintPayload.values, BuilderLocalConstraintPayload.front,
    BuilderLocalConstraintPayload.variableValues, List.reverse_cons,
    List.nil_append, List.cons_append, List.append_assoc]

private theorem layout_dimensions {language : Language} (problem : VerifierTableauProblem language) :
    problem.layout.dimensions = problem.dimensions := rfl

private theorem layout_mode {language : Language} (problem : VerifierTableauProblem language) :
    problem.layout.mode = problem.tableauInputMode := rfl

theorem symbol_variables {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) (position : Fin (Width problem)) :
    (problem.symbolVariables time position).map Fin.val =
      [symbolBase problem time.val position.val, symbolBase problem time.val position.val + 1,
        symbolBase problem time.val position.val + 2] := by
  simp only [VerifierTableauProblem.symbolVariables, tapeSymbols, List.map_cons, List.map_nil,
    VerifierTableauProblem.symbolLiteral, VariableLayout.symbolVariable, VariableBlock.index,
    VariableLayout.symbolBlock, VariableLayout.symbolLocalIndex, VariableLayout.flattenTwo,
    VariableLayout.tapeSymbolCode, symbolBase, Width, layout_dimensions, layout_mode,
    Nat.zero_add, Nat.add_zero]

theorem head_variables {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.headVariables time).map Fin.val =
      (finiteIndices (Width problem)).map (fun position => headBase problem time.val + position.val) := by
  simp only [VerifierTableauProblem.headVariables, List.map_map, Function.comp_def,
    VerifierTableauProblem.headLiteral, VariableLayout.headVariable, VariableBlock.index,
    VariableLayout.headBlock, VariableBlock.endOffset, VariableLayout.symbolBlock,
    VariableLayout.headLocalIndex, VariableLayout.flattenTwo, headBase, Width,
    layout_dimensions, layout_mode, Nat.zero_add, Nat.add_assoc]

theorem state_variables {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.stateVariables time).map Fin.val =
      (finiteIndices problem.dimensions.stateBound).map (fun state => stateBase problem time.val + state.val) := by
  simp only [VerifierTableauProblem.stateVariables, List.map_map, Function.comp_def,
    VerifierTableauProblem.stateLiteral, VariableLayout.stateVariable, VariableBlock.index,
    VariableLayout.stateBlock, VariableLayout.headBlock, VariableBlock.endOffset,
    VariableLayout.symbolBlock, VariableLayout.stateLocalIndex, VariableLayout.flattenTwo,
    stateBase, layout_dimensions, Nat.zero_add, Nat.add_assoc]

theorem symbol_payload {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) (position : Fin (Width problem)) :
    BuilderLocalConstraintPayload.values (some (some (problem.symbolShapeAt time position))) =
      BuilderRegisterExactlyOnePayload.payloadValues 3 (symbolBase problem time.val position.val + 3) := by
  let start := symbolBase problem time.val position.val
  have hOne : start + 3 - 1 = start + 2 := by omega
  have hTwo : start + 2 - 1 = start + 1 := by omega
  have hThree : start + 1 - 1 = start := by omega
  have hRange : BuilderRegisterDescendingRange.values (start + 3) 3 = [start + 2, start + 1, start] := by
    simp only [BuilderRegisterDescendingRange.values, hOne, hTwo, hThree]
  rw [VerifierTableauProblem.symbolShapeAt, exactlyOne_values, symbol_variables]
  change [start, start + 1, start + 2].reverse ++ [3, 4] =
    BuilderRegisterDescendingRange.values (start + 3) 3 ++ [3, 4]
  rw [hRange]
  rfl

theorem head_payload {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    BuilderLocalConstraintPayload.values (some (some (problem.headShapeAt time))) =
      BuilderRegisterExactlyOnePayload.payloadValues (Width problem) (headBase problem time.val + Width problem) := by
  rw [VerifierTableauProblem.headShapeAt, exactlyOne_values, head_variables,
    ← descending_eq_reverse_finiteIndices]
  simp only [VerifierTableauProblem.headVariables, List.length_map, finiteIndices_length,
    BuilderRegisterExactlyOnePayload.payloadValues, Width]

theorem state_payload {language : Language} (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    BuilderLocalConstraintPayload.values (some (some (problem.stateShapeAt time))) =
      BuilderRegisterExactlyOnePayload.payloadValues problem.dimensions.stateBound
        (stateBase problem time.val + problem.dimensions.stateBound) := by
  rw [VerifierTableauProblem.stateShapeAt, exactlyOne_values, state_variables,
    ← descending_eq_reverse_finiteIndices]
  simp only [VerifierTableauProblem.stateVariables, List.length_map, finiteIndices_length,
    BuilderRegisterExactlyOnePayload.payloadValues]

theorem payload_eq {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    BuilderLocalConstraintPayload.values (slot coordinates) =
      BuilderRegisterExactlyOnePayload.payloadValues (count coordinates) (upper coordinates) := by
  by_cases hSymbol : coordinates.row.val < Width problem
  · simpa only [slot, dif_pos hSymbol, kind, if_pos hSymbol, count, upper, base] using
      symbol_payload problem coordinates.time ⟨coordinates.row.val, hSymbol⟩
  · by_cases hHead : coordinates.row.val = Width problem
    · simpa only [slot, dif_neg hSymbol, if_pos hHead, kind, if_neg hSymbol, count, upper, base] using
        head_payload problem coordinates.time
    · simpa only [slot, dif_neg hSymbol, if_neg hHead, kind, if_neg hSymbol, count, upper, base] using
        state_payload problem coordinates.time

theorem count_le_upper {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : count coordinates ≤ upper coordinates := by
  unfold upper
  omega

private theorem block_prefix_le (layout : VariableLayout) :
    layout.symbolWidth + layout.headWidth + layout.stateWidth ≤ layout.variableCount := by
  simp only [VariableLayout.variableCount, VariableLayout.certificateLengthBlock,
    VariableLayout.certificateBitBlock, VariableLayout.stateBlock, VariableLayout.headBlock,
    VariableLayout.symbolBlock, VariableBlock.endOffset]
  omega

theorem upper_le_formulaWidth {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : upper coordinates ≤ problem.FormulaWidth := by
  have hBlocks := block_prefix_le problem.layout
  by_cases hSymbol : coordinates.row.val < Width problem
  · have hIndex := problem.layout.symbolVariable_lt_variableCount coordinates.time
        ⟨coordinates.row.val, hSymbol⟩ .one
    simp only [VariableLayout.symbolVariable, VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.symbolLocalIndex, VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode,
      Nat.zero_add] at hIndex
    simp only [upper, base, count, kind, if_pos hSymbol, symbolBase, Width]
    change (coordinates.time.val * Width problem + coordinates.row.val) * 3 + 3 ≤ problem.layout.variableCount
    change (coordinates.time.val * Width problem + coordinates.row.val) * 3 + 2 < problem.layout.variableCount at hIndex
    omega
  · by_cases hHead : coordinates.row.val = Width problem
    · have hTime := Nat.mul_le_mul_right (Width problem) (Nat.succ_le_of_lt coordinates.time.isLt)
      rw [Nat.succ_mul] at hTime
      change coordinates.time.val * Width problem + Width problem ≤ problem.layout.headWidth at hTime
      simp only [upper, base, count, kind, if_neg hSymbol, if_pos hHead, headBase]
      change problem.layout.symbolWidth + coordinates.time.val * Width problem + Width problem ≤ problem.layout.variableCount
      omega
    · have hTime := Nat.mul_le_mul_right problem.dimensions.stateBound (Nat.succ_le_of_lt coordinates.time.isLt)
      rw [Nat.succ_mul] at hTime
      change coordinates.time.val * problem.dimensions.stateBound + problem.dimensions.stateBound ≤ problem.layout.stateWidth at hTime
      simp only [upper, base, count, kind, if_neg hSymbol, if_neg hHead, stateBase]
      change problem.layout.symbolWidth + problem.layout.headWidth +
        coordinates.time.val * problem.dimensions.stateBound + problem.dimensions.stateBound ≤ problem.layout.variableCount
      omega

theorem source_coordinate_lt {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderConstraintRegionSource.localCoordinate problem index .shape < slotCount problem := by
  rw [← regionLength_eq]
  exact BuilderConstraintRegionSource.localCoordinate_valid problem index .shape hRegion

def ofSource {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) : Coordinates problem :=
  decode problem (BuilderConstraintRegionSource.localCoordinate problem index .shape)
    (source_coordinate_lt problem index hRegion)

theorem source_slot {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape) =
      slot (ofSource problem index hRegion) :=
  decode_slot problem _ (source_coordinate_lt problem index hRegion)

theorem source_radix_coordinates {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .shape)
        (BuilderConstraintRegionSource.localCoordinate problem index .shape) =
      [(ofSource problem index hRegion).row.val] ∧
    BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .shape)
        (BuilderConstraintRegionSource.localCoordinate problem index .shape) =
      (ofSource problem index hRegion).time.val := by
  rw [radices_eq]
  exact ⟨rfl, rfl⟩

theorem source_payload {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderRegisterExactlyOnePayload.payloadValues
        (count (ofSource problem index hRegion)) (upper (ofSource problem index hRegion)) =
      BuilderLocalConstraintPayload.values
        (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) := by
  rw [source_slot]
  exact (payload_eq (ofSource problem index hRegion)).symm

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderRegisterExactlyOnePayload.payloadValues
        (count (ofSource problem index hRegion)) (upper (ofSource problem index hRegion))) =
      some (problem.shapeConstraintSlotDirect (BuilderConstraintRegionSource.localCoordinate problem index .shape)) := by
  rw [source_payload, BuilderLocalConstraintPayload.decode_values]

/-- This entry is explicitly a prepared-field boundary. It does not execute field preparation. -/
theorem prepared_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
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
          inside ((List.replicate (upper coordinates - count coordinates + 1) .blank).drop (count coordinates + 6)) } := by
  dsimp only
  have h := BuilderRegisterExactlyOnePayload.workRunExact
    (count (ofSource problem index hRegion)) (upper (ofSource problem index hRegion)) older inside
    (count_le_upper (ofSource problem index hRegion))
  simpa only [BuilderRegisterExactlyOnePayload.initialConfiguration,
    BuilderRegisterExactlyOnePayload.finalConfiguration, BuilderRegisterExactlyOnePayload.finalTape,
    source_payload] using h

theorem prepared_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape)
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
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (prepared_workRunExact problem index hRegion older inside)

theorem prepared_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (coordinates : Coordinates problem) (bound : NatPolynomial) (older : List Nat) (inside : List WorkSymbol)
    (hWidth : problem.FormulaWidth ≤ bound.eval problem.input.length)
    (hOlder : (registerWord older).length ≤ bound.eval problem.input.length) :
    (registerWord (older ++ [count coordinates] ++ BuilderLocalConstraintPayload.values (slot coordinates))).length +
        (BuilderRegisterExactlyOnePayload.finalConfiguration
          (count coordinates) (upper coordinates) older inside).tape.left.length ≤
      (BuilderRegisterExactlyOnePayload.spanPolynomial bound).eval problem.input.length ∧
    6 * BuilderRegisterExactlyOnePayload.workSteps (count coordinates) (upper coordinates) ≤
      (BuilderRegisterExactlyOnePayload.rawTimePolynomial bound).eval problem.input.length := by
  have hUpper := Nat.le_trans (upper_le_formulaWidth coordinates) hWidth
  have hCount := Nat.le_trans (count_le_upper coordinates) hUpper
  rw [payload_eq]
  exact BuilderRegisterExactlyOnePayload.source_polynomial_bounds bound problem.input.length
    (count coordinates) (upper coordinates) older inside hCount hUpper hOlder

end PNP.Concrete.CookLevin.BuilderShapeCoordinates
