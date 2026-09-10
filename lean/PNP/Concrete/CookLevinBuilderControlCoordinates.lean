/-
Copyright (c) 2026 PNP Labs.

All-coordinate reconstruction of the canonical control-transition family.
The five coordinates come from the existing source-selected mixed-radix frame.
Every conclusion has the original three ordered premises and transition action.
This specification does not supply a runtime action, literal or payload.
-/

import PNP.Concrete.CookLevinBuilderLiteralArgumentSource
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload

namespace PNP.Concrete.CookLevin.BuilderControlCoordinates

abbrev Width {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.dimensions.tapeWidth problem.tableauInputMode

abbrev StateCount {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.dimensions.stateBound

theorem stateCount_positive {language : Language} (problem : VerifierTableauProblem language) :
    0 < StateCount problem := by
  change 0 < Nat.succ _
  exact Nat.zero_lt_succ _

def slotCount {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  problem.uniformFuel * (Width problem * (StateCount problem * 9))

theorem regionLength_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderConstraintRegionRegisters.regionLength problem .control = slotCount problem := by
  have hFuel := problem.formulaFuelPolynomial_eval
  have hWidth := problem.formulaTapeWidthPolynomial_eval
  have hState := problem.formulaStateCountPolynomial_eval
  simp only [BitString.size] at hFuel hWidth hState
  simp only [BuilderConstraintRegionRegisters.regionLength,
    BuilderConstraintRegionRegisters.lengthPolynomial,
    BuilderConstraintRegionRegisters.termPolynomial, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, hFuel, hWidth, hState, slotCount, Width, StateCount]
  ac_rfl

theorem radices_eq {language : Language} (problem : VerifierTableauProblem language) :
    BuilderRegionRadixSource.radices problem .control = [3, 3, StateCount problem, Width problem] :=
  BuilderRegionRadixSource.control_radices problem

def symbol : Fin 3 → TapeSymbol := VerifierTableauProblem.controlTapeSymbol

theorem symbol_code (code : Fin 3) :
    VariableLayout.tapeSymbolCode (symbol code) = code.val := by
  decide +revert

structure Coordinates {language : Language} (problem : VerifierTableauProblem language) where
  step : Fin problem.uniformFuel
  position : Fin (Width problem)
  state : Fin (StateCount problem)
  readCode : Fin 3
  conclusion : Fin 3

/-- The canonical rectangle order: step, position, state, symbol, conclusion. -/
def Coordinates.index {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : Nat :=
  coordinates.step.val * (Width problem * (StateCount problem * 9)) +
    (coordinates.position.val * (StateCount problem * 9) +
      (coordinates.state.val * 9 + (coordinates.readCode.val * 3 + coordinates.conclusion.val)))

private theorem rectangle_index_lt (count width : Nat) (outer : Fin count) (inner : Fin width) :
    outer.val * width + inner.val < count * width := by
  have h := Nat.mul_le_mul_right width (Nat.succ_le_of_lt outer.isLt)
  rw [Nat.succ_mul] at h
  have hInner := inner.isLt
  omega

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

theorem Coordinates.index_lt {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : coordinates.index < slotCount problem := by
  have hSymbol := rectangle_index_lt 3 3 coordinates.readCode coordinates.conclusion
  have hState := rectangle_index_lt (StateCount problem) 9 coordinates.state
    ⟨coordinates.readCode.val * 3 + coordinates.conclusion.val, hSymbol⟩
  have hPosition := rectangle_index_lt (Width problem) (StateCount problem * 9) coordinates.position
    ⟨coordinates.state.val * 9 + (coordinates.readCode.val * 3 + coordinates.conclusion.val), hState⟩
  exact rectangle_index_lt problem.uniformFuel (Width problem * (StateCount problem * 9)) coordinates.step
    ⟨coordinates.position.val * (StateCount problem * 9) +
      (coordinates.state.val * 9 + (coordinates.readCode.val * 3 + coordinates.conclusion.val)), hPosition⟩

private theorem step_lt {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    coordinate / 3 / 3 / StateCount problem / Width problem < problem.uniformFuel := by
  have hWidth := problem.dimensions.tapeWidth_positive problem.tableauInputMode
  have hState := stateCount_positive problem
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  apply (Nat.div_lt_iff_lt_mul
    (Nat.mul_pos (by decide : 0 < 3) (Nat.mul_pos (by decide : 0 < 3) (Nat.mul_pos hState hWidth)))).2
  rw [← Nat.mul_assoc 3 3]
  change coordinate < problem.uniformFuel * (9 * (StateCount problem * Width problem))
  have hProduct : problem.uniformFuel * (9 * (StateCount problem * Width problem)) = slotCount problem := by
    unfold slotCount
    ac_rfl
  rw [hProduct]
  exact hCoordinate

def decode {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) : Coordinates problem :=
  { step := ⟨coordinate / 3 / 3 / StateCount problem / Width problem, step_lt problem coordinate hCoordinate⟩
    position := ⟨coordinate / 3 / 3 / StateCount problem % Width problem,
      Nat.mod_lt _ (problem.dimensions.tapeWidth_positive problem.tableauInputMode)⟩
    state := ⟨coordinate / 3 / 3 % StateCount problem, Nat.mod_lt _ (stateCount_positive problem)⟩
    readCode := ⟨coordinate / 3 % 3, Nat.mod_lt _ (by decide)⟩
    conclusion := ⟨coordinate % 3, Nat.mod_lt _ (by decide)⟩ }

private theorem radix_rectangle (step position state readCode conclusion states width : Nat) :
    conclusion + 3 * (readCode + 3 * (state + states * (position + width * step))) =
      step * (width * (states * 9)) +
        (position * (states * 9) + (state * 9 + (readCode * 3 + conclusion))) := by
  simp only [Nat.mul_add, ← Nat.mul_assoc]
  ac_rfl

theorem decode_index {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    (decode problem coordinate hCoordinate).index = coordinate := by
  have h := BuilderRegionRadixDecoder.reconstruct_eq [3, 3, StateCount problem, Width problem] coordinate
  simp only [BuilderRegionRadixDecoder.reconstruct, BuilderRegionRadixDecoder.digits,
    BuilderRegionRadixDecoder.finalQuotient] at h
  rw [radix_rectangle] at h
  exact h

def stateRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  .state (problem.currentTime coordinates.step) coordinates.state

def headRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  .head (problem.currentTime coordinates.step) coordinates.position

def readRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  .symbol (problem.currentTime coordinates.step) coordinates.position (symbol coordinates.readCode)

def action {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : VerifierTableauProblem.LocalAction problem :=
  problem.localAction coordinates.state (symbol coordinates.readCode)

def conclusionRequest {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  match coordinates.conclusion.val with
  | 0 => .state (problem.nextTime coordinates.step) (action coordinates).targetState
  | 1 => .head (problem.nextTime coordinates.step)
      (VerifierTableauProblem.movePosition coordinates.position (action coordinates).move)
  | _ => .symbol (problem.nextTime coordinates.step) coordinates.position (action coordinates).writeSymbol

def conclusionLiteral {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BoundedLiteral problem.FormulaWidth :=
  match coordinates.conclusion.val with
  | 0 => problem.stateLiteral (problem.nextTime coordinates.step) (action coordinates).targetState
  | 1 => problem.headLiteral (problem.nextTime coordinates.step)
      (VerifierTableauProblem.movePosition coordinates.position (action coordinates).move)
  | _ => problem.symbolLiteral (problem.nextTime coordinates.step) coordinates.position (action coordinates).writeSymbol

def constraint {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : LocalConstraint problem.FormulaWidth :=
  .implication (problem.controlPremises coordinates.step coordinates.state coordinates.position
    (symbol coordinates.readCode)) (conclusionLiteral coordinates)

def slot {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : BuilderLocalConstraintPayload.Slot problem.FormulaWidth :=
  some (some (constraint coordinates))

theorem candidate_payload {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    BuilderLocalConstraintPayload.values (slot coordinates) =
      [(readRequest coordinates).index, 1, (headRequest coordinates).index, 1,
        (stateRequest coordinates).index, 1, (conclusionRequest coordinates).index, 1, 3, 3] := by
  rcases coordinates with ⟨step, position, state, readCode, ⟨conclusion, hConclusion⟩⟩
  have hCases : conclusion = 0 ∨ conclusion = 1 ∨ conclusion = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

theorem candidate_indices_lt {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    (stateRequest coordinates).index < problem.FormulaWidth ∧
      (headRequest coordinates).index < problem.FormulaWidth ∧
      (readRequest coordinates).index < problem.FormulaWidth ∧
      (conclusionRequest coordinates).index < problem.FormulaWidth :=
  ⟨(stateRequest coordinates).index_lt, (headRequest coordinates).index_lt,
    (readRequest coordinates).index_lt, (conclusionRequest coordinates).index_lt⟩

theorem slot_at {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) :
    problem.controlConstraintSlotDirect coordinates.index = slot coordinates := by
  have hSymbol := rectangle_index_lt 3 3 coordinates.readCode coordinates.conclusion
  have hState := rectangle_index_lt (StateCount problem) 9 coordinates.state
    ⟨coordinates.readCode.val * 3 + coordinates.conclusion.val, hSymbol⟩
  have hPosition := rectangle_index_lt (Width problem) (StateCount problem * 9) coordinates.position
    ⟨coordinates.state.val * 9 + (coordinates.readCode.val * 3 + coordinates.conclusion.val), hState⟩
  unfold Coordinates.index VerifierTableauProblem.controlConstraintSlotDirect
  rw [rectangle_at _ _ _ coordinates.step _ hPosition]
  unfold VerifierTableauProblem.controlPositionBlockSlotDirect
  rw [rectangle_at _ _ _ coordinates.position _ hState]
  unfold VerifierTableauProblem.controlStateBlockSlotDirect
  rw [rectangle_at _ _ _ coordinates.state _ hSymbol]
  unfold VerifierTableauProblem.controlSymbolBlockSlotDirect
  rw [rectangle_at _ _ _ coordinates.readCode _ coordinates.conclusion.isLt]
  rcases coordinates with ⟨step, position, state, readCode, ⟨conclusion, hConclusion⟩⟩
  have hCases : conclusion = 0 ∨ conclusion = 1 ∨ conclusion = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

theorem decode_slot {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    problem.controlConstraintSlotDirect coordinate = slot (decode problem coordinate hCoordinate) := by
  calc
    problem.controlConstraintSlotDirect coordinate =
        problem.controlConstraintSlotDirect (decode problem coordinate hCoordinate).index :=
      congrArg problem.controlConstraintSlotDirect (decode_index problem coordinate hCoordinate).symm
    _ = slot (decode problem coordinate hCoordinate) := slot_at _

theorem payload_decode {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) (hCoordinate : coordinate < slotCount problem) :
    BuilderLocalConstraintPayload.decode problem.FormulaWidth
      (BuilderLocalConstraintPayload.values (slot (decode problem coordinate hCoordinate))) =
        some (problem.controlConstraintSlotDirect coordinate) := by
  rw [BuilderLocalConstraintPayload.decode_values, decode_slot]

theorem source_coordinate_lt {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderConstraintRegionSource.localCoordinate problem index .control < slotCount problem := by
  rw [← regionLength_eq]
  exact BuilderConstraintRegionSource.localCoordinate_valid problem index .control hRegion

def ofSource {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    Coordinates problem :=
  decode problem (BuilderConstraintRegionSource.localCoordinate problem index .control)
    (source_coordinate_lt problem index hRegion)

theorem source_slot {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderConstraintRegionSource.regionSlot problem .control
      (BuilderConstraintRegionSource.localCoordinate problem index .control) =
        slot (ofSource problem index hRegion) :=
  decode_slot problem _ (source_coordinate_lt problem index hRegion)

theorem source_radix_coordinates {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderRegionRadixDecoder.digits (BuilderRegionRadixSource.radices problem .control)
        (BuilderConstraintRegionSource.localCoordinate problem index .control) =
      [(ofSource problem index hRegion).conclusion.val, (ofSource problem index hRegion).readCode.val,
        (ofSource problem index hRegion).state.val, (ofSource problem index hRegion).position.val] ∧
    BuilderRegionRadixDecoder.finalQuotient (BuilderRegionRadixSource.radices problem .control)
        (BuilderConstraintRegionSource.localCoordinate problem index .control) =
      (ofSource problem index hRegion).step.val := by
  rw [radices_eq]
  exact ⟨rfl, rfl⟩

end PNP.Concrete.CookLevin.BuilderControlCoordinates
