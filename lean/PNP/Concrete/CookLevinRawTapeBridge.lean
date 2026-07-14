/-
Copyright (c) 2026 PNP Labs.

Exact bridge from the finite Cook--Levin row semantics to the concrete raw
single-tape interpreter.

The finite formula uses a bounded absolute tape window, while `Tape` is a
focused zipper with implicit blank cells.  This file gives the zipper an
absolute observation function, proves that writes and moves preserve those
observations, and transports the deterministic finite-row evolution to the
literal first-match raw execution.  It does not establish a polynomial
reduction or NP-hardness.
-/

import PNP.Concrete.CookLevinTableauCNFSemantics

namespace PNP.Concrete

namespace Tape

/-- Observe an absolute tape position when the focused cell is assigned the
absolute coordinate `headPosition`.  Cells absent from either finite zipper
list are the raw machine's implicit blanks. -/
def symbolAt (tape : Tape) (headPosition position : Nat) : TapeSymbol :=
  if position < headPosition then
    (tape.left[headPosition - position - 1]?).getD .blank
  else if position = headPosition then
    tape.head
  else
    (tape.right[position - headPosition - 1]?).getD .blank

theorem symbolAt_ofInput_from_center (bits : BitString)
    (headPosition offset : Nat) :
    (Tape.ofInput bits).symbolAt headPosition (headPosition + offset) =
      ((bits.map TapeSymbol.ofBool)[offset]?).getD .blank := by
  cases bits with
  | nil =>
      simp [Tape.ofInput, Tape.blank, symbolAt]
  | cons first rest =>
      cases offset with
      | zero => simp [Tape.ofInput, symbolAt]
      | succ offset =>
          simp [Tape.ofInput, symbolAt]
          omega

theorem symbolAt_ofInput (bits : BitString)
    (headPosition position : Nat) :
    (Tape.ofInput bits).symbolAt headPosition position =
      if headPosition ≤ position then
        ((bits.map TapeSymbol.ofBool)[position - headPosition]?).getD .blank
      else
        .blank := by
  by_cases hInside : headPosition ≤ position
  · calc
      (Tape.ofInput bits).symbolAt headPosition position =
          (Tape.ofInput bits).symbolAt headPosition
            (headPosition + (position - headPosition)) := by
              congr 2
              omega
      _ = ((bits.map TapeSymbol.ofBool)[position - headPosition]?).getD
          .blank := symbolAt_ofInput_from_center bits headPosition
            (position - headPosition)
      _ = if headPosition ≤ position then
          ((bits.map TapeSymbol.ofBool)[position - headPosition]?).getD .blank
          else .blank := by simp [hInside]
  · have hBefore : position < headPosition := by omega
    cases bits <;>
      simp [Tape.ofInput, Tape.blank, symbolAt, hInside, hBefore]

@[simp] theorem symbolAt_head (tape : Tape) (headPosition : Nat) :
    tape.symbolAt headPosition headPosition = tape.head := by
  simp [symbolAt]

theorem symbolAt_write (tape : Tape) (symbol : TapeSymbol)
    (headPosition position : Nat) :
    (tape.write symbol).symbolAt headPosition position =
      if position = headPosition then symbol
      else tape.symbolAt headPosition position := by
  by_cases hEqual : position = headPosition
  · subst position
    simp [symbolAt, Tape.write]
  · simp [symbolAt, Tape.write, hEqual]

/-- Moving the focused zipper left does not change any absolute cell when the
old absolute head coordinate is positive. -/
theorem symbolAt_moveLeft (tape : Tape) (headPosition position : Nat)
    (hPositive : 0 < headPosition) :
    tape.moveLeft.symbolAt (headPosition - 1) position =
      tape.symbolAt headPosition position := by
  rcases tape with ⟨left, head, right⟩
  by_cases hFarLeft : position < headPosition - 1
  · have hOldLeft : position < headPosition := by omega
    have hIndex :
        headPosition - position - 1 =
          (headPosition - 1 - position - 1) + 1 := by omega
    cases left <;> simp_all [Tape.moveLeft, symbolAt]
  · by_cases hNewHead : position = headPosition - 1
    · subst position
      have hOldLeft : headPosition - 1 < headPosition := by omega
      have hIndex : headPosition - (headPosition - 1) - 1 = 0 := by omega
      cases left <;> simp_all [Tape.moveLeft, symbolAt] <;> omega
    · by_cases hOldHead : position = headPosition
      · subst position
        have hIndex : headPosition - (headPosition - 1) - 1 = 0 := by omega
        cases left <;> simp_all [Tape.moveLeft, symbolAt] <;> omega
      · have hAfter : headPosition < position := by omega
        have hNotNewLeft : ¬ position < headPosition - 1 := by omega
        have hNotOldLeft : ¬ position < headPosition := by omega
        have hIndex :
            position - (headPosition - 1) - 1 =
              (position - headPosition - 1) + 1 := by omega
        cases left <;> simp_all [Tape.moveLeft, symbolAt] <;>
          split <;> split <;> try omega
        all_goals rfl

/-- Moving the focused zipper right shifts the focus but leaves every
absolute cell unchanged. -/
theorem symbolAt_moveRight (tape : Tape) (headPosition position : Nat) :
    tape.moveRight.symbolAt (headPosition + 1) position =
      tape.symbolAt headPosition position := by
  rcases tape with ⟨left, head, right⟩
  by_cases hOldLeft : position < headPosition
  · have hNewLeft : position < headPosition + 1 := by omega
    have hIndex :
        headPosition + 1 - position - 1 =
          (headPosition - position - 1) + 1 := by omega
    cases right <;> simp_all [Tape.moveRight, symbolAt]
  · by_cases hOldHead : position = headPosition
    · subst position
      cases right <;> simp_all [Tape.moveRight, symbolAt] <;> omega
    · by_cases hNewHead : position = headPosition + 1
      · subst position
        cases right <;> simp_all [Tape.moveRight, symbolAt] <;> omega
      · have hAfter : headPosition + 1 < position := by omega
        have hNotNewLeft : ¬ position < headPosition + 1 := by omega
        have hNotOldLeft : ¬ position < headPosition := by omega
        have hIndex :
            position - headPosition - 1 =
              (position - (headPosition + 1) - 1) + 1 := by omega
        cases right <;> simp_all [Tape.moveRight, symbolAt] <;>
          split <;> split <;> try omega
        all_goals rfl

/-- A write followed by one raw movement has the expected absolute-cell
semantics. -/
theorem symbolAt_write_move (tape : Tape) (writeSymbol : TapeSymbol)
    (move : HeadMove) (headPosition position : Nat)
    (hPositive : 0 < headPosition) :
    ((tape.write writeSymbol).move move).symbolAt
        (match move with
         | .left => headPosition - 1
         | .stay => headPosition
         | .right => headPosition + 1)
        position =
      if position = headPosition then writeSymbol
      else tape.symbolAt headPosition position := by
  cases move with
  | left =>
      change
        (tape.write writeSymbol).moveLeft.symbolAt (headPosition - 1)
            position =
          if position = headPosition then writeSymbol
          else tape.symbolAt headPosition position
      rw [symbolAt_moveLeft (tape.write writeSymbol) headPosition position
        hPositive]
      exact symbolAt_write tape writeSymbol headPosition position
  | stay => exact symbolAt_write tape writeSymbol headPosition position
  | right =>
      change
        (tape.write writeSymbol).moveRight.symbolAt (headPosition + 1)
            position =
          if position = headPosition then writeSymbol
          else tape.symbolAt headPosition position
      rw [symbolAt_moveRight (tape.write writeSymbol) headPosition position]
      exact symbolAt_write tape writeSymbol headPosition position

end Tape

namespace CookLevin

namespace VerifierTableauProblem

/-- A finite row is the restriction of a raw focused configuration to the
fixed absolute Cook--Levin window. -/
def FiniteRow.Represents {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) (config : Configuration) : Prop :=
  row.state.val = config.state ∧
    ∀ position, row.symbol position =
      config.tape.symbolAt row.head.val position.val

theorem initialCellAtOffset_inputOnly (bits : BitString) (offset : Nat) :
    initialCellSymbol (fun index : Fin 0 => Fin.elim0 index)
        (initialCellAtOffset (inputOnlyInitialCells bits) offset) =
      ((bits.map TapeSymbol.ofBool)[offset]?).getD .blank := by
  induction bits generalizing offset with
  | nil => cases offset <;> rfl
  | cons first rest ih =>
      cases offset with
      | zero => rfl
      | succ offset => exact ih offset

theorem inputOnlyInitialSymbol_eq_ofInput {language : Language}
    (problem : VerifierTableauProblem language)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.inputOnlyInitialSymbol position =
      (Tape.ofInput problem.input).symbolAt problem.uniformFuel position.val := by
  unfold inputOnlyInitialSymbol initialCellAt
  rw [Tape.symbolAt_ofInput]
  by_cases hInside : problem.uniformFuel ≤ position.val
  · simp [hInside, initialCellAtOffset_inputOnly]
  · simp [hInside, initialCellSymbol]

theorem inputOnlyInitialRow_represents {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.verifier.program.inputMode = .inputOnly) :
    problem.inputOnlyInitialRow.Represents (problem.initial []) := by
  constructor
  · rfl
  · intro position
    change problem.inputOnlyInitialSymbol position =
      (Tape.ofInput (problem.rawInput [])).symbolAt
        problem.uniformFuel position.val
    have hRawInput : problem.rawInput [] = problem.input := by
      unfold rawInput
      rw [hMode]
      rfl
    rw [hRawInput]
    exact problem.inputOnlyInitialSymbol_eq_ofInput position

/-- Reconstruct the bounded certificate selected by the formula's unary
length coordinate and finite bit coordinates. -/
def certificateOf (certificateWidth : Nat)
    (length : Fin (certificateWidth + 1))
    (certificateBit : Fin certificateWidth → Bool) : BitString :=
  ((finiteIndices certificateWidth).take length.val).map certificateBit

theorem certificateOf_length (certificateWidth : Nat)
    (length : Fin (certificateWidth + 1))
    (certificateBit : Fin certificateWidth → Bool) :
    (certificateOf certificateWidth length certificateBit).length =
      length.val := by
  unfold certificateOf
  rw [List.length_map, List.length_take, finiteIndices_length]
  exact Nat.min_eq_left (Nat.lt_succ_iff.mp length.isLt)

/-- Total bit lookup used to embed an ordinary bounded certificate into the
formula's fixed-width certificate-bit namespace. -/
def certificateBitOf (certificate : BitString) (index : Fin width) : Bool :=
  (certificate[index.val]?).getD false

theorem map_finiteIndices_val (width : Nat) :
    (finiteIndices width).map Fin.val = List.range width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [finiteIndices, List.map_cons, List.range_succ_eq_map,
        List.cons.injEq, true_and]
      have hFunctions :
          (Fin.val ∘ Fin.succ : Fin width → Nat) =
            (Nat.succ ∘ Fin.val) := by
        funext index
        rfl
      rw [List.map_map, hFunctions, ← List.map_map, ih]

theorem map_range_getD (bits : BitString) :
    (List.range bits.length).map
        (fun index => (bits[index]?).getD false) = bits := by
  induction bits with
  | nil => rfl
  | cons first rest ih =>
      change
        (List.range (rest.length + 1)).map
            (fun index => ((first :: rest)[index]?).getD false) =
          first :: rest
      rw [List.range_succ_eq_map]
      rw [List.map_cons, List.map_map]
      simp only [List.getElem?_cons_zero, Option.getD_some,
        List.cons.injEq, true_and]
      have hTailFunction :
          ((fun index => ((first :: rest)[index]?).getD false) ∘ Nat.succ) =
            (fun index => (rest[index]?).getD false) := by
        funext index
        rfl
      rw [hTailFunction, ih]

theorem certificateOf_certificate (certificateWidth : Nat)
    (certificate : BitString)
    (hLength : certificate.length ≤ certificateWidth) :
    certificateOf certificateWidth
        ⟨certificate.length, Nat.lt_succ_of_le hLength⟩
        (certificateBitOf certificate) = certificate := by
  unfold certificateOf
  rw [List.map_take]
  have hMapped :
      (finiteIndices certificateWidth).map
          (certificateBitOf certificate) =
        (List.range certificateWidth).map
          (fun index => (certificate[index]?).getD false) := by
    have hValues := congrArg
      (List.map (fun index => (certificate[index]?).getD false))
      (map_finiteIndices_val certificateWidth)
    change
      (finiteIndices certificateWidth).map
          (fun index => (certificate[index.val]?).getD false) =
        (List.range certificateWidth).map
          (fun index => (certificate[index]?).getD false)
    have hFunctions :
        ((fun index => (certificate[index]?).getD false) ∘ Fin.val) =
      (fun index : Fin certificateWidth =>
            (certificate[index.val]?).getD false) := by
      rfl
    rw [List.map_map] at hValues
    rw [hFunctions] at hValues
    exact hValues
  rw [hMapped, ← List.map_take, List.take_range,
    Nat.min_eq_left hLength]
  exact map_range_getD certificate

theorem initialCellSymbol_fixed (certificateBit : Fin width → Bool)
    (value : Bool) :
    initialCellSymbol certificateBit (.fixed value) =
      TapeSymbol.ofBool value := by
  cases value <;> rfl

@[simp] theorem initialCellSymbol_certificate
    (certificateBit : Fin width → Bool) (index : Fin width) :
    initialCellSymbol certificateBit (.certificate index) =
      TapeSymbol.ofBool (certificateBit index) := by
  cases hValue : certificateBit index <;>
    simp [initialCellSymbol, hValue, TapeSymbol.ofBool]

theorem map_fixedFrameCells (bits : BitString)
    (certificateBit : Fin width → Bool) :
    (fixedFrameCells bits).map (initialCellSymbol certificateBit) =
      (BitString.frame bits).map TapeSymbol.ofBool := by
  unfold fixedFrameCells BitString.frame
  simp [List.map_append, initialCellSymbol_fixed]

theorem map_certificateFrameCells (certificateWidth : Nat)
    (length : Fin (certificateWidth + 1))
    (certificateBit : Fin certificateWidth → Bool) :
    (certificateFrameCells certificateWidth length).map
        (initialCellSymbol certificateBit) =
      (BitString.frame
        (certificateOf certificateWidth length certificateBit)).map
          TapeSymbol.ofBool := by
  unfold certificateFrameCells BitString.frame certificateOf
  rw [List.map_append, List.map_cons, List.map_append]
  rw [List.length_map, List.length_take, finiteIndices_length]
  rw [Nat.min_eq_left (Nat.lt_succ_iff.mp length.isLt)]
  simp only [List.map_replicate, initialCellSymbol_fixed,
    TapeSymbol.ofBool, List.map_cons, List.map_map]
  have hMap :
      ((finiteIndices certificateWidth).take length.val).map
          (initialCellSymbol certificateBit ∘ InitialCell.certificate) =
        ((finiteIndices certificateWidth).take length.val).map
          (TapeSymbol.ofBool ∘ certificateBit) := by
    apply List.map_congr_left
    intro index _
    exact initialCellSymbol_certificate certificateBit index
  rw [hMap]

theorem map_pairedInitialCells (input : BitString)
    (certificateWidth : Nat) (length : Fin (certificateWidth + 1))
    (certificateBit : Fin certificateWidth → Bool) :
    (pairedInitialCells input certificateWidth length).map
        (initialCellSymbol certificateBit) =
      (BitString.pair input
        (certificateOf certificateWidth length certificateBit)).map
          TapeSymbol.ofBool := by
  unfold pairedInitialCells BitString.pair
  rw [List.map_append, List.map_append]
  rw [map_fixedFrameCells, map_certificateFrameCells]

theorem initialCellAtOffset_map (cells : List (InitialCell width))
    (certificateBit : Fin width → Bool) (offset : Nat) :
    initialCellSymbol certificateBit (initialCellAtOffset cells offset) =
      ((cells.map (initialCellSymbol certificateBit))[offset]?).getD .blank := by
  induction cells generalizing offset with
  | nil => cases offset <;> rfl
  | cons first rest ih =>
      cases offset with
      | zero => rfl
      | succ offset => exact ih offset

theorem initialCellAt_symbol (cells : List (InitialCell width))
    (certificateBit : Fin width → Bool) (center position : Nat) :
    initialCellSymbol certificateBit (initialCellAt cells center position) =
      if center ≤ position then
        ((cells.map (initialCellSymbol certificateBit))[position - center]?).getD
          .blank
      else
        .blank := by
  unfold initialCellAt
  by_cases hInside : center ≤ position
  · simp [hInside, initialCellAtOffset_map]
  · simp [hInside, initialCellSymbol]

theorem pairedInitialSymbolFor_eq_ofInput {language : Language}
    (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1))
    (certificateBit : Fin problem.certificateLimit → Bool)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.pairedInitialSymbolFor length certificateBit position =
      (Tape.ofInput
        (BitString.pair problem.input
          (certificateOf problem.certificateLimit length certificateBit))).symbolAt
        problem.uniformFuel position.val := by
  unfold pairedInitialSymbolFor
  rw [initialCellAt_symbol, Tape.symbolAt_ofInput]
  rw [map_pairedInitialCells]

theorem pairedInitialRowFor_represents {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.verifier.program.inputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (certificateBit : Fin problem.certificateLimit → Bool) :
    problem.pairedInitialRowFor length certificateBit |>.Represents
      (problem.initial
        (certificateOf problem.certificateLimit length certificateBit)) := by
  constructor
  · rfl
  · intro position
    change problem.pairedInitialSymbolFor length certificateBit position =
      (Tape.ofInput
        (problem.rawInput
          (certificateOf problem.certificateLimit length certificateBit))).symbolAt
        problem.uniformFuel position.val
    have hRawInput :
        problem.rawInput
            (certificateOf problem.certificateLimit length certificateBit) =
          BitString.pair problem.input
            (certificateOf problem.certificateLimit length certificateBit) := by
      unfold rawInput
      rw [hMode]
      rfl
    rw [hRawInput]
    exact problem.pairedInitialSymbolFor_eq_ofInput length certificateBit
      position

set_option maxRecDepth 10000 in
theorem advance_eq_localAction {language : Language}
    (problem : VerifierTableauProblem language)
    (row : problem.FiniteRow) (config : Configuration)
    (hRepresents : row.Represents config) :
    advance problem.rawMachine config =
      { state :=
          (problem.localAction row.state (row.symbol row.head)).targetState.val
        tape :=
          (config.tape.write
            (problem.localAction row.state
              (row.symbol row.head)).writeSymbol).move
            (problem.localAction row.state
              (row.symbol row.head)).move } := by
  rcases hRepresents with ⟨hState, hSymbols⟩
  have hHeadSymbol : row.symbol row.head = config.tape.head := by
    rw [hSymbols row.head]
    exact Tape.symbolAt_head config.tape row.head.val
  rcases config with ⟨configState, tape⟩
  change row.state.val = configState at hState
  subst configState
  rcases tape with ⟨left, tapeHead, right⟩
  change row.symbol row.head = tapeHead at hHeadSymbol
  subst tapeHead
  unfold advance localAction step?
  unfold Machine.isHalted
  cases hHalted :
      (row.state.val == problem.rawMachine.acceptState ||
        row.state.val == problem.rawMachine.rejectState) with
  | true =>
      simp [Tape.write, Tape.move]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      next hStepNone =>
        split
        next hRuleNone => rfl
        next rule hRuleSome =>
          simp [hRuleSome] at hStepNone
      next selected hStepSelected =>
        split
        next hRuleNone =>
          simp [hRuleNone] at hStepSelected
        next rule hRuleSome =>
          have hApply :
              applyRule rule
                  { state := row.state.val
                    tape :=
                      { left := left
                        head := row.symbol row.head
                        right := right } } = selected := by
            simpa [hRuleSome] using hStepSelected
          rw [← hApply]
          rfl

theorem FiniteRow.next_represents_advance {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) (config : Configuration)
    (hRepresents : row.Represents config)
    (hPositive : 0 < row.head.val)
    (hInside : row.head.val + 1 <
      problem.dimensions.tapeWidth problem.tableauInputMode) :
    row.next.Represents (advance problem.rawMachine config) := by
  let action := problem.localAction row.state (row.symbol row.head)
  rw [problem.advance_eq_localAction row config hRepresents]
  constructor
  · rfl
  · intro position
    have hSymbols := hRepresents.right
    change
      (if position = row.head then action.writeSymbol
       else row.symbol position) =
        ((config.tape.write action.writeSymbol).move action.move).symbolAt
          (movePosition row.head action.move).val position.val
    have hMovement :
        (movePosition row.head action.move).val =
          match action.move with
          | .left => row.head.val - 1
          | .stay => row.head.val
          | .right => row.head.val + 1 := by
      cases hMove : action.move with
      | left => rfl
      | stay => rfl
      | right =>
          unfold movePosition
          simp [hInside]
    rw [hMovement]
    have hTape := Tape.symbolAt_write_move config.tape action.writeSymbol
      action.move row.head.val position.val hPositive
    rw [hTape]
    by_cases hPosition : position = row.head
    · subst position
      simp
    · have hValue : position.val ≠ row.head.val := by
        intro hEqual
        exact hPosition (Fin.ext hEqual)
      simp [hPosition, hValue, hSymbols position]

theorem movePosition_le_add_one {width : Nat} (position : Fin width)
    (move : HeadMove) :
    (movePosition position move).val ≤ position.val + 1 := by
  cases move with
  | left =>
      change position.val - 1 ≤ position.val + 1
      omega
  | stay =>
      change position.val ≤ position.val + 1
      omega
  | right =>
      change
        (if hNext : position.val + 1 < width then
          (⟨position.val + 1, hNext⟩ : Fin width)
        else position).val ≤ position.val + 1
      split
      next hNext => change position.val + 1 ≤ position.val + 1; omega
      next hNext => change position.val ≤ position.val + 1; omega

theorem le_movePosition_add_one {width : Nat} (position : Fin width)
    (move : HeadMove) :
    position.val ≤ (movePosition position move).val + 1 := by
  cases move with
  | left =>
      change position.val ≤ position.val - 1 + 1
      omega
  | stay =>
      change position.val ≤ position.val + 1
      omega
  | right =>
      change position.val ≤
        (if hNext : position.val + 1 < width then
          (⟨position.val + 1, hNext⟩ : Fin width)
        else position).val + 1
      split
      next hNext => change position.val ≤ position.val + 1 + 1; omega
      next hNext => change position.val ≤ position.val + 1; omega

theorem FiniteRow.next_head_le_add_one {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) :
    row.next.head.val ≤ row.head.val + 1 := by
  exact movePosition_le_add_one row.head
    (problem.localAction row.state (row.symbol row.head)).move

theorem FiniteRow.head_le_next_add_one {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) :
    row.head.val ≤ row.next.head.val + 1 := by
  exact le_movePosition_add_one row.head
    (problem.localAction row.state (row.symbol row.head)).move

/-- Iterate the literal finite-row successor.  The recursive shape mirrors
the raw interpreter: one successor is taken before the remaining budget. -/
def finiteRun {language : Language}
    {problem : VerifierTableauProblem language} :
    Nat → problem.FiniteRow → problem.FiniteRow
  | 0, row => row
  | fuel + 1, row => finiteRun fuel row.next

@[simp] theorem finiteRun_zero {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) :
    finiteRun 0 row = row := rfl

theorem finiteRun_succ_start {language : Language}
    {problem : VerifierTableauProblem language}
    (fuel : Nat) (row : problem.FiniteRow) :
    finiteRun (fuel + 1) row = finiteRun fuel row.next := rfl

/-- The same iteration can be exposed at its final step. -/
theorem finiteRun_succ_end {language : Language}
    {problem : VerifierTableauProblem language}
    (fuel : Nat) (row : problem.FiniteRow) :
    finiteRun (fuel + 1) row = (finiteRun fuel row).next := by
  induction fuel generalizing row with
  | zero => rfl
  | succ fuel ih =>
      change finiteRun (fuel + 1) row.next =
        (finiteRun (fuel + 1) row).next
      rw [ih row.next]
      rfl

theorem finiteRun_head_bounds {language : Language}
    {problem : VerifierTableauProblem language}
    (initial : problem.FiniteRow)
    (hInitialHead : initial.head = problem.initialHeadPosition)
    (fuel : Nat) :
    problem.uniformFuel ≤ (finiteRun fuel initial).head.val + fuel ∧
      (finiteRun fuel initial).head.val ≤ problem.uniformFuel + fuel := by
  induction fuel with
  | zero =>
      rw [finiteRun_zero, hInitialHead]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ fuel ih =>
      rw [finiteRun_succ_end]
      constructor
      · have stepBound :=
          (finiteRun fuel initial).head_le_next_add_one
        omega
      · have stepBound :=
          (finiteRun fuel initial).next_head_le_add_one
        omega

theorem finiteRun_head_positive_of_lt {language : Language}
    {problem : VerifierTableauProblem language}
    (initial : problem.FiniteRow)
    (hInitialHead : initial.head = problem.initialHeadPosition)
    (fuel : Nat) (hFuel : fuel < problem.uniformFuel) :
    0 < (finiteRun fuel initial).head.val := by
  have bounds := problem.finiteRun_head_bounds initial hInitialHead fuel
  omega

theorem finiteRun_head_inside_of_lt {language : Language}
    {problem : VerifierTableauProblem language}
    (initial : problem.FiniteRow)
    (hInitialHead : initial.head = problem.initialHeadPosition)
    (fuel : Nat) (hFuel : fuel < problem.uniformFuel) :
    (finiteRun fuel initial).head.val + 1 <
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  have bounds := problem.finiteRun_head_bounds initial hInitialHead fuel
  have hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode =
        problem.dimensions.encodedInputLength problem.tableauInputMode +
          2 * problem.uniformFuel + 1 := by
    unfold Dimensions.tapeWidth
    rw [problem.dimensions_timeBound]
  omega

theorem advance_run_commute (machine : Machine) (fuel : Nat)
    (config : Configuration) :
    advance machine (run machine fuel config) =
      run machine fuel (advance machine config) := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      rw [run_succ_eq_run_advance, run_succ_eq_run_advance]
      exact ih (advance machine config)

theorem run_succ_eq_advance_run (machine : Machine) (fuel : Nat)
    (config : Configuration) :
    run machine (fuel + 1) config =
      advance machine (run machine fuel config) := by
  rw [run_succ_eq_run_advance]
  exact (advance_run_commute machine fuel config).symm

theorem finiteRun_represents_run {language : Language}
    {problem : VerifierTableauProblem language}
    (initial : problem.FiniteRow) (config : Configuration)
    (hInitialHead : initial.head = problem.initialHeadPosition)
    (hRepresents : initial.Represents config)
    (fuel : Nat) (hFuel : fuel ≤ problem.uniformFuel) :
    (finiteRun fuel initial).Represents
      (run problem.rawMachine fuel config) := by
  induction fuel with
  | zero => simpa using hRepresents
  | succ fuel ih =>
      have hBefore : fuel < problem.uniformFuel := by omega
      rw [finiteRun_succ_end, run_succ_eq_advance_run]
      exact (finiteRun fuel initial).next_represents_advance
        (run problem.rawMachine fuel config)
        (ih (by omega))
        (problem.finiteRun_head_positive_of_lt initial hInitialHead fuel
          hBefore)
        (problem.finiteRun_head_inside_of_lt initial hInitialHead fuel hBefore)

/-- Canonical finite row at each represented time. -/
def finiteExecution {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) : problem.FiniteTableau :=
  fun time => finiteRun time.val initial

@[simp] theorem finiteExecution_initial {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) :
    problem.finiteExecution initial problem.initialTime = initial := rfl

theorem finiteExecution_transitions {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) :
    problem.FiniteTransitions (problem.finiteExecution initial) := by
  intro step
  change finiteRun (step.val + 1) initial =
    (finiteRun step.val initial).next
  exact finiteRun_succ_end step.val initial

def boundedTime {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Nat) (hTime : time ≤ problem.uniformFuel) :
    Fin problem.dimensions.timeCount :=
  ⟨time, by
    change time < problem.uniformFuel + 1
    omega⟩

theorem finiteTransitions_eq_finiteRun_at {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) (tableau : problem.FiniteTableau)
    (hInitial : tableau problem.initialTime = initial)
    (hTransitions : problem.FiniteTransitions tableau)
    (time : Nat) (hTime : time ≤ problem.uniformFuel) :
    tableau (problem.boundedTime time hTime) = finiteRun time initial := by
  induction time with
  | zero =>
      calc
        tableau (problem.boundedTime 0 hTime) =
            tableau problem.initialTime := by
              congr 1
        _ = initial := hInitial
        _ = finiteRun 0 initial := rfl
  | succ time ih =>
      have hStep : time < problem.uniformFuel := by omega
      let step : Fin problem.uniformFuel := ⟨time, hStep⟩
      have hPrevious : time ≤ problem.uniformFuel := by omega
      calc
        tableau (problem.boundedTime (time + 1) hTime) =
            tableau (problem.nextTime step) := by
              congr 1
        _ = (tableau (problem.currentTime step)).next :=
          hTransitions step
        _ = (tableau (problem.boundedTime time hPrevious)).next := by
          congr 2
        _ = (finiteRun time initial).next := congrArg FiniteRow.next
          (ih hPrevious)
        _ = finiteRun (time + 1) initial :=
          (finiteRun_succ_end time initial).symm

theorem finiteTransitions_eq_finiteExecution {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) (tableau : problem.FiniteTableau)
    (hInitial : tableau problem.initialTime = initial)
    (hTransitions : problem.FiniteTransitions tableau) :
    tableau = problem.finiteExecution initial := by
  funext time
  have hTime : time.val ≤ problem.uniformFuel := by
    have hLt := time.isLt
    change time.val < problem.uniformFuel + 1 at hLt
    omega
  calc
    tableau time = tableau (problem.boundedTime time.val hTime) := by
      congr 1
    _ = finiteRun time.val initial :=
      problem.finiteTransitions_eq_finiteRun_at initial tableau hInitial
        hTransitions time.val hTime
    _ = problem.finiteExecution initial time := rfl

theorem finiteExecution_final_represents_run {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) (config : Configuration)
    (hInitialHead : initial.head = problem.initialHeadPosition)
    (hRepresents : initial.Represents config) :
    (problem.finiteExecution initial problem.finalTime).Represents
      (run problem.rawMachine problem.uniformFuel config) := by
  exact problem.finiteRun_represents_run initial config hInitialHead
    hRepresents problem.uniformFuel (Nat.le_refl _)

/-- Finite accepting tableaux from a represented initial row are equivalent
to the raw run ending in the designated accept state. -/
theorem exists_finiteAcceptingFrom_iff_run_accept {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow) (config : Configuration)
    (hInitialHead : initial.head = problem.initialHeadPosition)
    (hRepresents : initial.Represents config) :
    (∃ tableau, problem.FiniteAcceptingFrom initial tableau) ↔
      (run problem.rawMachine problem.uniformFuel config).state =
        problem.rawMachine.acceptState := by
  have hFinal := problem.finiteExecution_final_represents_run initial config
    hInitialHead hRepresents
  constructor
  · intro hExists
    rcases hExists with ⟨tableau, hInitial, hTransitions, hAccept⟩
    have hTableau := problem.finiteTransitions_eq_finiteExecution initial
      tableau hInitial hTransitions
    have hState := congrArg
      (fun row : problem.FiniteRow => row.state) (congrFun hTableau problem.finalTime)
    have hRawState := hFinal.left
    rw [hAccept] at hState
    exact hRawState.symm.trans (congrArg Fin.val hState).symm
  · intro hAccept
    refine ⟨problem.finiteExecution initial,
      problem.finiteExecution_initial initial,
      problem.finiteExecution_transitions initial, ?_⟩
    apply Fin.ext
    change (problem.finiteExecution initial problem.finalTime).state.val =
      problem.rawMachine.acceptState
    exact hFinal.left.trans hAccept

/-- The finite tableau formula is semantically exact for the concrete NP
verifier on this source input.  This theorem is deliberately prior to the
external reduction-size and construction-runtime bounds. -/
theorem hasFiniteAccepting_iff_language {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.HasFiniteAcceptingTableau ↔ language problem.input := by
  cases hMode : problem.verifier.program.inputMode with
  | inputOnly =>
      unfold HasFiniteAcceptingTableau
      rw [hMode]
      constructor
      · intro hFinite
        have hRun :=
          (problem.exists_finiteAcceptingFrom_iff_run_accept
            problem.inputOnlyInitialRow (problem.initial []) rfl
            (problem.inputOnlyInitialRow_represents hMode)).mp hFinite
        have hBounded :
            boundedDecide problem.rawMachine problem.uniformFuel
                (problem.rawInput []) = .accept :=
          (boundedDecide_accept_iff_final problem.rawMachine
            problem.uniformFuel (problem.rawInput [])).mpr hRun
        have hProgram :
            problem.verifier.program.verdict problem.input [] = .accept := by
          rw [← problem.uniformFuel_verdict_eq [] (Nat.zero_le _)]
          exact hBounded
        apply (problem.verifier.accepts_iff problem.input).mpr
        exact ⟨[], Nat.zero_le _, hProgram⟩
      · intro hLanguage
        rcases (problem.verifier.accepts_iff problem.input).mp hLanguage with
          ⟨certificate, hCertificate, hAccept⟩
        have hEmptyAccept :
            problem.verifier.program.verdict problem.input [] = .accept := by
          unfold VerifierProgram.verdict at hAccept ⊢
          rw [hMode] at hAccept ⊢
          exact hAccept
        have hBounded :
            boundedDecide problem.rawMachine problem.uniformFuel
                (problem.rawInput []) = .accept := by
          rw [problem.uniformFuel_verdict_eq [] (Nat.zero_le _)]
          exact hEmptyAccept
        have hRun :
            (run problem.rawMachine problem.uniformFuel
              (problem.initial [])).state =
                problem.rawMachine.acceptState :=
          (boundedDecide_accept_iff_final problem.rawMachine
            problem.uniformFuel (problem.rawInput [])).mp hBounded
        exact (problem.exists_finiteAcceptingFrom_iff_run_accept
          problem.inputOnlyInitialRow (problem.initial []) rfl
          (problem.inputOnlyInitialRow_represents hMode)).mpr hRun
  | paired =>
      unfold HasFiniteAcceptingTableau
      rw [hMode]
      constructor
      · intro hFinite
        rcases hFinite with
          ⟨length, certificateBit, tableau, hAccepting⟩
        let certificate := certificateOf problem.certificateLimit length
          certificateBit
        have hCertificate :
            BitString.size certificate ≤ problem.certificateLimit := by
          change certificate.length ≤ problem.certificateLimit
          rw [certificateOf_length]
          exact Nat.lt_succ_iff.mp length.isLt
        have hRun :=
          (problem.exists_finiteAcceptingFrom_iff_run_accept
            (problem.pairedInitialRowFor length certificateBit)
            (problem.initial certificate) rfl
            (problem.pairedInitialRowFor_represents hMode length
              certificateBit)).mp ⟨tableau, hAccepting⟩
        have hBounded :
            boundedDecide problem.rawMachine problem.uniformFuel
                (problem.rawInput certificate) = .accept :=
          (boundedDecide_accept_iff_final problem.rawMachine
            problem.uniformFuel (problem.rawInput certificate)).mpr hRun
        have hProgram :
            problem.verifier.program.verdict problem.input certificate =
              .accept := by
          rw [← problem.uniformFuel_verdict_eq certificate hCertificate]
          exact hBounded
        apply (problem.verifier.accepts_iff problem.input).mpr
        exact ⟨certificate, hCertificate, hProgram⟩
      · intro hLanguage
        rcases (problem.verifier.accepts_iff problem.input).mp hLanguage with
          ⟨certificate, hCertificate, hAccept⟩
        change certificate.length ≤ problem.certificateLimit at hCertificate
        let length : Fin (problem.certificateLimit + 1) :=
          ⟨certificate.length, Nat.lt_succ_of_le hCertificate⟩
        let certificateBit : Fin problem.certificateLimit → Bool :=
          certificateBitOf certificate
        have hCertificateEq :
            certificateOf problem.certificateLimit length certificateBit =
              certificate := by
          simpa [length, certificateBit] using
            (certificateOf_certificate problem.certificateLimit certificate
              hCertificate)
        have hBounded :
            boundedDecide problem.rawMachine problem.uniformFuel
                (problem.rawInput certificate) = .accept := by
          rw [problem.uniformFuel_verdict_eq certificate]
          · exact hAccept
          · exact hCertificate
        have hRun :
            (run problem.rawMachine problem.uniformFuel
              (problem.initial certificate)).state =
                problem.rawMachine.acceptState :=
          (boundedDecide_accept_iff_final problem.rawMachine
            problem.uniformFuel (problem.rawInput certificate)).mp hBounded
        have hReconstructedRun :
            (run problem.rawMachine problem.uniformFuel
              (problem.initial
                (certificateOf problem.certificateLimit length
                  certificateBit))).state =
                problem.rawMachine.acceptState := by
          rw [hCertificateEq]
          exact hRun
        rcases (problem.exists_finiteAcceptingFrom_iff_run_accept
          (problem.pairedInitialRowFor length certificateBit)
          (problem.initial
            (certificateOf problem.certificateLimit length certificateBit))
          rfl
          (problem.pairedInitialRowFor_represents hMode length
            certificateBit)).mpr hReconstructedRun with
          ⟨tableau, hAccepting⟩
        exact ⟨length, certificateBit, tableau, hAccepting⟩

theorem formula_satisfiable_iff_language {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formula.Satisfiable ↔ language problem.input :=
  problem.formula_satisfiable_iff_finiteAccepting.trans
    problem.hasFiniteAccepting_iff_language

/-- Exact semantic Cook--Levin bridge for the canonical encoded formula.
No NP-hardness or polynomial construction claim is made here. -/
theorem encodedFormula_mem_CNFSAT_iff_language {language : Language}
    (problem : VerifierTableauProblem language) :
    CNFSAT problem.encodedFormula ↔ language problem.input :=
  problem.encodedFormula_mem_CNFSAT_iff_finiteAccepting.trans
    problem.hasFiniteAccepting_iff_language

end VerifierTableauProblem

end CookLevin

end PNP.Concrete
