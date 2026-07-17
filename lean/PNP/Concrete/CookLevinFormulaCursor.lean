/-
Copyright (c) 2026 PNP Labs.

Direct coordinate lookup and a fuelled specification cursor for the concrete
Cook--Levin formula schedule.

The executable definitions in this file do not construct the whole scheduled
program, formula, token stream, or encoded formula in order to answer one slot.
They are nevertheless Lean-level specification functions, not raw finite
machines.  No constant-time raw interpretation or construction-runtime claim
is made here.
-/

import PNP.Concrete.CookLevinFormulaSchedule

namespace PNP.Concrete

namespace CookLevin

/-! ### Generic direct lookup combinators -/

namespace DirectSlot

/-- Direct lookup in a singleton without allocating a coordinate list. -/
def singleton (value : α) : Nat → Option α
  | 0 => some value
  | _ + 1 => none

theorem singleton_eq_getElem?_singleton (value : α) (index : Nat) :
    singleton value index = [value][index]? := by
  cases index <;> rfl

/-- Direct lookup in a concatenation when the left length is already known. -/
def append (leftLength : Nat) (left right : Nat → Option α)
    (index : Nat) : Option α :=
  if index < leftLength then left index else right (index - leftLength)

theorem append_eq_getElem?_append (left right : List α)
    (leftSlot rightSlot : Nat → Option α)
    (hLeft : ∀ index, leftSlot index = left[index]?)
    (hRight : ∀ index, rightSlot index = right[index]?)
    (index : Nat) :
    append left.length leftSlot rightSlot index = (left ++ right)[index]? := by
  rw [List.getElem?_append]
  unfold append
  split <;> simp_all

/-- Direct lookup in a finite sequence of variable-width blocks.  The outer
coordinate is consumed recursively; no list of outer coordinates or flattened
output is constructed. -/
def flatFinite : (count : Nat) →
    (Fin count → Nat → Option α) → (Fin count → Nat) → Nat → Option α
  | 0, _, _, _ => none
  | count + 1, blockSlot, blockLength, index =>
      if index < blockLength ⟨0, Nat.zero_lt_succ count⟩ then
        blockSlot ⟨0, Nat.zero_lt_succ count⟩ index
      else
        flatFinite count
          (fun coordinate => blockSlot coordinate.succ)
          (fun coordinate => blockLength coordinate.succ)
          (index - blockLength ⟨0, Nat.zero_lt_succ count⟩)

/-- Total width of the same finite variable-width block family. -/
def totalWidth : (count : Nat) → (Fin count → Nat) → Nat
  | 0, _ => 0
  | count + 1, blockLength =>
      blockLength ⟨0, Nat.zero_lt_succ count⟩ +
        totalWidth count (fun coordinate => blockLength coordinate.succ)

theorem totalWidth_eq_flatMap_length (count : Nat)
    (blocks : Fin count → List α) (blockLength : Fin count → Nat)
    (hLength : ∀ coordinate,
      blockLength coordinate = (blocks coordinate).length) :
    totalWidth count blockLength =
      ((finiteIndices count).flatMap blocks).length := by
  induction count with
  | zero => rfl
  | succ count ih =>
      unfold totalWidth finiteIndices
      simp only [List.flatMap_cons, List.flatMap_map, List.length_append]
      rw [hLength ⟨0, Nat.zero_lt_succ count⟩]
      apply congrArg ((blocks ⟨0, Nat.zero_lt_succ count⟩).length + ·)
      apply ih
      intro coordinate
      exact hLength coordinate.succ

theorem flatFinite_eq_getElem?_flatMap
    (count : Nat) (blocks : Fin count → List α)
    (blockSlot : Fin count → Nat → Option α)
    (blockLength : Fin count → Nat)
    (hSlot : ∀ coordinate index,
      blockSlot coordinate index = (blocks coordinate)[index]?)
    (hLength : ∀ coordinate,
      blockLength coordinate = (blocks coordinate).length)
    (index : Nat) :
    flatFinite count blockSlot blockLength index =
      ((finiteIndices count).flatMap blocks)[index]? := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
      unfold flatFinite finiteIndices
      simp only [List.flatMap_cons, List.flatMap_map]
      rw [List.getElem?_append]
      rw [← hLength ⟨0, Nat.zero_lt_succ count⟩]
      split
      · exact hSlot ⟨0, Nat.zero_lt_succ count⟩ index
      · apply ih
        · intro coordinate next
          exact hSlot coordinate.succ next
        · intro coordinate
          exact hLength coordinate.succ

/-- Direct lookup in a fixed-width block sequence. -/
def rectangle (count width : Nat)
    (blockSlot : Fin count → Nat → Option α) (index : Nat) : Option α :=
  flatFinite count blockSlot (fun _ => width) index

theorem rectangle_eq_getElem?_flatMap
    (count width : Nat) (blocks : Fin count → List α)
    (blockSlot : Fin count → Nat → Option α)
    (hSlot : ∀ coordinate index,
      blockSlot coordinate index = (blocks coordinate)[index]?)
    (hLength : ∀ coordinate, (blocks coordinate).length = width)
    (index : Nat) :
    rectangle count width blockSlot index =
      ((finiteIndices count).flatMap blocks)[index]? := by
  apply flatFinite_eq_getElem?_flatMap count blocks blockSlot
      (fun _ => width)
  · exact hSlot
  · intro coordinate
    exact (hLength coordinate).symm

/-- Turn direct lookup in an ordinary list into lookup in its padded option
schedule.  Coordinates below `bound` are valid schedule slots, including
coordinates at which the source list is already exhausted. -/
def pad (bound : Nat) (itemSlot : Nat → Option α) (index : Nat) :
    Option (Option α) :=
  if index < bound then some (itemSlot index) else none

theorem pad_eq_getElem?_pad (bound : Nat) (items : List α)
    (itemSlot : Nat → Option α)
    (hSlot : ∀ index, itemSlot index = items[index]?)
    (hLength : items.length ≤ bound) (index : Nat) :
    pad bound itemSlot index = (FormulaSchedule.pad bound items)[index]? := by
  unfold pad FormulaSchedule.pad
  rw [List.getElem?_append, List.length_map, List.getElem?_map]
  split <;> rename_i hBound
  · by_cases hItems : index < items.length
    · rw [if_pos hItems, hSlot]
      rw [List.getElem?_eq_getElem hItems]
      rfl
    · rw [if_neg hItems]
      have hOffset : index - items.length < bound - items.length := by omega
      rw [List.getElem?_replicate, if_pos hOffset]
      rw [hSlot, List.getElem?_eq_none (by omega)]
  · have hItems : ¬ index < items.length := by omega
    rw [if_neg hItems]
    by_cases hOffset : index - items.length < bound - items.length
    · omega
    · rw [List.getElem?_replicate, if_neg hOffset]

/-- Lookup in a list generated pointwise over one finite initial segment. -/
def finiteMap (count : Nat) (value : Fin count → α) (index : Nat) : Option α :=
  if h : index < count then some (value ⟨index, h⟩) else none

theorem finiteIndices_eq_ofFn (count : Nat) :
    finiteIndices count = List.ofFn (fun index : Fin count => index) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      unfold finiteIndices
      rw [ih]
      apply List.ext_getElem?
      intro index
      simp only [List.getElem?_ofFn]
      by_cases hZero : index = 0
      · subst index
        simp
      · cases index with
        | zero => exact False.elim (hZero rfl)
        | succ previous =>
            by_cases hPrevious : previous < count
            · simp [hPrevious]
            · have hIndex : ¬ Nat.succ previous < Nat.succ count := by omega
              simp [hIndex]

theorem finiteMap_eq_getElem?_map (count : Nat) (value : Fin count → α)
    (index : Nat) :
    finiteMap count value index =
      ((finiteIndices count).map value)[index]? := by
  rw [finiteIndices_eq_ofFn, List.getElem?_map, List.getElem?_ofFn]
  unfold finiteMap
  split <;> rfl

end DirectSlot

/-! ### Direct local-clause coordinates -/

namespace LocalConstraint

/-- Direct lookup in the pair-exclusion clauses contributed by one leading
variable. -/
def excludeWithClauseSlotDirect {width : Nat} (first : Fin width) :
    List (Fin width) → Nat → Option (BoundedClause width)
  | [], _ => none
  | next :: _, 0 => some (excludeBoundedPairClause first next)
  | _ :: rest, index + 1 => excludeWithClauseSlotDirect first rest index

theorem excludeWithClauseSlotDirect_eq {width : Nat} (first : Fin width)
    (rest : List (Fin width)) (index : Nat) :
    excludeWithClauseSlotDirect first rest index =
      (excludeBoundedWithClauses first rest)[index]? := by
  induction rest generalizing index with
  | nil => rfl
  | cons next rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

/-- Direct lookup in the recursively ordered pair-exclusion clauses. -/
def atMostOneClauseSlotDirect {width : Nat} :
    List (Fin width) → Nat → Option (BoundedClause width)
  | [], _ => none
  | first :: rest, index =>
      DirectSlot.append rest.length
        (excludeWithClauseSlotDirect first rest)
        (atMostOneClauseSlotDirect rest) index

theorem atMostOneClauseSlotDirect_eq {width : Nat}
    (variables : List (Fin width)) (index : Nat) :
    atMostOneClauseSlotDirect variables index =
      (atMostOneBoundedClauses variables)[index]? := by
  induction variables generalizing index with
  | nil => rfl
  | cons first rest ih =>
      unfold atMostOneClauseSlotDirect atMostOneBoundedClauses
      rw [← excludeBoundedWithClauses_length first rest]
      apply DirectSlot.append_eq_getElem?_append
      · exact excludeWithClauseSlotDirect_eq first rest
      · exact ih

/-- Direct lookup in the clauses emitted by one local constraint.  It follows
the syntax tree and never constructs the emitted clause list. -/
def clauseSlotDirect {width : Nat} :
    LocalConstraint width → Nat → Option (BoundedClause width)
  | .require literal, 0 => some [literal]
  | .require _, _ + 1 => none
  | .implication premises conclusion, 0 =>
      some (implicationClause premises conclusion)
  | .implication _ _, _ + 1 => none
  | .exactlyOne variables, 0 => some (atLeastOneBoundedClause variables)
  | .exactlyOne variables, index + 1 =>
      atMostOneClauseSlotDirect variables index

theorem clauseSlotDirect_eq_emit_getElem? {width : Nat}
    (constraint : LocalConstraint width) (index : Nat) :
    clauseSlotDirect constraint index = (constraint.emit)[index]? := by
  cases constraint with
  | require literal => cases index <;> rfl
  | implication premises conclusion => cases index <;> rfl
  | exactlyOne variables =>
      cases index with
      | zero => rfl
      | succ index => exact atMostOneClauseSlotDirect_eq variables index

end LocalConstraint

/-! ### Direct canonical-token coordinates -/

namespace DirectToken

/-- Direct coordinate decoder for `T^count F`. -/
def unarySlot : Nat → Nat → Option CNFToken
  | 0, 0 => some .f
  | 0, _ + 1 => none
  | _ + 1, 0 => some .t
  | count + 1, index + 1 => unarySlot count index

theorem unarySlot_eq_encodeUnaryTokens_getElem? (count index : Nat) :
    unarySlot count index = (encodeUnaryTokens count)[index]? := by
  induction count generalizing index with
  | zero => cases index <;> rfl
  | succ count ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

/-- Direct coordinate decoder for the sign and unary variable index of one
literal. -/
def literalSlot (literal : CNFLiteral) : Nat → Option CNFToken
  | 0 => some (if literal.positive then .t else .f)
  | index + 1 => unarySlot literal.variableIndex index

theorem literalSlot_eq_encodeLiteralTokens_getElem?
    (literal : CNFLiteral) (index : Nat) :
    literalSlot literal index = (encodeLiteralTokens literal)[index]? := by
  cases index with
  | zero => rfl
  | succ index =>
      exact unarySlot_eq_encodeUnaryTokens_getElem?
        literal.variableIndex index

/-- Exact token width of one bounded literal, computed without encoding it. -/
def boundedLiteralWidth {width : Nat} (literal : BoundedLiteral width) : Nat :=
  literal.index.val + 2

theorem boundedLiteralWidth_eq_encodeLiteralTokens_length {width : Nat}
    (literal : BoundedLiteral width) :
    boundedLiteralWidth literal =
      (encodeLiteralTokens literal.emit).length := by
  rw [encodeLiteralTokens_length]
  rfl

/-- Exact token width of a bounded clause's literal payload. -/
def boundedLiteralListWidth {width : Nat} : List (BoundedLiteral width) → Nat
  | [] => 0
  | literal :: rest =>
      boundedLiteralWidth literal + boundedLiteralListWidth rest

/-- Direct lookup through the variable-width literal payload of a bounded
clause. -/
def boundedLiteralListSlot {width : Nat} :
    List (BoundedLiteral width) → Nat → Option CNFToken
  | [], _ => none
  | literal :: rest, index =>
      DirectSlot.append (boundedLiteralWidth literal)
        (literalSlot literal.emit)
        (boundedLiteralListSlot rest) index

theorem boundedLiteralListWidth_eq_length {width : Nat}
    (clause : List (BoundedLiteral width)) :
    boundedLiteralListWidth clause =
      (encodeLiteralListTokens (BoundedClause.emit clause)).length := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      unfold boundedLiteralListWidth BoundedClause.emit
      change boundedLiteralWidth literal + boundedLiteralListWidth rest =
        (encodeLiteralTokens literal.emit ++
          encodeLiteralListTokens (BoundedClause.emit rest)).length
      rw [List.length_append, ← boundedLiteralWidth_eq_encodeLiteralTokens_length,
        ih]

theorem boundedLiteralListSlot_eq_getElem? {width : Nat}
    (clause : List (BoundedLiteral width)) (index : Nat) :
    boundedLiteralListSlot clause index =
      (encodeLiteralListTokens (BoundedClause.emit clause))[index]? := by
  induction clause generalizing index with
  | nil => rfl
  | cons literal rest ih =>
      unfold boundedLiteralListSlot BoundedClause.emit
      change DirectSlot.append (boundedLiteralWidth literal)
          (literalSlot literal.emit) (boundedLiteralListSlot rest) index =
        (encodeLiteralTokens literal.emit ++
          encodeLiteralListTokens (BoundedClause.emit rest))[index]?
      rw [boundedLiteralWidth_eq_encodeLiteralTokens_length]
      apply DirectSlot.append_eq_getElem?_append
      · exact literalSlot_eq_encodeLiteralTokens_getElem? literal.emit
      · exact ih

/-- Direct token lookup for one bounded clause, including separator and
terminal token. -/
def clauseSlot {width : Nat} (clause : BoundedClause width) (index : Nat) :
    Option CNFToken :=
  DirectSlot.append 1 (DirectSlot.singleton .sep)
    (DirectSlot.append (boundedLiteralListWidth clause)
      (boundedLiteralListSlot clause) (DirectSlot.singleton .finish)) index

theorem clauseSlot_eq_encodeClauseTokens_getElem? {width : Nat}
    (clause : BoundedClause width) (index : Nat) :
    clauseSlot clause index =
      (encodeClauseTokens (BoundedClause.emit clause))[index]? := by
  unfold clauseSlot encodeClauseTokens
  change DirectSlot.append [CNFToken.sep].length
      (DirectSlot.singleton .sep)
      (DirectSlot.append (boundedLiteralListWidth clause)
        (boundedLiteralListSlot clause) (DirectSlot.singleton .finish)) index =
    ([CNFToken.sep] ++
      (encodeLiteralListTokens (BoundedClause.emit clause) ++
        [CNFToken.finish]))[index]?
  apply DirectSlot.append_eq_getElem?_append
  · exact DirectSlot.singleton_eq_getElem?_singleton CNFToken.sep
  · rw [boundedLiteralListWidth_eq_length]
    apply DirectSlot.append_eq_getElem?_append
    · exact boundedLiteralListSlot_eq_getElem? clause
    · exact DirectSlot.singleton_eq_getElem?_singleton CNFToken.finish

end DirectToken

/-! ### Direct constraint coordinates -/

namespace VerifierTableauProblem

/-- Direct lookup in one row's symbol/head/state shape opportunities. -/
def shapeRowSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.append
    (problem.dimensions.tapeWidth problem.tableauInputMode)
    (DirectSlot.finiteMap
      (problem.dimensions.tapeWidth problem.tableauInputMode)
      (fun position => some (problem.symbolShapeAt time position)))
    (DirectSlot.append 1
      (DirectSlot.singleton (some (problem.headShapeAt time)))
      (DirectSlot.singleton (some (problem.stateShapeAt time)))) index

theorem shapeRowSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) (index : Nat) :
  problem.shapeRowSlotDirect time index =
      (((finiteIndices
          (problem.dimensions.tapeWidth problem.tableauInputMode)).map
            (fun position => some (problem.symbolShapeAt time position))) ++
        [some (problem.headShapeAt time),
          some (problem.stateShapeAt time)])[index]? := by
  have hRight : ∀ next,
      DirectSlot.append 1
          (DirectSlot.singleton (some (problem.headShapeAt time)))
          (DirectSlot.singleton (some (problem.stateShapeAt time))) next =
        [some (problem.headShapeAt time),
          some (problem.stateShapeAt time)][next]? := by
    intro next
    change DirectSlot.append [some (problem.headShapeAt time)].length
        (DirectSlot.singleton (some (problem.headShapeAt time)))
        (DirectSlot.singleton (some (problem.stateShapeAt time))) next =
      ([some (problem.headShapeAt time)] ++
        [some (problem.stateShapeAt time)])[next]?
    apply DirectSlot.append_eq_getElem?_append
    · exact DirectSlot.singleton_eq_getElem?_singleton _
    · exact DirectSlot.singleton_eq_getElem?_singleton _
  unfold shapeRowSlotDirect
  simpa [finiteIndices_length] using
    (DirectSlot.append_eq_getElem?_append
      ((finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)).map
          (fun position => some (problem.symbolShapeAt time position)))
      [some (problem.headShapeAt time), some (problem.stateShapeAt time)]
      (DirectSlot.finiteMap
        (problem.dimensions.tapeWidth problem.tableauInputMode)
        (fun position => some (problem.symbolShapeAt time position)))
      (DirectSlot.append 1
        (DirectSlot.singleton (some (problem.headShapeAt time)))
        (DirectSlot.singleton (some (problem.stateShapeAt time))))
      (DirectSlot.finiteMap_eq_getElem?_map _ _)
      hRight index)

/-- Direct lookup in the complete rectangular row-shape region. -/
def shapeConstraintSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle problem.dimensions.timeCount
    (problem.dimensions.tapeWidth problem.tableauInputMode + 2)
    problem.shapeRowSlotDirect index

theorem shapeConstraintSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.shapeConstraintSlotDirect index =
      problem.scheduledShapeConstraints[index]? := by
  unfold shapeConstraintSlotDirect scheduledShapeConstraints
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.shapeRowSlotDirect_eq
  · intro time
    simp [finiteIndices_length]

/-- Direct input-only initial symbol at one tape coordinate. -/
def inputOnlyInitialSymbolDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) : TapeSymbol :=
  initialCellSymbol (fun index : Fin 0 => Fin.elim0 index)
    (initialCellAtCoordinate (inputOnlyInitialCells problem.input)
      problem.uniformFuel position.val)

theorem inputOnlyInitialSymbolDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.inputOnlyInitialSymbolDirect position =
      problem.inputOnlyInitialSymbol position := by
  unfold inputOnlyInitialSymbolDirect inputOnlyInitialSymbol
  rw [initialCellAtCoordinate_eq_initialCellAt]

/-- Direct lookup in the unpadded input-only initial-symbol program. -/
def inputOnlySymbolsSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (LocalConstraint problem.FormulaWidth) :=
  DirectSlot.finiteMap
    (problem.dimensions.tapeWidth problem.tableauInputMode)
    (fun position => problem.fixedInitialCellConstraint position
      (problem.inputOnlyInitialSymbolDirect position)) index

theorem inputOnlySymbolsSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.inputOnlySymbolsSlotDirect index =
      problem.inputOnlyInitialSymbolsProgram[index]? := by
  unfold inputOnlySymbolsSlotDirect
  rw [DirectSlot.finiteMap_eq_getElem?_map]
  have hPrograms := problem.scheduledInputOnlyCells_emit_eq
  unfold scheduledInputOnlyCells at hPrograms
  rw [FormulaSchedule.emit_pad] at hPrograms
  unfold inputOnlyInitialSymbolDirect
  rw [hPrograms]

/-- Direct constraint count for one paired-input cell. -/
def pairedCellConstraintWidthDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) : Nat :=
  match initialCellAtCoordinate
      (pairedInitialCells problem.input problem.certificateLimit length)
      problem.uniformFuel position.val with
  | .blank => 1
  | .fixed _ => 1
  | .certificate _ => 2

/-- Direct lookup in the one- or two-constraint paired-input cell program. -/
def pairedCellConstraintSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    Nat → Option (LocalConstraint problem.FormulaWidth)
  | index =>
      let selectedLength := problem.pairedLengthLiteral hMode length
      match initialCellAtCoordinate
          (pairedInitialCells problem.input problem.certificateLimit length)
          problem.uniformFuel position.val with
      | .blank =>
          DirectSlot.singleton
            (.implication [selectedLength]
              (problem.symbolLiteral problem.initialTime position .blank)) index
      | .fixed value =>
          DirectSlot.singleton
            (.implication [selectedLength]
              (problem.symbolLiteral problem.initialTime position
                (symbolOfFixedBit value))) index
      | .certificate certificateIndex =>
          let bit := problem.pairedBitLiteral hMode certificateIndex
          DirectSlot.append 1
            (DirectSlot.singleton
              (.implication [selectedLength, bit]
                (problem.symbolLiteral problem.initialTime position .one)))
            (DirectSlot.singleton
              (.implication [selectedLength, bit.negate]
                (problem.symbolLiteral problem.initialTime position .zero))) index

theorem pairedCellConstraintWidthDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.pairedCellConstraintWidthDirect length position =
      (problem.pairedCellProgram hMode length position).length := by
  unfold pairedCellConstraintWidthDirect pairedCellProgram
  rw [← initialCellAtCoordinate_eq_initialCellAt]
  generalize initialCellAtCoordinate
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val = cell
  cases cell <;> rfl

theorem pairedCellConstraintSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    problem.pairedCellConstraintSlotDirect hMode length position index =
      (problem.pairedCellProgram hMode length position)[index]? := by
  unfold pairedCellConstraintSlotDirect pairedCellProgram
  rw [← initialCellAtCoordinate_eq_initialCellAt]
  generalize initialCellAtCoordinate
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val = cell
  cases cell with
  | blank => exact DirectSlot.singleton_eq_getElem?_singleton _ index
  | fixed value => exact DirectSlot.singleton_eq_getElem?_singleton _ index
  | certificate certificateIndex =>
      let first : LocalConstraint problem.FormulaWidth :=
        .implication
            [problem.pairedLengthLiteral hMode length,
              problem.pairedBitLiteral hMode certificateIndex]
            (problem.symbolLiteral problem.initialTime position .one)
      let second : LocalConstraint problem.FormulaWidth :=
        .implication
            [problem.pairedLengthLiteral hMode length,
              (problem.pairedBitLiteral hMode certificateIndex).negate]
            (problem.symbolLiteral problem.initialTime position .zero)
      change DirectSlot.append [first].length
          (DirectSlot.singleton first)
          (DirectSlot.singleton second) index =
        ([first] ++ [second])[index]?
      apply DirectSlot.append_eq_getElem?_append
      · exact DirectSlot.singleton_eq_getElem?_singleton _
      · exact DirectSlot.singleton_eq_getElem?_singleton _

/-- Total direct width of all paired cells for one selected length. -/
def pairedCellsForLengthWidthDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1)) : Nat :=
  DirectSlot.totalWidth
    (problem.dimensions.tapeWidth problem.tableauInputMode)
    (fun position =>
      problem.pairedCellConstraintWidthDirect length position)

/-- Direct lookup through all paired cells for one selected length. -/
def pairedCellsForLengthSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (index : Nat) :
    Option (LocalConstraint problem.FormulaWidth) :=
  DirectSlot.flatFinite
    (problem.dimensions.tapeWidth problem.tableauInputMode)
    (fun position =>
      problem.pairedCellConstraintSlotDirect hMode length position)
    (fun position =>
      problem.pairedCellConstraintWidthDirect length position) index

theorem pairedCellsForLengthWidthDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    problem.pairedCellsForLengthWidthDirect length =
      (problem.pairedCellsForLengthProgram hMode length).length := by
  unfold pairedCellsForLengthWidthDirect pairedCellsForLengthProgram
  apply DirectSlot.totalWidth_eq_flatMap_length
  intro position
  exact problem.pairedCellConstraintWidthDirect_eq hMode length position

theorem pairedCellsForLengthSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) (index : Nat) :
    problem.pairedCellsForLengthSlotDirect hMode length index =
      (problem.pairedCellsForLengthProgram hMode length)[index]? := by
  unfold pairedCellsForLengthSlotDirect pairedCellsForLengthProgram
  apply DirectSlot.flatFinite_eq_getElem?_flatMap
  · intro position next
    exact problem.pairedCellConstraintSlotDirect_eq hMode length position next
  · intro position
    exact problem.pairedCellConstraintWidthDirect_eq hMode length position

/-- Total direct width of every paired-cell block, excluding the leading
length one-hot constraint. -/
def pairedCellsWidthDirect {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  DirectSlot.totalWidth (problem.certificateLimit + 1)
    problem.pairedCellsForLengthWidthDirect

/-- Direct lookup through every paired-cell block. -/
def pairedCellsSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (index : Nat) :
    Option (LocalConstraint problem.FormulaWidth) :=
  DirectSlot.flatFinite (problem.certificateLimit + 1)
    (problem.pairedCellsForLengthSlotDirect hMode)
    problem.pairedCellsForLengthWidthDirect index

theorem pairedCellsWidthDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    problem.pairedCellsWidthDirect =
      ((finiteIndices (problem.certificateLimit + 1)).flatMap
        (problem.pairedCellsForLengthProgram hMode)).length := by
  unfold pairedCellsWidthDirect
  apply DirectSlot.totalWidth_eq_flatMap_length
  intro length
  exact problem.pairedCellsForLengthWidthDirect_eq hMode length

theorem pairedCellsSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (index : Nat) :
    problem.pairedCellsSlotDirect hMode index =
      ((finiteIndices (problem.certificateLimit + 1)).flatMap
        (problem.pairedCellsForLengthProgram hMode))[index]? := by
  unfold pairedCellsSlotDirect
  apply DirectSlot.flatFinite_eq_getElem?_flatMap
  · intro length next
    exact problem.pairedCellsForLengthSlotDirect_eq hMode length next
  · intro length
    exact problem.pairedCellsForLengthWidthDirect_eq hMode length

/-- Direct lookup in the complete paired initial-symbol program. -/
def pairedSymbolsSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (index : Nat) :
    Option (LocalConstraint problem.FormulaWidth) :=
  DirectSlot.append 1
    (DirectSlot.singleton
      (.exactlyOne (problem.pairedLengthVariables hMode)))
    (problem.pairedCellsSlotDirect hMode) index

theorem pairedSymbolsSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) (index : Nat) :
    problem.pairedSymbolsSlotDirect hMode index =
      (problem.pairedInitialSymbolsProgram hMode)[index]? := by
  unfold pairedSymbolsSlotDirect pairedInitialSymbolsProgram
  let first : LocalConstraint problem.FormulaWidth :=
    .exactlyOne (problem.pairedLengthVariables hMode)
  change DirectSlot.append [first].length
      (DirectSlot.singleton first) (problem.pairedCellsSlotDirect hMode) index =
    ([first] ++
      (finiteIndices (problem.certificateLimit + 1)).flatMap
        (problem.pairedCellsForLengthProgram hMode))[index]?
  apply DirectSlot.append_eq_getElem?_append
  · exact DirectSlot.singleton_eq_getElem?_singleton _
  · exact problem.pairedCellsSlotDirect_eq hMode

/-- Direct lookup in the mode-dependent initial-symbol program. -/
def initialSymbolsSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (LocalConstraint problem.FormulaWidth) :=
  if hMode : problem.tableauInputMode = .paired then
    problem.pairedSymbolsSlotDirect hMode index
  else
    problem.inputOnlySymbolsSlotDirect index

theorem initialSymbolsProgram_eq_inputOnly {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.verifier.program.inputMode = .inputOnly) :
    problem.initialSymbolsProgram =
      problem.inputOnlyInitialSymbolsProgram := by
  unfold initialSymbolsProgram
  split <;> rename_i hBranch
  · rfl
  · rw [hMode] at hBranch
    contradiction

theorem initialSymbolsProgram_eq_paired {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.verifier.program.inputMode = .paired) :
    problem.initialSymbolsProgram =
      problem.pairedInitialSymbolsProgram
        (problem.tableauInputMode_of_paired hMode) := by
  unfold initialSymbolsProgram
  split <;> rename_i hBranch
  · rw [hMode] at hBranch
    contradiction
  · congr

theorem initialSymbolsSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.initialSymbolsSlotDirect index =
      problem.initialSymbolsProgram[index]? := by
  cases hVerifierMode : problem.verifier.program.inputMode with
  | inputOnly =>
      have hTableau := problem.tableauInputMode_of_inputOnly hVerifierMode
      rw [problem.initialSymbolsProgram_eq_inputOnly hVerifierMode]
      simp only [initialSymbolsSlotDirect, hTableau, reduceCtorEq, dite_false]
      exact problem.inputOnlySymbolsSlotDirect_eq index
  | paired =>
      have hTableau := problem.tableauInputMode_of_paired hVerifierMode
      rw [problem.initialSymbolsProgram_eq_paired hVerifierMode]
      simp only [initialSymbolsSlotDirect, hTableau, dite_true]
      exact problem.pairedSymbolsSlotDirect_eq hTableau index

/-- Direct lookup in the two fixed initial constraints followed by the padded
mode-dependent initial-symbol region. -/
def initialConstraintSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.append 2
    (DirectSlot.append 1
      (DirectSlot.singleton (some (.require
        (problem.stateLiteral problem.initialTime problem.startState))))
      (DirectSlot.singleton (some (.require
        (problem.headLiteral problem.initialTime
          problem.initialHeadPosition)))))
    (DirectSlot.pad
      (1 + 2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode))
      problem.initialSymbolsSlotDirect) index

theorem initialConstraintSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.initialConstraintSlotDirect index =
      problem.scheduledInitialConstraints[index]? := by
  let stateEntry : Option (LocalConstraint problem.FormulaWidth) :=
    some (.require
      (problem.stateLiteral problem.initialTime problem.startState))
  let headEntry : Option (LocalConstraint problem.FormulaWidth) :=
    some (.require
      (problem.headLiteral problem.initialTime problem.initialHeadPosition))
  have hPrefix : ∀ next,
      DirectSlot.append 1 (DirectSlot.singleton stateEntry)
          (DirectSlot.singleton headEntry) next =
        [stateEntry, headEntry][next]? := by
    intro next
    change DirectSlot.append [stateEntry].length
        (DirectSlot.singleton stateEntry) (DirectSlot.singleton headEntry) next =
      ([stateEntry] ++ [headEntry])[next]?
    apply DirectSlot.append_eq_getElem?_append
    · exact DirectSlot.singleton_eq_getElem?_singleton _
    · exact DirectSlot.singleton_eq_getElem?_singleton _
  unfold initialConstraintSlotDirect scheduledInitialConstraints
  change DirectSlot.append [stateEntry, headEntry].length
      (DirectSlot.append 1 (DirectSlot.singleton stateEntry)
        (DirectSlot.singleton headEntry))
      (DirectSlot.pad
        (1 + 2 * ((problem.certificateLimit + 1) *
          problem.dimensions.tapeWidth problem.tableauInputMode))
        problem.initialSymbolsSlotDirect) index =
    ([stateEntry, headEntry] ++ FormulaSchedule.pad
      (1 + 2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode))
      problem.initialSymbolsProgram)[index]?
  apply DirectSlot.append_eq_getElem?_append
  · exact hPrefix
  · apply DirectSlot.pad_eq_getElem?_pad
    · exact problem.initialSymbolsSlotDirect_eq
    · exact problem.initialSymbolsProgram_length_le

/-- Direct three-way tape-symbol coordinate used by the control rectangle. -/
def controlTapeSymbol (coordinate : Fin 3) : TapeSymbol :=
  match coordinate.val with
  | 0 => .blank
  | 1 => .zero
  | _ => .one

theorem controlTapeSymbols_eq :
    (finiteIndices 3).map controlTapeSymbol = tapeSymbols := by
  rfl

/-- Direct lookup in the three local control constraints for one transition
coordinate. -/
def controlLocalSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  (problem.controlConstraints step state position symbol)[index]?.map some

theorem controlLocalSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) (index : Nat) :
    problem.controlLocalSlotDirect step state position symbol index =
      ((problem.controlConstraints step state position symbol).map some)[index]? := by
  unfold controlLocalSlotDirect
  rw [List.getElem?_map]

/-- Direct lookup in the fixed nine-slot symbol/control block for one state. -/
def controlSymbolBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle 3 3
    (fun symbol => problem.controlLocalSlotDirect step state position
      (controlTapeSymbol symbol)) index

theorem controlSymbolBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    problem.controlSymbolBlockSlotDirect step state position index =
      (tapeSymbols.flatMap fun symbol =>
        (problem.controlConstraints step state position symbol).map some)[index]? := by
  unfold controlSymbolBlockSlotDirect
  rw [← controlTapeSymbols_eq]
  rw [FormulaSchedule.flatMap_map_apply]
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · intro symbol next
    exact problem.controlLocalSlotDirect_eq step state position
      (controlTapeSymbol symbol) next
  · intro symbol
    simp [controlConstraints]

/-- Direct lookup over every state block for one time/position coordinate. -/
def controlStateBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle problem.dimensions.stateBound 9
    (fun state =>
      problem.controlSymbolBlockSlotDirect step state position) index

theorem controlStateBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    problem.controlStateBlockSlotDirect step position index =
      ((finiteIndices problem.dimensions.stateBound).flatMap fun state =>
        tapeSymbols.flatMap fun symbol =>
          (problem.controlConstraints step state position symbol).map some)[index]? := by
  unfold controlStateBlockSlotDirect
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.controlSymbolBlockSlotDirect_eq step
      (position := position)
  · intro state
    simp [tapeSymbols, controlConstraints]

/-- Direct lookup over every tape position for one transition step. -/
def controlPositionBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle
    (problem.dimensions.tapeWidth problem.tableauInputMode)
    (problem.dimensions.stateBound * 9)
    (problem.controlStateBlockSlotDirect step) index

theorem controlPositionBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel) (index : Nat) :
    problem.controlPositionBlockSlotDirect step index =
      ((finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
          fun position =>
            (finiteIndices problem.dimensions.stateBound).flatMap fun state =>
              tapeSymbols.flatMap fun symbol =>
                (problem.controlConstraints step state position symbol).map some)[index]? := by
  unfold controlPositionBlockSlotDirect
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.controlStateBlockSlotDirect_eq step
  · intro position
    rw [flatMap_length_eq_mul]
    · rw [finiteIndices_length]
    · intro state hState
      simp [tapeSymbols, controlConstraints]

/-- Direct lookup in the complete control-transition rectangle. -/
def controlConstraintSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle problem.uniformFuel
    (problem.dimensions.tapeWidth problem.tableauInputMode *
      (problem.dimensions.stateBound * 9))
    problem.controlPositionBlockSlotDirect index

theorem controlConstraintSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.controlConstraintSlotDirect index =
      problem.scheduledControlConstraints[index]? := by
  unfold controlConstraintSlotDirect scheduledControlConstraints
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.controlPositionBlockSlotDirect_eq
  · intro step
    rw [flatMap_length_eq_mul]
    · rw [finiteIndices_length]
    · intro position hPosition
      rw [flatMap_length_eq_mul]
      · rw [finiteIndices_length]
      · intro state hState
        simp [tapeSymbols, controlConstraints]

/-- Direct lookup in the three padded preservation opportunities for one
step/head/other coordinate. -/
def preservationLocalSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition otherPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) : Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.pad 3
    (fun next =>
      (problem.preservationConstraints step headPosition otherPosition)[next]?)
    index

theorem preservationLocalSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition otherPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    problem.preservationLocalSlotDirect step headPosition otherPosition index =
      (FormulaSchedule.pad 3
        (problem.preservationConstraints step headPosition
          otherPosition))[index]? := by
  unfold preservationLocalSlotDirect
  apply DirectSlot.pad_eq_getElem?_pad
  · intro next
    rfl
  · exact problem.preservationConstraints_length_le step headPosition
      otherPosition

/-- Direct lookup over every other-position block for one head position. -/
def preservationOtherBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) : Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle
    (problem.dimensions.tapeWidth problem.tableauInputMode) 3
    (problem.preservationLocalSlotDirect step headPosition) index

theorem preservationOtherBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (index : Nat) :
    problem.preservationOtherBlockSlotDirect step headPosition index =
      ((finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
          fun otherPosition => FormulaSchedule.pad 3
            (problem.preservationConstraints step headPosition
              otherPosition))[index]? := by
  unfold preservationOtherBlockSlotDirect
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.preservationLocalSlotDirect_eq step headPosition
  · intro otherPosition
    apply FormulaSchedule.pad_length
    exact problem.preservationConstraints_length_le step headPosition
      otherPosition

/-- Direct lookup over every head-position block for one transition step. -/
def preservationHeadBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle
    (problem.dimensions.tapeWidth problem.tableauInputMode)
    (problem.dimensions.tapeWidth problem.tableauInputMode * 3)
    (problem.preservationOtherBlockSlotDirect step) index

theorem preservationHeadBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel) (index : Nat) :
    problem.preservationHeadBlockSlotDirect step index =
      ((finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
          fun headPosition =>
            (finiteIndices
              (problem.dimensions.tapeWidth problem.tableauInputMode)).flatMap
                fun otherPosition => FormulaSchedule.pad 3
                  (problem.preservationConstraints step headPosition
                    otherPosition))[index]? := by
  unfold preservationHeadBlockSlotDirect
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.preservationOtherBlockSlotDirect_eq step
  · intro headPosition
    rw [flatMap_length_eq_mul]
    · rw [finiteIndices_length]
    · intro otherPosition hOther
      apply FormulaSchedule.pad_length
      exact problem.preservationConstraints_length_le step headPosition
        otherPosition

/-- Direct lookup in the complete preservation rectangle. -/
def preservationConstraintSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.rectangle problem.uniformFuel
    (problem.dimensions.tapeWidth problem.tableauInputMode *
      (problem.dimensions.tapeWidth problem.tableauInputMode * 3))
    problem.preservationHeadBlockSlotDirect index

theorem preservationConstraintSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.preservationConstraintSlotDirect index =
      problem.scheduledPreservationConstraints[index]? := by
  unfold preservationConstraintSlotDirect scheduledPreservationConstraints
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.preservationHeadBlockSlotDirect_eq
  · intro step
    rw [flatMap_length_eq_mul]
    · rw [finiteIndices_length]
    · intro headPosition hHead
      rw [flatMap_length_eq_mul]
      · rw [finiteIndices_length]
      · intro otherPosition hOther
        apply FormulaSchedule.pad_length
        exact problem.preservationConstraints_length_le step headPosition
          otherPosition

/-- Direct lookup across the literal concatenation of shape, initial,
control, preservation, and accepting regions. -/
def formulaConstraintSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (LocalConstraint problem.FormulaWidth)) :=
  DirectSlot.append
    (problem.dimensions.timeCount *
      (problem.dimensions.tapeWidth problem.tableauInputMode + 2))
    problem.shapeConstraintSlotDirect
    (DirectSlot.append
      (3 + 2 * ((problem.certificateLimit + 1) *
        problem.dimensions.tapeWidth problem.tableauInputMode))
      problem.initialConstraintSlotDirect
      (DirectSlot.append
        (9 * (problem.uniformFuel *
          problem.dimensions.tapeWidth problem.tableauInputMode *
          problem.dimensions.stateBound))
        problem.controlConstraintSlotDirect
        (DirectSlot.append
          (3 * (problem.uniformFuel *
            problem.dimensions.tapeWidth problem.tableauInputMode *
            problem.dimensions.tapeWidth problem.tableauInputMode))
          problem.preservationConstraintSlotDirect
          (DirectSlot.singleton (some (.require
            (problem.stateLiteral problem.finalTime
              problem.acceptingState))))))) index

theorem formulaConstraintSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaConstraintSlotDirect index =
      problem.formulaConstraintSchedule[index]? := by
  unfold formulaConstraintSlotDirect formulaConstraintSchedule
  simp only [List.append_assoc]
  rw [← problem.scheduledShapeConstraints_length]
  apply DirectSlot.append_eq_getElem?_append
  · exact problem.shapeConstraintSlotDirect_eq
  · rw [← problem.scheduledInitialConstraints_length]
    apply DirectSlot.append_eq_getElem?_append
    · exact problem.initialConstraintSlotDirect_eq
    · rw [← problem.scheduledControlConstraints_length]
      apply DirectSlot.append_eq_getElem?_append
      · exact problem.controlConstraintSlotDirect_eq
      · rw [← problem.scheduledPreservationConstraints_length]
        apply DirectSlot.append_eq_getElem?_append
        · exact problem.preservationConstraintSlotDirect_eq
        · exact DirectSlot.singleton_eq_getElem?_singleton _

/-! ### Direct clause coordinates -/

/-- Direct lookup in the fixed clause rectangle belonging to one constraint
coordinate.  The constraint itself is obtained from the direct decoder. -/
def constraintClauseBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaConstraintSlotCount)
    (index : Nat) : Option (Option (BoundedClause problem.FormulaWidth)) :=
  match problem.formulaConstraintSlotDirect coordinate.val with
  | none => none
  | some none =>
      DirectSlot.pad problem.formulaClauseSlotsPerConstraint
        (fun _ => (none : Option (BoundedClause problem.FormulaWidth))) index
  | some (some constraint) =>
      DirectSlot.pad problem.formulaClauseSlotsPerConstraint
        (LocalConstraint.clauseSlotDirect constraint) index

theorem constraintClauseBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaConstraintSlotCount)
    (index : Nat) :
    problem.constraintClauseBlockSlotDirect coordinate index =
      (problem.scheduledConstraintClauses
        (problem.formulaConstraintSchedule.get
          (Fin.cast problem.formulaConstraintSchedule_length.symm
            coordinate)))[index]? := by
  let scheduleCoordinate : Fin problem.formulaConstraintSchedule.length :=
    Fin.cast problem.formulaConstraintSchedule_length.symm coordinate
  let entry := problem.formulaConstraintSchedule.get scheduleCoordinate
  have hEntry : entry ∈ problem.formulaConstraintSchedule :=
    List.get_mem _ scheduleCoordinate
  have hIndex : coordinate.val <
      problem.formulaConstraintSchedule.length := by
    rw [problem.formulaConstraintSchedule_length]
    exact coordinate.isLt
  have hCoordinate : (⟨coordinate.val, hIndex⟩ :
      Fin problem.formulaConstraintSchedule.length) = scheduleCoordinate :=
    Fin.ext rfl
  have hDirect := problem.formulaConstraintSlotDirect_eq coordinate.val
  rw [List.getElem?_eq_getElem hIndex] at hDirect
  have hValue : problem.formulaConstraintSchedule[coordinate.val] = entry := by
    change problem.formulaConstraintSchedule.get ⟨coordinate.val, hIndex⟩ =
      problem.formulaConstraintSchedule.get scheduleCoordinate
    rw [hCoordinate]
  rw [hValue] at hDirect
  change problem.constraintClauseBlockSlotDirect coordinate index =
    (problem.scheduledConstraintClauses entry)[index]?
  unfold constraintClauseBlockSlotDirect
  rw [hDirect]
  generalize hSelected : entry = selected at hEntry ⊢
  cases selected with
  | none =>
      simpa [scheduledConstraintClauses, FormulaSchedule.pad] using
        (DirectSlot.pad_eq_getElem?_pad
          problem.formulaClauseSlotsPerConstraint
          ([] : List (BoundedClause problem.FormulaWidth))
          (fun _ => (none : Option (BoundedClause problem.FormulaWidth)))
          (by intro next; rfl) (Nat.zero_le _) index)
  | some constraint =>
      unfold scheduledConstraintClauses
      apply DirectSlot.pad_eq_getElem?_pad
      · exact LocalConstraint.clauseSlotDirect_eq_emit_getElem? constraint
      · rw [LocalConstraint.emit_length]
        apply LocalConstraint.clauseCount_le
        exact problem.constraint_sizeBounded_formulaVariableSlotBound
          constraint hEntry

theorem formulaConstraintCoordinateEnumeration {language : Language}
    (problem : VerifierTableauProblem language) :
    (finiteIndices problem.formulaConstraintSlotCount).map
        (fun coordinate => problem.formulaConstraintSchedule.get
          (Fin.cast problem.formulaConstraintSchedule_length.symm
            coordinate)) =
      problem.formulaConstraintSchedule := by
  rw [DirectSlot.finiteIndices_eq_ofFn, List.map_ofFn]
  apply List.ext_getElem
  · simp [problem.formulaConstraintSchedule_length]
  · intro index hLeft hRight
    rw [List.getElem_ofFn]
    apply congrArg problem.formulaConstraintSchedule.get
    apply Fin.ext
    rfl

/-- Direct lookup in the complete fixed-width clause rectangle. -/
def formulaClauseSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option (BoundedClause problem.FormulaWidth)) :=
  DirectSlot.rectangle problem.formulaConstraintSlotCount
    problem.formulaClauseSlotsPerConstraint
    problem.constraintClauseBlockSlotDirect index

theorem formulaClauseSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaClauseSlotDirect index =
      problem.formulaClauseSchedule[index]? := by
  unfold formulaClauseSlotDirect formulaClauseSchedule
  rw [← problem.formulaConstraintCoordinateEnumeration]
  rw [FormulaSchedule.flatMap_map_apply]
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.constraintClauseBlockSlotDirect_eq
  · intro coordinate
    apply problem.scheduledConstraintClauses_length
    exact List.get_mem _ _

/-! ### Direct token coordinates -/

/-- Direct lookup in the padded unary formula-width header. -/
def formulaHeaderTokenSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option CNFToken) :=
  DirectSlot.pad (problem.formulaVariableSlotBound + 1)
    (DirectToken.unarySlot problem.FormulaWidth) index

theorem formulaHeaderTokenSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaHeaderTokenSlotDirect index =
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth))[index]? := by
  unfold formulaHeaderTokenSlotDirect
  apply DirectSlot.pad_eq_getElem?_pad
  · exact DirectToken.unarySlot_eq_encodeUnaryTokens_getElem?
      problem.FormulaWidth
  · rw [encodeUnaryTokens_length]
    unfold formulaVariableSlotBound
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1

/-- Direct lookup in the fixed token rectangle belonging to one clause
coordinate. -/
def clauseTokenBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaClauseSlotCount)
    (index : Nat) : Option (Option CNFToken) :=
  match problem.formulaClauseSlotDirect coordinate.val with
  | none => none
  | some none =>
      DirectSlot.pad problem.formulaTokensPerClause
        (fun _ => (none : Option CNFToken)) index
  | some (some clause) =>
      DirectSlot.pad problem.formulaTokensPerClause
        (DirectToken.clauseSlot clause) index

theorem clauseTokenBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaClauseSlotCount)
    (index : Nat) :
    problem.clauseTokenBlockSlotDirect coordinate index =
      (problem.scheduledClauseTokens
        (problem.formulaClauseSchedule.get
          (Fin.cast problem.formulaClauseSchedule_length.symm
            coordinate)))[index]? := by
  let scheduleCoordinate : Fin problem.formulaClauseSchedule.length :=
    Fin.cast problem.formulaClauseSchedule_length.symm coordinate
  let entry := problem.formulaClauseSchedule.get scheduleCoordinate
  have hEntry : entry ∈ problem.formulaClauseSchedule :=
    List.get_mem _ scheduleCoordinate
  have hIndex : coordinate.val < problem.formulaClauseSchedule.length := by
    rw [problem.formulaClauseSchedule_length]
    exact coordinate.isLt
  have hCoordinate : (⟨coordinate.val, hIndex⟩ :
      Fin problem.formulaClauseSchedule.length) = scheduleCoordinate :=
    Fin.ext rfl
  have hDirect := problem.formulaClauseSlotDirect_eq coordinate.val
  rw [List.getElem?_eq_getElem hIndex] at hDirect
  have hValue : problem.formulaClauseSchedule[coordinate.val] = entry := by
    change problem.formulaClauseSchedule.get ⟨coordinate.val, hIndex⟩ =
      problem.formulaClauseSchedule.get scheduleCoordinate
    rw [hCoordinate]
  rw [hValue] at hDirect
  change problem.clauseTokenBlockSlotDirect coordinate index =
    (problem.scheduledClauseTokens entry)[index]?
  unfold clauseTokenBlockSlotDirect
  rw [hDirect]
  generalize hSelected : entry = selected at hEntry ⊢
  cases selected with
  | none =>
      simpa [scheduledClauseTokens, FormulaSchedule.pad] using
        (DirectSlot.pad_eq_getElem?_pad problem.formulaTokensPerClause
          ([] : List CNFToken) (fun _ => (none : Option CNFToken))
          (by intro next; rfl) (Nat.zero_le _) index)
  | some clause =>
      unfold scheduledClauseTokens
      apply DirectSlot.pad_eq_getElem?_pad
      · exact DirectToken.clauseSlot_eq_encodeClauseTokens_getElem? clause
      · rw [encodeClauseTokens_length]
        apply clauseTokenCost_le (BoundedClause.emit clause)
        · intro literal hLiteral
          exact BoundedClause.emitted_variable_lt clause literal hLiteral
        · unfold formulaVariableSlotBound
          exact problem.formulaWidth_le_formulaVariableCountPolynomial
        · have hBoundedClause : clause ∈
              FormulaSchedule.emit problem.formulaClauseSchedule :=
            FormulaSchedule.mem_emit_of_mem_some hEntry
          have hFormulaClause : BoundedClause.emit clause ∈
              problem.formula.clauses := by
            rw [← problem.formulaClauseSchedule_emit_eq_formulaClauses]
            exact List.mem_map_of_mem hBoundedClause
          have hLength := problem.formula_clause_length_le
            (BoundedClause.emit clause) hFormulaClause
          simpa [formulaVariableSlotBound] using hLength

theorem formulaClauseCoordinateEnumeration {language : Language}
    (problem : VerifierTableauProblem language) :
    (finiteIndices problem.formulaClauseSlotCount).map
        (fun coordinate => problem.formulaClauseSchedule.get
          (Fin.cast problem.formulaClauseSchedule_length.symm coordinate)) =
      problem.formulaClauseSchedule := by
  rw [DirectSlot.finiteIndices_eq_ofFn, List.map_ofFn]
  apply List.ext_getElem
  · simp [problem.formulaClauseSchedule_length]
  · intro index hLeft hRight
    rw [List.getElem_ofFn]
    apply congrArg problem.formulaClauseSchedule.get
    apply Fin.ext
    rfl

/-- Direct lookup in every fixed-width clause-token block. -/
def formulaClauseTokenSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option CNFToken) :=
  DirectSlot.rectangle problem.formulaClauseSlotCount
    problem.formulaTokensPerClause
    problem.clauseTokenBlockSlotDirect index

theorem formulaClauseTokenSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaClauseTokenSlotDirect index =
      (problem.formulaClauseSchedule.flatMap
        problem.scheduledClauseTokens)[index]? := by
  unfold formulaClauseTokenSlotDirect
  rw [← problem.formulaClauseCoordinateEnumeration]
  rw [FormulaSchedule.flatMap_map_apply]
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.clauseTokenBlockSlotDirect_eq
  · intro coordinate
    apply problem.scheduledClauseTokens_length
    exact List.get_mem _ _

/-- Direct lookup in the header, clause-token rectangle, and final finish
token. -/
def formulaTokenSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option CNFToken) :=
  DirectSlot.append (problem.formulaVariableSlotBound + 1)
    problem.formulaHeaderTokenSlotDirect
    (DirectSlot.append
      (problem.formulaClauseSlotCount * problem.formulaTokensPerClause)
      problem.formulaClauseTokenSlotDirect
      (DirectSlot.singleton (some CNFToken.finish))) index

theorem formulaTokenSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaTokenSlotDirect index =
      problem.formulaTokenSchedule[index]? := by
  unfold formulaTokenSlotDirect formulaTokenSchedule
  simp only [List.append_assoc]
  have hHeader : (FormulaSchedule.pad
      (problem.formulaVariableSlotBound + 1)
      (encodeUnaryTokens problem.FormulaWidth)).length =
      problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    unfold formulaVariableSlotBound
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hRight : ∀ next,
      DirectSlot.append
          (problem.formulaClauseSlotCount * problem.formulaTokensPerClause)
          problem.formulaClauseTokenSlotDirect
          (DirectSlot.singleton (some CNFToken.finish)) next =
        (problem.formulaClauseSchedule.flatMap
          problem.scheduledClauseTokens ++ [some CNFToken.finish])[next]? := by
    intro next
    simpa [problem.formulaClauseTokensSchedule_length] using
      (DirectSlot.append_eq_getElem?_append
        (problem.formulaClauseSchedule.flatMap
          problem.scheduledClauseTokens)
        [some CNFToken.finish]
        problem.formulaClauseTokenSlotDirect
        (DirectSlot.singleton (some CNFToken.finish))
        problem.formulaClauseTokenSlotDirect_eq
        (DirectSlot.singleton_eq_getElem?_singleton _) next)
  simpa [hHeader] using
    (DirectSlot.append_eq_getElem?_append
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth))
      (problem.formulaClauseSchedule.flatMap
        problem.scheduledClauseTokens ++ [some CNFToken.finish])
      problem.formulaHeaderTokenSlotDirect
      (DirectSlot.append
        (problem.formulaClauseSlotCount * problem.formulaTokensPerClause)
        problem.formulaClauseTokenSlotDirect
        (DirectSlot.singleton (some CNFToken.finish)))
      problem.formulaHeaderTokenSlotDirect_eq hRight index)

/-! ### Direct raw-bit coordinates -/

/-- Direct lookup in the two-bit code of one token. -/
def tokenBitSlotDirect : CNFToken → Nat → Option Bool
  | .f, 0 => some false
  | .f, 1 => some false
  | .f, _ + 2 => none
  | .t, 0 => some true
  | .t, 1 => some true
  | .t, _ + 2 => none
  | .sep, 0 => some false
  | .sep, 1 => some true
  | .sep, _ + 2 => none
  | .finish, 0 => some true
  | .finish, 1 => some false
  | .finish, _ + 2 => none

theorem tokenBitSlotDirect_eq (token : CNFToken) (index : Nat) :
    tokenBitSlotDirect token index = token.bits[index]? := by
  cases token <;> cases index with
  | zero => rfl
  | succ index => cases index <;> rfl

/-- Direct token schedule width, computed from the rectangular bounds. -/
def formulaTokenSlotCountDirect {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (problem.formulaVariableSlotBound + 1) +
    problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1

theorem formulaTokenSlotCountDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotCountDirect =
      problem.formulaTokenSchedule.length := by
  unfold formulaTokenSlotCountDirect
  rw [problem.formulaTokenSchedule_length]

/-! ### Fuelled direct token cursor -/

/-- Token-level cursor used by the literal formula builder.  The existing
raw-bit cursor remains the final encoding specification; this cursor matches
the builder workspace, where one emitted token occupies one work cell. -/
structure FormulaTokenCursor where
  nextSlot : Nat
deriving DecidableEq, Repr

namespace FormulaTokenCursor

def initial : FormulaTokenCursor := ⟨0⟩

def done {language : Language} (problem : VerifierTableauProblem language)
    (cursor : FormulaTokenCursor) : Prop :=
  problem.formulaTokenSlotCountDirect ≤ cursor.nextSlot

/-- Decode one padded token opportunity and advance.  `none` means the
cursor is outside the complete token schedule, while `some none` is an
in-range padding opportunity. -/
def step {language : Language} (problem : VerifierTableauProblem language)
    (cursor : FormulaTokenCursor) :
    Option (Option CNFToken × FormulaTokenCursor) :=
  match problem.formulaTokenSlotDirect cursor.nextSlot with
  | none => none
  | some entry => some (entry, ⟨cursor.nextSlot + 1⟩)

theorem step_of_lt {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : FormulaTokenCursor)
    (hCursor : cursor.nextSlot < problem.formulaTokenSlotCountDirect) :
    step problem cursor =
      some (problem.formulaTokenSchedule.get
          ⟨cursor.nextSlot, by
            rw [← problem.formulaTokenSlotCountDirect_eq]
            exact hCursor⟩,
        ⟨cursor.nextSlot + 1⟩) := by
  unfold step
  rw [problem.formulaTokenSlotDirect_eq]
  have hSchedule : cursor.nextSlot < problem.formulaTokenSchedule.length := by
    rw [← problem.formulaTokenSlotCountDirect_eq]
    exact hCursor
  rw [List.getElem?_eq_getElem hSchedule]
  simp only
  congr

theorem step_of_done {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : FormulaTokenCursor) (hDone : done problem cursor) :
    step problem cursor = none := by
  unfold step done at *
  rw [problem.formulaTokenSlotDirect_eq]
  rw [List.getElem?_eq_none]
  rw [← problem.formulaTokenSlotCountDirect_eq]
  exact hDone

theorem step_at_end {language : Language}
    (problem : VerifierTableauProblem language) :
    step problem ⟨problem.formulaTokenSlotCountDirect⟩ = none := by
  apply step_of_done
  exact Nat.le_refl _

end FormulaTokenCursor

/-- Direct lookup in one token's two raw-bit opportunities. -/
def tokenBitBlockSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaTokenSlotCountDirect)
    (index : Nat) : Option (Option Bool) :=
  match problem.formulaTokenSlotDirect coordinate.val with
  | none => none
  | some none =>
      DirectSlot.pad 2 (fun _ => (none : Option Bool)) index
  | some (some token) => (tokenBitSlotDirect token index).map some

theorem tokenBitBlockSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate : Fin problem.formulaTokenSlotCountDirect)
    (index : Nat) :
    problem.tokenBitBlockSlotDirect coordinate index =
      (scheduledTokenBits
        (problem.formulaTokenSchedule.get
          (Fin.cast problem.formulaTokenSlotCountDirect_eq coordinate)))[index]? := by
  let scheduleCoordinate : Fin problem.formulaTokenSchedule.length :=
    Fin.cast problem.formulaTokenSlotCountDirect_eq coordinate
  let entry := problem.formulaTokenSchedule.get scheduleCoordinate
  have hIndex : coordinate.val < problem.formulaTokenSchedule.length := by
    rw [← problem.formulaTokenSlotCountDirect_eq]
    exact coordinate.isLt
  have hCoordinate : (⟨coordinate.val, hIndex⟩ :
      Fin problem.formulaTokenSchedule.length) = scheduleCoordinate :=
    Fin.ext rfl
  have hDirect := problem.formulaTokenSlotDirect_eq coordinate.val
  rw [List.getElem?_eq_getElem hIndex] at hDirect
  have hValue : problem.formulaTokenSchedule[coordinate.val] = entry := by
    change problem.formulaTokenSchedule.get ⟨coordinate.val, hIndex⟩ =
      problem.formulaTokenSchedule.get scheduleCoordinate
    rw [hCoordinate]
  rw [hValue] at hDirect
  change problem.tokenBitBlockSlotDirect coordinate index =
    (scheduledTokenBits entry)[index]?
  unfold tokenBitBlockSlotDirect
  rw [hDirect]
  generalize hSelected : entry = selected
  cases selected with
  | none =>
      simpa [scheduledTokenBits, FormulaSchedule.pad] using
        (DirectSlot.pad_eq_getElem?_pad 2 ([] : List Bool)
          (fun _ => (none : Option Bool)) (by intro next; rfl)
          (Nat.zero_le _) index)
  | some token =>
      unfold scheduledTokenBits
      rw [List.getElem?_map]
      change (tokenBitSlotDirect token index).map some =
        token.bits[index]?.map some
      rw [tokenBitSlotDirect_eq]

theorem formulaTokenCoordinateEnumeration {language : Language}
    (problem : VerifierTableauProblem language) :
    (finiteIndices problem.formulaTokenSlotCountDirect).map
        (fun coordinate => problem.formulaTokenSchedule.get
          (Fin.cast problem.formulaTokenSlotCountDirect_eq coordinate)) =
      problem.formulaTokenSchedule := by
  rw [DirectSlot.finiteIndices_eq_ofFn, List.map_ofFn]
  apply List.ext_getElem
  · simp [problem.formulaTokenSlotCountDirect_eq]
  · intro index hLeft hRight
    rw [List.getElem_ofFn]
    apply congrArg problem.formulaTokenSchedule.get
    apply Fin.ext
    rfl

/-- Direct lookup in all two-bit token blocks. -/
def formulaTokenBitSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option Bool) :=
  DirectSlot.rectangle problem.formulaTokenSlotCountDirect 2
    problem.tokenBitBlockSlotDirect index

theorem formulaTokenBitSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaTokenBitSlotDirect index =
      (problem.formulaTokenSchedule.flatMap scheduledTokenBits)[index]? := by
  unfold formulaTokenBitSlotDirect
  rw [← problem.formulaTokenCoordinateEnumeration]
  rw [FormulaSchedule.flatMap_map_apply]
  apply DirectSlot.rectangle_eq_getElem?_flatMap
  · exact problem.tokenBitBlockSlotDirect_eq
  · intro coordinate
    exact scheduledTokenBits_length _

/-- Direct lookup in the complete raw-bit schedule, including the populated
final odd-length zero pad. -/
def formulaBitSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option Bool) :=
  DirectSlot.append (problem.formulaTokenSlotCountDirect * 2)
    problem.formulaTokenBitSlotDirect
    (DirectSlot.singleton (some false)) index

theorem formulaTokenBitSchedule_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (problem.formulaTokenSchedule.flatMap scheduledTokenBits).length =
      problem.formulaTokenSlotCountDirect * 2 := by
  rw [flatMap_length_eq_mul]
  · rw [← problem.formulaTokenSlotCountDirect_eq]
  · intro entry hEntry
    exact scheduledTokenBits_length entry

theorem formulaBitSlotDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    problem.formulaBitSlotDirect index =
      problem.formulaBitSchedule[index]? := by
  unfold formulaBitSlotDirect formulaBitSchedule
  simpa [problem.formulaTokenBitSchedule_length] using
    (DirectSlot.append_eq_getElem?_append
      (problem.formulaTokenSchedule.flatMap scheduledTokenBits)
      [some false] problem.formulaTokenBitSlotDirect
      (DirectSlot.singleton (some false))
      problem.formulaTokenBitSlotDirect_eq
      (DirectSlot.singleton_eq_getElem?_singleton _) index)

/-! ### Fuelled direct formula cursor -/

/-- Total number of direct raw-bit opportunities. -/
def formulaBitSlotCountDirect {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaTokenSlotCountDirect * 2 + 1

theorem formulaBitSlotCountDirect_eq {language : Language}
    (problem : VerifierTableauProblem language) :
  problem.formulaBitSlotCountDirect = problem.formulaBitSchedule.length := by
  unfold formulaBitSlotCountDirect formulaBitSchedule
  rw [List.length_append, problem.formulaTokenBitSchedule_length]
  rfl

theorem formulaBitSlotCountDirect_eq_polynomial {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaBitSlotCountDirect =
      (encodedFormulaSizePolynomial problem.verifier).eval
        (BitString.size problem.input) := by
  rw [problem.formulaBitSlotCountDirect_eq,
    problem.formulaBitSchedule_length]

/-- Cursor state contains only the next direct coordinate. -/
structure FormulaBitCursor where
  nextSlot : Nat
deriving DecidableEq, Repr

namespace FormulaBitCursor

def initial : FormulaBitCursor := ⟨0⟩

def done {language : Language} (problem : VerifierTableauProblem language)
    (cursor : FormulaBitCursor) : Prop :=
  problem.formulaBitSlotCountDirect ≤ cursor.nextSlot

/-- Decode one coordinate and advance.  `none` means that the cursor is
already outside the complete direct schedule; `some none` is a valid padded
coordinate. -/
def step {language : Language} (problem : VerifierTableauProblem language)
    (cursor : FormulaBitCursor) :
    Option (Option Bool × FormulaBitCursor) :=
  match problem.formulaBitSlotDirect cursor.nextSlot with
  | none => none
  | some entry => some (entry, ⟨cursor.nextSlot + 1⟩)

/-- Consume at most `fuel` direct coordinates, stopping exactly when lookup
leaves the schedule. -/
def run {language : Language} (problem : VerifierTableauProblem language) :
    Nat → FormulaBitCursor → List (Option Bool) × FormulaBitCursor
  | 0, cursor => ([], cursor)
  | fuel + 1, cursor =>
      match step problem cursor with
      | none => ([], cursor)
      | some (entry, next) =>
          let tail := run problem fuel next
          (entry :: tail.1, tail.2)

theorem step_of_lt {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : FormulaBitCursor)
    (hCursor : cursor.nextSlot < problem.formulaBitSlotCountDirect) :
    step problem cursor =
      some (problem.formulaBitSchedule.get
          ⟨cursor.nextSlot, by
            rw [← problem.formulaBitSlotCountDirect_eq]
            exact hCursor⟩,
        ⟨cursor.nextSlot + 1⟩) := by
  unfold step
  rw [problem.formulaBitSlotDirect_eq]
  have hSchedule : cursor.nextSlot < problem.formulaBitSchedule.length := by
    rw [← problem.formulaBitSlotCountDirect_eq]
    exact hCursor
  rw [List.getElem?_eq_getElem hSchedule]
  simp only
  congr

theorem step_of_done {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : FormulaBitCursor) (hDone : done problem cursor) :
    step problem cursor = none := by
  unfold step done at *
  rw [problem.formulaBitSlotDirect_eq]
  rw [List.getElem?_eq_none]
  rw [← problem.formulaBitSlotCountDirect_eq]
  exact hDone

theorem run_of_done {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : FormulaBitCursor) (hDone : done problem cursor)
    (fuel : Nat) : run problem fuel cursor = ([], cursor) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [run, step_of_done problem cursor hDone]

theorem run_prefix {language : Language}
    (problem : VerifierTableauProblem language)
    (start fuel : Nat)
    (hBound : start + fuel ≤ problem.formulaBitSlotCountDirect) :
    run problem fuel ⟨start⟩ =
      ((problem.formulaBitSchedule.drop start).take fuel,
        ⟨start + fuel⟩) := by
  induction fuel generalizing start with
  | zero => simp [run]
  | succ fuel ih =>
      have hStart : start < problem.formulaBitSlotCountDirect := by omega
      have hTail : start + 1 + fuel ≤
          problem.formulaBitSlotCountDirect := by omega
      rw [run, step_of_lt problem ⟨start⟩ hStart]
      simp only
      rw [ih (start := start + 1) hTail]
      have hSchedule : start < problem.formulaBitSchedule.length := by
        rw [← problem.formulaBitSlotCountDirect_eq]
        exact hStart
      rw [List.drop_eq_getElem_cons hSchedule]
      simp only [List.take_succ_cons]
      congr 2 <;> omega

theorem run_of_step_none {language : Language}
    (problem : VerifierTableauProblem language)
    (cursor : FormulaBitCursor) (hStep : step problem cursor = none)
    (fuel : Nat) : run problem fuel cursor = ([], cursor) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [run, hStep]

theorem run_to_end {language : Language}
    (problem : VerifierTableauProblem language)
    (start fuel : Nat)
    (hStart : start ≤ problem.formulaBitSlotCountDirect)
    (hFuel : problem.formulaBitSlotCountDirect - start ≤ fuel) :
    run problem fuel ⟨start⟩ =
      (problem.formulaBitSchedule.drop start,
        ⟨problem.formulaBitSlotCountDirect⟩) := by
  induction fuel generalizing start with
  | zero =>
      have hEqual : start = problem.formulaBitSlotCountDirect := by omega
      subst start
      rw [run]
      rw [problem.formulaBitSlotCountDirect_eq]
      simp
  | succ fuel ih =>
      by_cases hEnd : problem.formulaBitSlotCountDirect ≤ start
      · have hEqual : start = problem.formulaBitSlotCountDirect := by omega
        subst start
        rw [run, step_of_done problem
          ⟨problem.formulaBitSlotCountDirect⟩ (Nat.le_refl _)]
        rw [problem.formulaBitSlotCountDirect_eq]
        simp
      · have hIndex : start < problem.formulaBitSlotCountDirect := by omega
        have hNext : start + 1 ≤ problem.formulaBitSlotCountDirect := by omega
        have hNextFuel : problem.formulaBitSlotCountDirect - (start + 1) ≤
            fuel := by omega
        rw [run, step_of_lt problem ⟨start⟩ hIndex]
        simp only
        rw [ih (start := start + 1) hNext hNextFuel]
        have hSchedule : start < problem.formulaBitSchedule.length := by
          rw [← problem.formulaBitSlotCountDirect_eq]
          exact hIndex
        rw [List.drop_eq_getElem_cons hSchedule]
        simp only
        congr

theorem run_full {language : Language}
    (problem : VerifierTableauProblem language) :
    run problem problem.formulaBitSlotCountDirect initial =
      (problem.formulaBitSchedule,
        ⟨problem.formulaBitSlotCountDirect⟩) := by
  have hPrefix := run_prefix problem 0 problem.formulaBitSlotCountDirect
    (by omega)
  simpa [initial, problem.formulaBitSlotCountDirect_eq] using hPrefix

theorem step_at_end {language : Language}
    (problem : VerifierTableauProblem language) :
    step problem ⟨problem.formulaBitSlotCountDirect⟩ = none := by
  apply step_of_done
  exact Nat.le_refl _

theorem run_one_step_short {language : Language}
    (problem : VerifierTableauProblem language) :
    run problem (problem.formulaBitSlotCountDirect - 1) initial =
      (problem.formulaBitSchedule.take
        (problem.formulaBitSlotCountDirect - 1),
        ⟨problem.formulaBitSlotCountDirect - 1⟩) := by
  have hPrefix := run_prefix problem 0
    (problem.formulaBitSlotCountDirect - 1) (by omega)
  simpa [initial] using hPrefix

theorem step_after_one_step_short {language : Language}
    (problem : VerifierTableauProblem language) :
    step problem ⟨problem.formulaBitSlotCountDirect - 1⟩ =
      some
        (problem.formulaBitSchedule.get
          ⟨problem.formulaBitSlotCountDirect - 1, by
            rw [← problem.formulaBitSlotCountDirect_eq]
            unfold formulaBitSlotCountDirect
            omega⟩,
          ⟨problem.formulaBitSlotCountDirect⟩) := by
  have hPositive : 0 < problem.formulaBitSlotCountDirect := by
    unfold formulaBitSlotCountDirect
    omega
  have hIndex : problem.formulaBitSlotCountDirect - 1 <
      problem.formulaBitSlotCountDirect := by omega
  have hStep := step_of_lt problem
    ⟨problem.formulaBitSlotCountDirect - 1⟩ hIndex
  have hNext : problem.formulaBitSlotCountDirect - 1 + 1 =
      problem.formulaBitSlotCountDirect := by omega
  simpa [hNext] using hStep

theorem run_excess {language : Language}
    (problem : VerifierTableauProblem language) (extra : Nat) :
    run problem (problem.formulaBitSlotCountDirect + extra) initial =
      (problem.formulaBitSchedule,
        ⟨problem.formulaBitSlotCountDirect⟩) := by
  have hEnd := run_to_end problem 0
    (problem.formulaBitSlotCountDirect + extra) (by omega) (by omega)
  simpa [initial] using hEnd

/-- The populated output of the exact full cursor run is the canonical raw
formula encoding. -/
theorem run_full_emit_eq_encodedFormula {language : Language}
    (problem : VerifierTableauProblem language) :
    FormulaSchedule.emit
        (run problem problem.formulaBitSlotCountDirect initial).1 =
      problem.encodedFormula := by
  rw [run_full]
  exact problem.formulaBitSchedule_emit_eq_encodedFormula

end FormulaBitCursor

end VerifierTableauProblem

end CookLevin

end PNP.Concrete
