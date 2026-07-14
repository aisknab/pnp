/-
Copyright (c) 2026 PNP Labs.

Constructive semantic decoding for the finite Cook--Levin tableau formula.

This file connects the width-indexed Boolean namespaces to an intrinsic
finite row semantics.  It proves the coordinate maps injective, extracts the
unique symbol, head, and state selected by each one-hot family, and fixes the
literal deterministic successor represented by the transition clauses.

The subsequent raw-tape bridge is kept separate: no theorem in this file
claims CNF-SAT NP-hardness or a polynomial reduction.
-/

import PNP.Concrete.CookLevinTableauCNF

namespace PNP.Concrete

namespace CookLevin

open VariableLayout

/-! ### Injectivity of the row-major variable coordinates -/

theorem flattenTwo_injective {outer₁ inner₁ outer₂ inner₂ innerCount : Nat}
    (hInner₁ : inner₁ < innerCount)
    (hInner₂ : inner₂ < innerCount)
    (hEqual : flattenTwo outer₁ inner₁ innerCount =
      flattenTwo outer₂ inner₂ innerCount) :
    outer₁ = outer₂ ∧ inner₁ = inner₂ := by
  unfold flattenTwo at hEqual
  by_cases hOuter : outer₁ = outer₂
  · subst outer₂
    exact ⟨rfl, Nat.add_left_cancel hEqual⟩
  · have ordered : outer₁ < outer₂ ∨ outer₂ < outer₁ :=
      Nat.lt_or_gt_of_ne hOuter
    cases ordered with
    | inl hLess =>
        have belowNext :
            outer₁ * innerCount + inner₁ <
              (outer₁ + 1) * innerCount := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left hInner₁ (outer₁ * innerCount)
        have nextBelow :
            (outer₁ + 1) * innerCount ≤ outer₂ * innerCount :=
          Nat.mul_le_mul_right innerCount ((Nat.succ_le_iff).mpr hLess)
        have impossible :
            outer₂ * innerCount + inner₂ <
              outer₂ * innerCount := by
          rw [← hEqual]
          exact Nat.lt_of_lt_of_le belowNext nextBelow
        exact False.elim
          ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) impossible)
    | inr hGreater =>
        have belowNext :
            outer₂ * innerCount + inner₂ <
              (outer₂ + 1) * innerCount := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left hInner₂ (outer₂ * innerCount)
        have nextBelow :
            (outer₂ + 1) * innerCount ≤ outer₁ * innerCount :=
          Nat.mul_le_mul_right innerCount ((Nat.succ_le_iff).mpr hGreater)
        have impossible :
            outer₁ * innerCount + inner₁ <
              outer₁ * innerCount := by
          rw [hEqual]
          exact Nat.lt_of_lt_of_le belowNext nextBelow
        exact False.elim
          ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) impossible)

theorem tapeSymbolCode_injective {left right : TapeSymbol}
    (hEqual : tapeSymbolCode left = tapeSymbolCode right) : left = right := by
  cases left <;> cases right <;> cases hEqual <;> rfl

namespace VariableBlock

theorem index_injective (block : VariableBlock)
    {left right : Fin block.width}
    (hEqual : block.index left = block.index right) : left = right := by
  apply Fin.ext
  exact Nat.add_left_cancel hEqual

end VariableBlock

namespace VariableLayout

theorem symbolVariable_injective (layout : VariableLayout)
    {time₁ time₂ : Fin layout.dimensions.timeCount}
    {position₁ position₂ :
      Fin (layout.dimensions.tapeWidth layout.mode)}
    {symbol₁ symbol₂ : TapeSymbol}
    (hEqual : layout.symbolVariable time₁ position₁ symbol₁ =
      layout.symbolVariable time₂ position₂ symbol₂) :
    time₁ = time₂ ∧ position₁ = position₂ ∧ symbol₁ = symbol₂ := by
  have localEqual :
      layout.symbolLocalIndex time₁ position₁ symbol₁ =
        layout.symbolLocalIndex time₂ position₂ symbol₂ :=
    VariableBlock.index_injective layout.symbolBlock hEqual
  have flattenedEqual :
      flattenTwo
          (flattenTwo time₁.val position₁.val
            (layout.dimensions.tapeWidth layout.mode))
          (tapeSymbolCode symbol₁) 3 =
        flattenTwo
          (flattenTwo time₂.val position₂.val
            (layout.dimensions.tapeWidth layout.mode))
          (tapeSymbolCode symbol₂) 3 :=
    congrArg Fin.val localEqual
  have outerAndSymbol := flattenTwo_injective
    (tapeSymbolCode_lt_three symbol₁)
    (tapeSymbolCode_lt_three symbol₂) flattenedEqual
  have timeAndPosition := flattenTwo_injective
    position₁.isLt position₂.isLt outerAndSymbol.left
  exact ⟨Fin.ext timeAndPosition.left,
    Fin.ext timeAndPosition.right,
    tapeSymbolCode_injective outerAndSymbol.right⟩

theorem headVariable_injective (layout : VariableLayout)
    {time₁ time₂ : Fin layout.dimensions.timeCount}
    {position₁ position₂ :
      Fin (layout.dimensions.tapeWidth layout.mode)}
    (hEqual : layout.headVariable time₁ position₁ =
      layout.headVariable time₂ position₂) :
    time₁ = time₂ ∧ position₁ = position₂ := by
  have localEqual :
      layout.headLocalIndex time₁ position₁ =
        layout.headLocalIndex time₂ position₂ :=
    VariableBlock.index_injective layout.headBlock hEqual
  have flattenedEqual :
      flattenTwo time₁.val position₁.val
          (layout.dimensions.tapeWidth layout.mode) =
        flattenTwo time₂.val position₂.val
          (layout.dimensions.tapeWidth layout.mode) :=
    congrArg Fin.val localEqual
  have coordinates := flattenTwo_injective
    position₁.isLt position₂.isLt flattenedEqual
  exact ⟨Fin.ext coordinates.left, Fin.ext coordinates.right⟩

theorem stateVariable_injective (layout : VariableLayout)
    {time₁ time₂ : Fin layout.dimensions.timeCount}
    {state₁ state₂ : Fin layout.dimensions.stateBound}
    (hEqual : layout.stateVariable time₁ state₁ =
      layout.stateVariable time₂ state₂) :
    time₁ = time₂ ∧ state₁ = state₂ := by
  have localEqual :
      layout.stateLocalIndex time₁ state₁ =
        layout.stateLocalIndex time₂ state₂ :=
    VariableBlock.index_injective layout.stateBlock hEqual
  have flattenedEqual :
      flattenTwo time₁.val state₁.val layout.dimensions.stateBound =
        flattenTwo time₂.val state₂.val layout.dimensions.stateBound :=
    congrArg Fin.val localEqual
  have coordinates := flattenTwo_injective
    state₁.isLt state₂.isLt flattenedEqual
  exact ⟨Fin.ext coordinates.left, Fin.ext coordinates.right⟩

theorem certificateBitVariable_injective (layout : VariableLayout)
    {left right : Fin layout.certificateBitWidth}
    (hEqual : layout.certificateBitVariable left =
      layout.certificateBitVariable right) : left = right :=
  VariableBlock.index_injective layout.certificateBitBlock hEqual

theorem certificateLengthVariable_injective (layout : VariableLayout)
    {left right : Fin layout.certificateLengthWidth}
    (hEqual : layout.certificateLengthVariable left =
      layout.certificateLengthVariable right) : left = right :=
  VariableBlock.index_injective layout.certificateLengthBlock hEqual

theorem symbolEnd_le_stateOffset (layout : VariableLayout) :
    layout.symbolBlock.endOffset ≤ layout.stateBlock.offset := by
  exact Nat.le_add_right layout.symbolBlock.endOffset layout.headBlock.width

theorem symbolEnd_le_certificateBitOffset (layout : VariableLayout) :
    layout.symbolBlock.endOffset ≤ layout.certificateBitBlock.offset := by
  exact Nat.le_trans layout.symbolEnd_le_stateOffset
    (Nat.le_add_right layout.stateBlock.offset layout.stateBlock.width)

theorem headEnd_le_certificateBitOffset (layout : VariableLayout) :
    layout.headBlock.endOffset ≤ layout.certificateBitBlock.offset := by
  exact Nat.le_add_right layout.stateBlock.offset layout.stateBlock.width

theorem symbolEnd_le_certificateLengthOffset (layout : VariableLayout) :
    layout.symbolBlock.endOffset ≤ layout.certificateLengthBlock.offset := by
  exact Nat.le_trans layout.symbolEnd_le_certificateBitOffset
    (Nat.le_add_right layout.certificateBitBlock.offset
      layout.certificateBitBlock.width)

theorem headEnd_le_certificateLengthOffset (layout : VariableLayout) :
    layout.headBlock.endOffset ≤ layout.certificateLengthBlock.offset := by
  exact Nat.le_trans layout.headEnd_le_certificateBitOffset
    (Nat.le_add_right layout.certificateBitBlock.offset
      layout.certificateBitBlock.width)

theorem stateEnd_le_certificateLengthOffset (layout : VariableLayout) :
    layout.stateBlock.endOffset ≤ layout.certificateLengthBlock.offset := by
  exact Nat.le_add_right layout.certificateBitBlock.offset
    layout.certificateBitBlock.width

end VariableLayout

/-! ### Constructive decoding of one-hot coordinate lists -/

theorem nodup_map_of_injective (mapping : α → β)
    (hInjective : Function.Injective mapping)
    {items : List α} (hNodup : items.Nodup) :
    (items.map mapping).Nodup := by
  induction items with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      have split := List.nodup_cons.mp hNodup
      apply List.nodup_cons.mpr
      constructor
      · intro hMapped
        rcases List.mem_map.mp hMapped with ⟨item, hItem, hEqual⟩
        exact split.left (hInjective hEqual.symm ▸ hItem)
      · exact ih split.right

theorem finiteIndices_nodup (width : Nat) :
    (finiteIndices width).Nodup := by
  induction width with
  | zero => exact List.Pairwise.nil
  | succ width ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro hZero
        rcases List.mem_map.mp hZero with ⟨index, _, hEqual⟩
        have impossible : 0 = index.val + 1 :=
          (congrArg Fin.val hEqual).symm
        cases impossible
      · exact nodup_map_of_injective Fin.succ
          (fun _ _ hEqual => Fin.ext
            (Nat.succ.inj (congrArg Fin.val hEqual))) ih

theorem tapeSymbols_nodup : tapeSymbols.Nodup := by
  decide

theorem AtMostOneTrue.eq_of_mem {width : Nat}
    {variables : List (Fin width)}
    (hNodup : variables.Nodup)
    {left right : Fin width}
    (hLeft : left ∈ variables)
    (hRight : right ∈ variables)
    (assignment : BitString)
    (hAtMost : AtMostOneTrue variables assignment)
    (hLeftTrue : (trueLiteral left).Holds assignment)
    (hRightTrue : (trueLiteral right).Holds assignment) :
    left = right := by
  induction variables with
  | nil => cases hLeft
  | cons first rest ih =>
      have nodupSplit := List.nodup_cons.mp hNodup
      rcases hAtMost with ⟨hFirst, hRest⟩
      cases hLeft with
      | head =>
          cases hRight with
          | head => rfl
          | tail _ hRightRest =>
              exact False.elim
                (hFirst right hRightRest ⟨hLeftTrue, hRightTrue⟩)
      | tail _ hLeftRest =>
          cases hRight with
          | head =>
              exact False.elim
                (hFirst left hLeftRest ⟨hRightTrue, hLeftTrue⟩)
          | tail _ hRightRest =>
              exact ih nodupSplit.right hLeftRest hRightRest
                hRest

def coordinateIsTrue {coordinate : Type}
    {width : Nat} (assignment : BitString)
    (coordinateVariable : coordinate → Fin width)
    (item : coordinate) : Bool :=
  assignmentAt assignment (coordinateVariable item).val == some true

theorem coordinateIsTrue_eq_true_iff {coordinate : Type}
    {width : Nat} (assignment : BitString)
    (coordinateVariable : coordinate → Fin width) (item : coordinate) :
    coordinateIsTrue assignment coordinateVariable item = true ↔
      (trueLiteral (coordinateVariable item)).Holds assignment := by
  simp [coordinateIsTrue, trueLiteral, BoundedLiteral.Holds]

def selectCoordinate {coordinate : Type}
    {width : Nat} (coordinates : List coordinate)
    (fallback : coordinate) (assignment : BitString)
    (coordinateVariable : coordinate → Fin width) : coordinate :=
  (coordinates.find?
    (coordinateIsTrue assignment coordinateVariable)).getD fallback

theorem selectCoordinate_holds {coordinate : Type}
    {width : Nat} (coordinates : List coordinate)
    (fallback : coordinate) (assignment : BitString)
    (coordinateVariable : coordinate → Fin width)
    (hAny : AnyTrue (coordinates.map coordinateVariable) assignment) :
    (trueLiteral
      (coordinateVariable
        (selectCoordinate coordinates fallback assignment
          coordinateVariable))).Holds
        assignment := by
  rcases hAny with ⟨selectedVariable, hSelectedMem, hSelectedTrue⟩
  rcases List.mem_map.mp hSelectedMem with
    ⟨candidate, hCandidateMem, hCandidateEqual⟩
  have hCandidateTrue :
      coordinateIsTrue assignment coordinateVariable candidate = true :=
    (coordinateIsTrue_eq_true_iff assignment coordinateVariable candidate).mpr
      (hCandidateEqual ▸ hSelectedTrue)
  have hSome :
      (coordinates.find?
        (coordinateIsTrue assignment coordinateVariable)).isSome =
        true :=
    (List.find?_isSome).mpr
      ⟨candidate, hCandidateMem, hCandidateTrue⟩
  have hNotNone :
      coordinates.find? (coordinateIsTrue assignment coordinateVariable) ≠
        none := by
    intro hNone
    rw [hNone] at hSome
    cases hSome
  clear hSome
  cases hFind : coordinates.find?
      (coordinateIsTrue assignment coordinateVariable) with
  | none => exact False.elim (hNotNone hFind)
  | some selected =>
      unfold selectCoordinate
      rw [hFind]
      exact (coordinateIsTrue_eq_true_iff assignment coordinateVariable
        selected).mp
        (List.find?_some hFind)

theorem selectCoordinate_mem {coordinate : Type}
    {width : Nat} (coordinates : List coordinate)
    (fallback : coordinate) (assignment : BitString)
    (coordinateVariable : coordinate → Fin width)
    (hAny : AnyTrue (coordinates.map coordinateVariable) assignment) :
    selectCoordinate coordinates fallback assignment coordinateVariable ∈
      coordinates := by
  rcases hAny with ⟨selectedVariable, hSelectedMem, hSelectedTrue⟩
  rcases List.mem_map.mp hSelectedMem with
    ⟨candidate, hCandidateMem, hCandidateEqual⟩
  have hCandidateTrue :
      coordinateIsTrue assignment coordinateVariable candidate = true :=
    (coordinateIsTrue_eq_true_iff assignment coordinateVariable candidate).mpr
      (hCandidateEqual ▸ hSelectedTrue)
  have hSome :
      (coordinates.find?
        (coordinateIsTrue assignment coordinateVariable)).isSome = true :=
    (List.find?_isSome).mpr
      ⟨candidate, hCandidateMem, hCandidateTrue⟩
  have hNotNone :
      coordinates.find? (coordinateIsTrue assignment coordinateVariable) ≠
        none := by
    intro hNone
    rw [hNone] at hSome
    cases hSome
  clear hSome
  cases hFind : coordinates.find?
      (coordinateIsTrue assignment coordinateVariable) with
  | none => exact False.elim (hNotNone hFind)
  | some selected =>
      unfold selectCoordinate
      rw [hFind]
      exact List.mem_of_find?_eq_some hFind

theorem selectCoordinate_eq_of_holds {coordinate : Type}
    {width : Nat} (coordinates : List coordinate)
    (fallback : coordinate) (assignment : BitString)
    (coordinateVariable : coordinate → Fin width)
    (hNodup : (coordinates.map coordinateVariable).Nodup)
    (hExactly : ExactlyOneTrue
      (coordinates.map coordinateVariable) assignment)
    (candidate : coordinate) (hCandidateMem : candidate ∈ coordinates)
    (hCandidateTrue :
      (trueLiteral (coordinateVariable candidate)).Holds assignment)
    (hInjective : Function.Injective coordinateVariable) :
    selectCoordinate coordinates fallback assignment coordinateVariable =
      candidate := by
  apply hInjective
  exact AtMostOneTrue.eq_of_mem hNodup
    (List.mem_map.mpr
      ⟨selectCoordinate coordinates fallback assignment coordinateVariable,
        selectCoordinate_mem coordinates fallback assignment coordinateVariable
          hExactly.left,
        rfl⟩)
    (List.mem_map.mpr ⟨candidate, hCandidateMem, rfl⟩)
    assignment hExactly.right
    (selectCoordinate_holds coordinates fallback assignment coordinateVariable
      hExactly.left)
    hCandidateTrue

namespace LocalProgram

theorem holds_of_mem {width : Nat}
    {program : LocalProgram width} {assignment : BitString}
    (hHolds : Holds program assignment)
    {constraint : LocalConstraint width}
    (hMem : constraint ∈ program) :
    LocalConstraint.Holds constraint assignment := by
  induction program with
  | nil => cases hMem
  | cons first rest ih =>
      rcases hHolds with ⟨hFirst, hRest⟩
      cases hMem with
      | head => exact hFirst
      | tail _ hTail => exact ih hRest hTail

theorem holds_of_subset {width : Nat}
    {program subprogram : LocalProgram width} {assignment : BitString}
    (hHolds : Holds program assignment)
    (hSubset : ∀ constraint, constraint ∈ subprogram →
      constraint ∈ program) :
    Holds subprogram assignment := by
  induction subprogram with
  | nil => exact True.intro
  | cons first rest ih =>
      exact ⟨holds_of_mem hHolds (hSubset first (List.Mem.head rest)),
        ih (fun constraint hMem =>
          hSubset constraint (List.Mem.tail first hMem))⟩

theorem holds_of_all {width : Nat}
    {program : LocalProgram width} {assignment : BitString}
    (hAll : ∀ constraint, constraint ∈ program →
      LocalConstraint.Holds constraint assignment) :
    Holds program assignment := by
  induction program with
  | nil => exact True.intro
  | cons first rest ih =>
      exact ⟨hAll first (List.Mem.head rest),
        ih (fun constraint hMem =>
          hAll constraint (List.Mem.tail first hMem))⟩

theorem holds_append {width : Nat}
    (left right : LocalProgram width) (assignment : BitString) :
    Holds (left ++ right) assignment ↔
      Holds left assignment ∧ Holds right assignment := by
  induction left with
  | nil =>
      constructor
      · intro hRight
        exact ⟨True.intro, hRight⟩
      · intro conjunction
        exact conjunction.right
  | cons first rest ih =>
      change
        (LocalConstraint.Holds first assignment ∧
          Holds (rest ++ right) assignment) ↔
        (LocalConstraint.Holds first assignment ∧ Holds rest assignment) ∧
          Holds right assignment
      constructor
      · intro conjunction
        have tail := ih.mp conjunction.right
        exact ⟨⟨conjunction.left, tail.left⟩, tail.right⟩
      · intro conjunction
        exact ⟨conjunction.left.left,
          ih.mpr ⟨conjunction.left.right, conjunction.right⟩⟩

end LocalProgram

theorem AtMostOneTrue.of_pairwise {width : Nat}
    {variables : List (Fin width)} (assignment : BitString)
    (hNodup : variables.Nodup)
    (hUnique : ∀ left right, left ∈ variables → right ∈ variables →
      (trueLiteral left).Holds assignment →
      (trueLiteral right).Holds assignment → left = right) :
    AtMostOneTrue variables assignment := by
  induction variables with
  | nil => exact True.intro
  | cons first rest ih =>
      have nodupSplit := List.nodup_cons.mp hNodup
      constructor
      · intro next hNext hBoth
        have equal := hUnique first next (List.Mem.head rest)
          (List.Mem.tail first hNext) hBoth.left hBoth.right
        exact nodupSplit.left (equal ▸ hNext)
      · apply ih nodupSplit.right
        intro left right hLeft hRight hLeftTrue hRightTrue
        exact hUnique left right (List.Mem.tail first hLeft)
          (List.Mem.tail first hRight) hLeftTrue hRightTrue

theorem ExactlyOneTrue.of_selected {width : Nat}
    {variables : List (Fin width)} (assignment : BitString)
    (hNodup : variables.Nodup)
    (selected : Fin width) (hSelectedMem : selected ∈ variables)
    (hSelectedTrue : (trueLiteral selected).Holds assignment)
    (hOnly : ∀ candidate, candidate ∈ variables →
      (trueLiteral candidate).Holds assignment → candidate = selected) :
    ExactlyOneTrue variables assignment :=
  ⟨⟨selected, hSelectedMem, hSelectedTrue⟩,
    AtMostOneTrue.of_pairwise assignment hNodup
      (fun left right hLeft hRight hLeftTrue hRightTrue =>
        (hOnly left hLeft hLeftTrue).trans
          (hOnly right hRight hRightTrue).symm)⟩

def finMembershipValue {width : Nat}
    (variables : List (Fin width)) (index : Nat) : Bool :=
  if index ∈ variables.map Fin.val then true else false

theorem finMembershipValue_eq_true_iff {width : Nat}
    (variables : List (Fin width)) (index : Fin width) :
    finMembershipValue variables index.val = true ↔ index ∈ variables := by
  unfold finMembershipValue
  by_cases hMem : index.val ∈ variables.map Fin.val
  · rw [if_pos hMem]
    constructor
    · intro _
      rcases List.mem_map.mp hMem with ⟨candidate, hCandidate, hEqual⟩
      have equalFin : candidate = index := Fin.ext hEqual
      exact equalFin ▸ hCandidate
    · intro _
      rfl
  · rw [if_neg hMem]
    constructor
    · intro impossible
      cases impossible
    · intro hIndex
      exact False.elim (hMem (List.mem_map.mpr ⟨index, hIndex, rfl⟩))

/-! ### Intrinsic finite rows and their literal successor -/

namespace VerifierTableauProblem

def symbolCoordinateVariable {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : Fin problem.FormulaWidth :=
  (problem.symbolLiteral time position symbol).index

def headCoordinateVariable {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    Fin problem.FormulaWidth :=
  (problem.headLiteral time position).index

def stateCoordinateVariable {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (state : Fin problem.dimensions.stateBound) :
    Fin problem.FormulaWidth :=
  (problem.stateLiteral time state).index

theorem symbolCoordinateVariable_injective {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    Function.Injective (problem.symbolCoordinateVariable time position) := by
  intro left right hEqual
  have numericEqual :
      problem.layout.symbolVariable time position left =
        problem.layout.symbolVariable time position right :=
    congrArg Fin.val hEqual
  exact (problem.layout.symbolVariable_injective numericEqual).right.right

theorem headCoordinateVariable_injective {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    Function.Injective (problem.headCoordinateVariable time) := by
  intro left right hEqual
  have numericEqual :
      problem.layout.headVariable time left =
        problem.layout.headVariable time right :=
    congrArg Fin.val hEqual
  exact (problem.layout.headVariable_injective numericEqual).right

theorem stateCoordinateVariable_injective {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    Function.Injective (problem.stateCoordinateVariable time) := by
  intro left right hEqual
  have numericEqual :
      problem.layout.stateVariable time left =
        problem.layout.stateVariable time right :=
    congrArg Fin.val hEqual
  exact (problem.layout.stateVariable_injective numericEqual).right

theorem symbolVariables_nodup {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.symbolVariables time position).Nodup := by
  exact nodup_map_of_injective
    (problem.symbolCoordinateVariable time position)
    (problem.symbolCoordinateVariable_injective time position)
    tapeSymbols_nodup

theorem headVariables_nodup {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.headVariables time).Nodup := by
  exact nodup_map_of_injective
    (problem.headCoordinateVariable time)
    (problem.headCoordinateVariable_injective time)
    (finiteIndices_nodup _)

theorem stateVariables_nodup {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    (problem.stateVariables time).Nodup := by
  exact nodup_map_of_injective
    (problem.stateCoordinateVariable time)
    (problem.stateCoordinateVariable_injective time)
    (finiteIndices_nodup _)

def decodedSymbol {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) : TapeSymbol :=
  selectCoordinate tapeSymbols .blank assignment
    (problem.symbolCoordinateVariable time position)

def decodedHead {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (time : Fin problem.dimensions.timeCount) :
    Fin (problem.dimensions.tapeWidth problem.tableauInputMode) :=
  selectCoordinate
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    problem.initialHeadPosition assignment
    (problem.headCoordinateVariable time)

def decodedState {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (time : Fin problem.dimensions.timeCount) :
    Fin problem.dimensions.stateBound :=
  selectCoordinate (finiteIndices problem.dimensions.stateBound)
    problem.startState assignment
    (problem.stateCoordinateVariable time)

structure FiniteRow {language : Language}
    (problem : VerifierTableauProblem language) where
  state : Fin problem.dimensions.stateBound
  head : Fin (problem.dimensions.tapeWidth problem.tableauInputMode)
  symbol :
    Fin (problem.dimensions.tapeWidth problem.tableauInputMode) → TapeSymbol

def decodedRow {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (time : Fin problem.dimensions.timeCount) : problem.FiniteRow :=
  { state := problem.decodedState assignment time
    head := problem.decodedHead assignment time
    symbol := problem.decodedSymbol assignment time }

theorem symbolShapeAt_mem_shapeProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.symbolShapeAt time position ∈ problem.shapeProgram := by
  apply List.mem_flatMap.mpr
  refine ⟨time, finiteIndices_mem time, ?_⟩
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨position, finiteIndices_mem position, rfl⟩

theorem headShapeAt_mem_shapeProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    problem.headShapeAt time ∈ problem.shapeProgram := by
  apply List.mem_flatMap.mpr
  refine ⟨time, finiteIndices_mem time, ?_⟩
  apply List.mem_append_right (problem.symbolShapeRow time)
  exact List.Mem.head _

theorem stateShapeAt_mem_shapeProgram {language : Language}
    (problem : VerifierTableauProblem language)
    (time : Fin problem.dimensions.timeCount) :
    problem.stateShapeAt time ∈ problem.shapeProgram := by
  apply List.mem_flatMap.mpr
  refine ⟨time, finiteIndices_mem time, ?_⟩
  apply List.mem_append_right (problem.symbolShapeRow time)
  exact List.Mem.tail _ (List.Mem.head _)

theorem shapeConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language)
    {constraint : LocalConstraint problem.FormulaWidth}
    (hMem : constraint ∈ problem.shapeProgram) :
    constraint ∈ problem.program := by
  apply List.mem_append_left problem.acceptanceProgram
  apply List.mem_append_left problem.transitionProgram
  apply List.mem_append_left problem.initialProgram
  exact hMem

theorem symbolExactlyOne_of_program {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    ExactlyOneTrue (problem.symbolVariables time position) assignment := by
  exact LocalProgram.holds_of_mem hProgram
    (problem.shapeConstraint_mem_program
      (problem.symbolShapeAt_mem_shapeProgram time position))

theorem headExactlyOne_of_program {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount) :
    ExactlyOneTrue (problem.headVariables time) assignment := by
  exact LocalProgram.holds_of_mem hProgram
    (problem.shapeConstraint_mem_program
      (problem.headShapeAt_mem_shapeProgram time))

theorem stateExactlyOne_of_program {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount) :
    ExactlyOneTrue (problem.stateVariables time) assignment := by
  exact LocalProgram.holds_of_mem hProgram
    (problem.shapeConstraint_mem_program
      (problem.stateShapeAt_mem_shapeProgram time))

theorem decodedSymbol_literal_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.symbolLiteral time position
      (problem.decodedSymbol assignment time position)).Holds assignment := by
  change
    (trueLiteral
      (problem.symbolCoordinateVariable time position
        (problem.decodedSymbol assignment time position))).Holds assignment
  exact selectCoordinate_holds tapeSymbols .blank assignment
    (problem.symbolCoordinateVariable time position)
    (problem.symbolExactlyOne_of_program assignment hProgram time position).left

theorem decodedHead_literal_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount) :
    (problem.headLiteral time
      (problem.decodedHead assignment time)).Holds assignment := by
  change
    (trueLiteral
      (problem.headCoordinateVariable time
        (problem.decodedHead assignment time))).Holds assignment
  exact selectCoordinate_holds
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    problem.initialHeadPosition assignment
    (problem.headCoordinateVariable time)
    (problem.headExactlyOne_of_program assignment hProgram time).left

theorem decodedState_literal_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount) :
    (problem.stateLiteral time
      (problem.decodedState assignment time)).Holds assignment := by
  change
    (trueLiteral
      (problem.stateCoordinateVariable time
        (problem.decodedState assignment time))).Holds assignment
  exact selectCoordinate_holds
    (finiteIndices problem.dimensions.stateBound)
    problem.startState assignment
    (problem.stateCoordinateVariable time)
    (problem.stateExactlyOne_of_program assignment hProgram time).left

theorem symbolLiteral_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    (problem.symbolLiteral time position symbol).Holds assignment ↔
      problem.decodedSymbol assignment time position = symbol := by
  constructor
  · intro hSymbol
    apply selectCoordinate_eq_of_holds tapeSymbols .blank assignment
      (problem.symbolCoordinateVariable time position)
      (problem.symbolVariables_nodup time position)
      (problem.symbolExactlyOne_of_program assignment hProgram time position)
      symbol (tapeSymbols_mem symbol)
    · exact hSymbol
    · exact problem.symbolCoordinateVariable_injective time position
  · intro hEqual
    rw [← hEqual]
    exact problem.decodedSymbol_literal_holds assignment hProgram time position

theorem headLiteral_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.headLiteral time position).Holds assignment ↔
      problem.decodedHead assignment time = position := by
  constructor
  · intro hHead
    apply selectCoordinate_eq_of_holds
      (finiteIndices
        (problem.dimensions.tapeWidth problem.tableauInputMode))
      problem.initialHeadPosition assignment
      (problem.headCoordinateVariable time)
      (problem.headVariables_nodup time)
      (problem.headExactlyOne_of_program assignment hProgram time)
      position (finiteIndices_mem position)
    · exact hHead
    · exact problem.headCoordinateVariable_injective time
  · intro hEqual
    rw [← hEqual]
    exact problem.decodedHead_literal_holds assignment hProgram time

theorem stateLiteral_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (time : Fin problem.dimensions.timeCount)
    (state : Fin problem.dimensions.stateBound) :
    (problem.stateLiteral time state).Holds assignment ↔
      problem.decodedState assignment time = state := by
  constructor
  · intro hState
    apply selectCoordinate_eq_of_holds
      (finiteIndices problem.dimensions.stateBound)
      problem.startState assignment
      (problem.stateCoordinateVariable time)
      (problem.stateVariables_nodup time)
      (problem.stateExactlyOne_of_program assignment hProgram time)
      state (finiteIndices_mem state)
    · exact hState
    · exact problem.stateCoordinateVariable_injective time
  · intro hEqual
    rw [← hEqual]
    exact problem.decodedState_literal_holds assignment hProgram time

/-! ### Exact initial control, certificate selection, and acceptance -/

theorem initialConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language)
    {constraint : LocalConstraint problem.FormulaWidth}
    (hMem : constraint ∈ problem.initialProgram) :
    constraint ∈ problem.program := by
  apply List.mem_append_left problem.acceptanceProgram
  apply List.mem_append_left problem.transitionProgram
  exact List.mem_append_right problem.shapeProgram hMem

theorem acceptanceConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language) :
    (.require
      (problem.stateLiteral problem.finalTime problem.acceptingState) :
        LocalConstraint problem.FormulaWidth) ∈ problem.program := by
  apply List.mem_append_right
    (problem.shapeProgram ++ problem.initialProgram ++ problem.transitionProgram)
  exact List.Mem.head _

theorem decodedInitialState {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment) :
    problem.decodedState assignment problem.initialTime =
      problem.startState := by
  have required := LocalProgram.holds_of_mem hProgram
    (problem.initialConstraint_mem_program (List.Mem.head _))
  exact (problem.stateLiteral_holds_iff assignment hProgram
    problem.initialTime problem.startState).mp required

theorem decodedInitialHead {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment) :
    problem.decodedHead assignment problem.initialTime =
      problem.initialHeadPosition := by
  have localMem :
      (.require
        (problem.headLiteral problem.initialTime problem.initialHeadPosition) :
          LocalConstraint problem.FormulaWidth) ∈ problem.initialProgram :=
    List.Mem.tail _ (List.Mem.head _)
  have required := LocalProgram.holds_of_mem hProgram
    (problem.initialConstraint_mem_program localMem)
  exact (problem.headLiteral_holds_iff assignment hProgram
    problem.initialTime problem.initialHeadPosition).mp required

theorem decodedFinalAccepting {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment) :
    problem.decodedState assignment problem.finalTime =
      problem.acceptingState := by
  have required := LocalProgram.holds_of_mem hProgram
    problem.acceptanceConstraint_mem_program
  exact (problem.stateLiteral_holds_iff assignment hProgram
    problem.finalTime problem.acceptingState).mp required

def pairedLengthCoordinateVariable {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    Fin problem.FormulaWidth :=
  (problem.pairedLengthLiteral hMode length).index

def pairedBitCoordinateVariable {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (index : Fin problem.certificateLimit) :
    Fin problem.FormulaWidth :=
  (problem.pairedBitLiteral hMode index).index

theorem pairedLengthCoordinateVariable_injective {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    Function.Injective (problem.pairedLengthCoordinateVariable hMode) := by
  intro left right hEqual
  have numericEqual :
      problem.layout.certificateLengthVariable
          (problem.pairedCertificateLengthIndex hMode left) =
        problem.layout.certificateLengthVariable
          (problem.pairedCertificateLengthIndex hMode right) :=
    congrArg Fin.val hEqual
  have castEqual :=
    problem.layout.certificateLengthVariable_injective numericEqual
  have valueEqual :
      (problem.pairedCertificateLengthIndex hMode left).val =
        (problem.pairedCertificateLengthIndex hMode right).val :=
    congrArg Fin.val castEqual
  change left.val = right.val at valueEqual
  exact Fin.ext valueEqual

theorem pairedBitCoordinateVariable_injective {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    Function.Injective (problem.pairedBitCoordinateVariable hMode) := by
  intro left right hEqual
  have numericEqual :
      problem.layout.certificateBitVariable
          (problem.pairedCertificateBitIndex hMode left) =
        problem.layout.certificateBitVariable
          (problem.pairedCertificateBitIndex hMode right) :=
    congrArg Fin.val hEqual
  have castEqual := problem.layout.certificateBitVariable_injective numericEqual
  have valueEqual :
      (problem.pairedCertificateBitIndex hMode left).val =
        (problem.pairedCertificateBitIndex hMode right).val :=
    congrArg Fin.val castEqual
  change left.val = right.val at valueEqual
  exact Fin.ext valueEqual

theorem pairedLengthVariables_nodup {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired) :
    (problem.pairedLengthVariables hMode).Nodup := by
  exact nodup_map_of_injective
    (problem.pairedLengthCoordinateVariable hMode)
    (problem.pairedLengthCoordinateVariable_injective hMode)
    (finiteIndices_nodup _)

theorem pairedLengthExactlyOne_of_program {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    ExactlyOneTrue
      (problem.pairedLengthVariables
        (problem.tableauInputMode_of_paired hVerifierMode)) assignment := by
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  have localMem :
      (.exactlyOne (problem.pairedLengthVariables hMode) :
        LocalConstraint problem.FormulaWidth) ∈ problem.initialProgram := by
    apply List.mem_append_right
      [(.require
          (problem.stateLiteral problem.initialTime problem.startState) :
          LocalConstraint problem.FormulaWidth),
       (.require
          (problem.headLiteral problem.initialTime
            problem.initialHeadPosition) :
          LocalConstraint problem.FormulaWidth)]
    change
      (.exactlyOne (problem.pairedLengthVariables hMode) :
        LocalConstraint problem.FormulaWidth) ∈
        problem.initialSymbolsProgram
    unfold initialSymbolsProgram
    split
    next hInputOnly =>
      have impossible :
          VerifierInputMode.inputOnly = VerifierInputMode.paired :=
        hInputOnly.symm.trans hVerifierMode
      cases impossible
    next hPaired =>
      exact List.Mem.head _
  exact LocalProgram.holds_of_mem hProgram
    (problem.initialConstraint_mem_program localMem)

def decodedCertificateLength {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    Fin (problem.certificateLimit + 1) :=
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  selectCoordinate (finiteIndices (problem.certificateLimit + 1))
    ⟨0, Nat.zero_lt_succ problem.certificateLimit⟩ assignment
    (problem.pairedLengthCoordinateVariable hMode)

theorem decodedCertificateLength_literal_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    (problem.pairedLengthLiteral
      (problem.tableauInputMode_of_paired hVerifierMode)
      (problem.decodedCertificateLength assignment hVerifierMode)).Holds
        assignment := by
  change
    (trueLiteral
      (problem.pairedLengthCoordinateVariable
        (problem.tableauInputMode_of_paired hVerifierMode)
        (problem.decodedCertificateLength assignment hVerifierMode))).Holds
      assignment
  exact selectCoordinate_holds
    (finiteIndices (problem.certificateLimit + 1))
    ⟨0, Nat.zero_lt_succ problem.certificateLimit⟩ assignment
    (problem.pairedLengthCoordinateVariable
      (problem.tableauInputMode_of_paired hVerifierMode))
    (problem.pairedLengthExactlyOne_of_program assignment hProgram
      hVerifierMode).left

def decodedCertificateBit {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (index : Fin problem.certificateLimit) : Bool :=
  (assignmentAt assignment
    (problem.pairedBitCoordinateVariable
      (problem.tableauInputMode_of_paired hVerifierMode) index).val).getD false

theorem decodedCertificateBit_eq_true_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (index : Fin problem.certificateLimit) :
    problem.decodedCertificateBit assignment hVerifierMode index = true ↔
      (problem.pairedBitLiteral
        (problem.tableauInputMode_of_paired hVerifierMode) index).Holds
          assignment := by
  unfold decodedCertificateBit pairedBitCoordinateVariable
    pairedBitLiteral certificateBitLiteral BoundedLiteral.Holds
  cases hValue : assignmentAt assignment
      (problem.layout.certificateBitVariable
        (problem.pairedCertificateBitIndex
          (problem.tableauInputMode_of_paired hVerifierMode) index)) with
  | none => simp
  | some value => cases value <;> simp

theorem decodedCertificateLength_le {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    (problem.decodedCertificateLength assignment hVerifierMode).val ≤
      problem.certificateLimit :=
  (Nat.lt_succ_iff).mp
    (problem.decodedCertificateLength assignment hVerifierMode).isLt

def initialCellSymbol (certificateBit : Fin certificateWidth → Bool) :
    InitialCell certificateWidth → TapeSymbol
  | .blank => .blank
  | .fixed value => symbolOfFixedBit value
  | .certificate index =>
      if certificateBit index then .one else .zero

def inputOnlyInitialSymbol {language : Language}
    (problem : VerifierTableauProblem language)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    TapeSymbol :=
  initialCellSymbol (fun index : Fin 0 => Fin.elim0 index)
    (initialCellAt (inputOnlyInitialCells problem.input)
      problem.uniformFuel position.val)

def pairedInitialSymbolFor {language : Language}
    (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1))
    (certificateBit : Fin problem.certificateLimit → Bool)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    TapeSymbol :=
  initialCellSymbol certificateBit
    (initialCellAt
      (pairedInitialCells problem.input problem.certificateLimit length)
      problem.uniformFuel position.val)

def pairedInitialSymbol {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    TapeSymbol :=
  problem.pairedInitialSymbolFor
    (problem.decodedCertificateLength assignment hVerifierMode)
    (problem.decodedCertificateBit assignment hVerifierMode) position

theorem inputOnlyCellProgram_eq {language : Language}
    (problem : VerifierTableauProblem language)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.inputOnlyCellProgram position =
      [problem.fixedInitialCellConstraint position
        (problem.inputOnlyInitialSymbol position)] := by
  unfold inputOnlyCellProgram inputOnlyInitialSymbol initialCellSymbol
  generalize hCell : initialCellAt (inputOnlyInitialCells problem.input)
    problem.uniformFuel position.val = cell
  cases cell with
  | blank => rfl
  | fixed value => rfl
  | certificate index => exact Fin.elim0 index

theorem inputOnlyInitialConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (.require
      (problem.symbolLiteral problem.initialTime position
        (problem.inputOnlyInitialSymbol position)) :
        LocalConstraint problem.FormulaWidth) ∈ problem.program := by
  have cellMem :
      (.require
        (problem.symbolLiteral problem.initialTime position
          (problem.inputOnlyInitialSymbol position)) :
          LocalConstraint problem.FormulaWidth) ∈
        problem.inputOnlyCellProgram position := by
    rw [problem.inputOnlyCellProgram_eq position]
    exact List.Mem.head _
  have inputSymbolsMem :
      (.require
        (problem.symbolLiteral problem.initialTime position
          (problem.inputOnlyInitialSymbol position)) :
          LocalConstraint problem.FormulaWidth) ∈
        problem.inputOnlyInitialSymbolsProgram := by
    apply List.mem_flatMap.mpr
    exact ⟨position, finiteIndices_mem position, cellMem⟩
  have symbolsMem :
      (.require
        (problem.symbolLiteral problem.initialTime position
          (problem.inputOnlyInitialSymbol position)) :
          LocalConstraint problem.FormulaWidth) ∈
        problem.initialSymbolsProgram := by
    unfold initialSymbolsProgram
    split
    next hInputOnly => exact inputSymbolsMem
    next hPaired =>
      have impossible :
          VerifierInputMode.paired = VerifierInputMode.inputOnly :=
        hPaired.symm.trans hVerifierMode
      cases impossible
  apply problem.initialConstraint_mem_program
  exact List.mem_append_right _ symbolsMem

theorem decodedInputOnlyInitialSymbol {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.decodedSymbol assignment problem.initialTime position =
      problem.inputOnlyInitialSymbol position := by
  have required := LocalProgram.holds_of_mem hProgram
    (problem.inputOnlyInitialConstraint_mem_program hVerifierMode position)
  exact (problem.symbolLiteral_holds_iff assignment hProgram
    problem.initialTime position
    (problem.inputOnlyInitialSymbol position)).mp required

theorem pairedCellConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (length : Fin (problem.certificateLimit + 1))
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    {constraint : LocalConstraint problem.FormulaWidth}
    (hMem : constraint ∈ problem.pairedCellProgram
      (problem.tableauInputMode_of_paired hVerifierMode) length position) :
    constraint ∈ problem.program := by
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  have lengthCellsMem : constraint ∈
      problem.pairedCellsForLengthProgram hMode length := by
    apply List.mem_flatMap.mpr
    exact ⟨position, finiteIndices_mem position, hMem⟩
  have pairedSymbolsMem : constraint ∈
      problem.pairedInitialSymbolsProgram hMode := by
    apply List.Mem.tail
    apply List.mem_flatMap.mpr
    exact ⟨length, finiteIndices_mem length, lengthCellsMem⟩
  have symbolsMem : constraint ∈ problem.initialSymbolsProgram := by
    unfold initialSymbolsProgram
    split
    next hInputOnly =>
      have impossible :
          VerifierInputMode.inputOnly = VerifierInputMode.paired :=
        hInputOnly.symm.trans hVerifierMode
      cases impossible
    next hPaired => exact pairedSymbolsMem
  apply problem.initialConstraint_mem_program
  exact List.mem_append_right _ symbolsMem

theorem decodedCertificateBit_negate_holds_of_false
    {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hAssignmentLength : assignment.length = problem.FormulaWidth)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (index : Fin problem.certificateLimit)
    (hFalse :
      problem.decodedCertificateBit assignment hVerifierMode index = false) :
    (problem.pairedBitLiteral
      (problem.tableauInputMode_of_paired hVerifierMode) index).negate.Holds
        assignment := by
  apply (BoundedLiteral.negate_holds_iff_not
    (problem.pairedBitLiteral
      (problem.tableauInputMode_of_paired hVerifierMode) index)
    assignment hAssignmentLength).mpr
  intro hPositive
  have hTrue :=
    (problem.decodedCertificateBit_eq_true_iff assignment hVerifierMode
      index).mpr hPositive
  rw [hFalse] at hTrue
  cases hTrue

theorem decodedPairedInitialSymbol {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hAssignmentLength : assignment.length = problem.FormulaWidth)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.decodedSymbol assignment problem.initialTime position =
      problem.pairedInitialSymbol assignment hVerifierMode position := by
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  let length := problem.decodedCertificateLength assignment hVerifierMode
  let selectedLength := problem.pairedLengthLiteral hMode length
  let cell := initialCellAt
    (pairedInitialCells problem.input problem.certificateLimit length)
    problem.uniformFuel position.val
  have hSelectedLength : selectedLength.Holds assignment :=
    problem.decodedCertificateLength_literal_holds assignment hProgram
      hVerifierMode
  have cellHolds : LocalProgram.Holds
      (problem.pairedCellProgram hMode length position) assignment := by
    apply LocalProgram.holds_of_subset hProgram
    intro constraint hMem
    exact problem.pairedCellConstraint_mem_program hVerifierMode length
      position hMem
  change problem.decodedSymbol assignment problem.initialTime position =
    initialCellSymbol
      (problem.decodedCertificateBit assignment hVerifierMode) cell
  unfold pairedCellProgram at cellHolds
  cases hCell : cell with
  | blank =>
      dsimp [cell] at hCell
      rw [hCell] at cellHolds
      change problem.decodedSymbol assignment problem.initialTime position =
        TapeSymbol.blank
      have conclusion := cellHolds.left ⟨hSelectedLength, True.intro⟩
      exact (problem.symbolLiteral_holds_iff assignment hProgram
        problem.initialTime position .blank).mp conclusion
  | fixed value =>
      dsimp [cell] at hCell
      rw [hCell] at cellHolds
      change problem.decodedSymbol assignment problem.initialTime position =
        symbolOfFixedBit value
      have conclusion := cellHolds.left ⟨hSelectedLength, True.intro⟩
      exact (problem.symbolLiteral_holds_iff assignment hProgram
        problem.initialTime position (symbolOfFixedBit value)).mp conclusion
  | certificate index =>
      dsimp [cell] at hCell
      rw [hCell] at cellHolds
      cases hBit :
          problem.decodedCertificateBit assignment hVerifierMode index with
      | false =>
          simp [initialCellSymbol, hBit]
          have hNegative :=
            problem.decodedCertificateBit_negate_holds_of_false assignment
              hAssignmentLength hVerifierMode index hBit
          have conclusion := cellHolds.right.left
            ⟨hSelectedLength, ⟨hNegative, True.intro⟩⟩
          exact (problem.symbolLiteral_holds_iff assignment hProgram
            problem.initialTime position .zero).mp conclusion
      | true =>
          simp [initialCellSymbol, hBit]
          have hPositive :=
            (problem.decodedCertificateBit_eq_true_iff assignment
              hVerifierMode index).mp hBit
          have conclusion := cellHolds.left
            ⟨hSelectedLength, ⟨hPositive, True.intro⟩⟩
          exact (problem.symbolLiteral_holds_iff assignment hProgram
            problem.initialTime position .one).mp conclusion

/-! ### Membership of every local transition clause in the whole program -/

def stateTransitionConstraint {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : LocalConstraint problem.FormulaWidth :=
  .implication (problem.controlPremises step state position symbol)
    (problem.stateLiteral (problem.nextTime step)
      (problem.localAction state symbol).targetState)

def headTransitionConstraint {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : LocalConstraint problem.FormulaWidth :=
  .implication (problem.controlPremises step state position symbol)
    (problem.headLiteral (problem.nextTime step)
      (movePosition position (problem.localAction state symbol).move))

def writeTransitionConstraint {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) : LocalConstraint problem.FormulaWidth :=
  .implication (problem.controlPremises step state position symbol)
    (problem.symbolLiteral (problem.nextTime step) position
      (problem.localAction state symbol).writeSymbol)

theorem stateTransitionConstraint_mem_controlConstraints
    {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    problem.stateTransitionConstraint step state position symbol ∈
      problem.controlConstraints step state position symbol := by
  exact List.Mem.head _

theorem headTransitionConstraint_mem_controlConstraints
    {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    problem.headTransitionConstraint step state position symbol ∈
      problem.controlConstraints step state position symbol := by
  exact List.Mem.tail _ (List.Mem.head _)

theorem writeTransitionConstraint_mem_controlConstraints
    {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    problem.writeTransitionConstraint step state position symbol ∈
      problem.controlConstraints step state position symbol := by
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem controlConstraint_mem_controlTransitionProgram
    {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol)
    {constraint : LocalConstraint problem.FormulaWidth}
    (hMem : constraint ∈
      problem.controlConstraints step state position symbol) :
    constraint ∈ problem.controlTransitionProgram := by
  apply List.mem_flatMap.mpr
  refine ⟨step, finiteIndices_mem step, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨position, finiteIndices_mem position, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨state, finiteIndices_mem state, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨symbol, tapeSymbols_mem symbol, hMem⟩

theorem controlConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language)
    {constraint : LocalConstraint problem.FormulaWidth}
    (hMem : constraint ∈ problem.controlTransitionProgram) :
    constraint ∈ problem.program := by
  apply List.mem_append_left problem.acceptanceProgram
  apply List.mem_append_right
    (problem.shapeProgram ++ problem.initialProgram)
  exact List.mem_append_left problem.preservationProgram hMem

theorem preservationConstraint_mem_program {language : Language}
    (problem : VerifierTableauProblem language)
    (step : Fin problem.uniformFuel)
    (headPosition otherPosition :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (hDifferent : headPosition ≠ otherPosition)
    (symbol : TapeSymbol) :
    (.implication
      [problem.headLiteral (problem.currentTime step) headPosition,
       problem.symbolLiteral (problem.currentTime step) otherPosition symbol]
      (problem.symbolLiteral (problem.nextTime step) otherPosition symbol) :
        LocalConstraint problem.FormulaWidth) ∈ problem.program := by
  have localMem :
      (.implication
        [problem.headLiteral (problem.currentTime step) headPosition,
         problem.symbolLiteral (problem.currentTime step) otherPosition symbol]
        (problem.symbolLiteral (problem.nextTime step) otherPosition symbol) :
          LocalConstraint problem.FormulaWidth) ∈
        problem.preservationConstraints step headPosition otherPosition := by
    unfold preservationConstraints
    rw [if_neg hDifferent]
    apply List.mem_map.mpr
    exact ⟨symbol, tapeSymbols_mem symbol, rfl⟩
  have preservationMem :
      (.implication
        [problem.headLiteral (problem.currentTime step) headPosition,
         problem.symbolLiteral (problem.currentTime step) otherPosition symbol]
        (problem.symbolLiteral (problem.nextTime step) otherPosition symbol) :
          LocalConstraint problem.FormulaWidth) ∈
        problem.preservationProgram := by
    apply List.mem_flatMap.mpr
    refine ⟨step, finiteIndices_mem step, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨headPosition, finiteIndices_mem headPosition, ?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨otherPosition, finiteIndices_mem otherPosition, localMem⟩
  apply List.mem_append_left problem.acceptanceProgram
  apply List.mem_append_right
    (problem.shapeProgram ++ problem.initialProgram)
  exact List.mem_append_right problem.controlTransitionProgram preservationMem

namespace FiniteRow

theorem extensionality {language : Language}
    {problem : VerifierTableauProblem language}
    (left right : problem.FiniteRow)
    (hState : left.state = right.state)
    (hHead : left.head = right.head)
    (hSymbol : ∀ position, left.symbol position = right.symbol position) :
    left = right := by
  cases left with
  | mk leftState leftHead leftSymbol =>
      cases right with
      | mk rightState rightHead rightSymbol =>
          cases hState
          cases hHead
          have functionsEqual : leftSymbol = rightSymbol := funext hSymbol
          cases functionsEqual
          rfl

def next {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) : problem.FiniteRow :=
  let action := problem.localAction row.state (row.symbol row.head)
  { state := action.targetState
    head := movePosition row.head action.move
    symbol := fun position =>
      if position = row.head then action.writeSymbol else row.symbol position }

@[simp] theorem next_state {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) :
    row.next.state =
      (problem.localAction row.state (row.symbol row.head)).targetState := rfl

@[simp] theorem next_head {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) :
    row.next.head =
      movePosition row.head
        (problem.localAction row.state (row.symbol row.head)).move := rfl

theorem next_symbol_at_head {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow) :
    row.next.symbol row.head =
      (problem.localAction row.state (row.symbol row.head)).writeSymbol := by
  simp [next]

theorem next_symbol_of_ne {language : Language}
    {problem : VerifierTableauProblem language}
    (row : problem.FiniteRow)
    (position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode))
    (hDifferent : position ≠ row.head) :
    row.next.symbol position = row.symbol position := by
  simp [next, hDifferent]

end FiniteRow

/-- A finite tableau supplies one unique row at every represented time. -/
abbrev FiniteTableau {language : Language}
    (problem : VerifierTableauProblem language) :=
  Fin problem.dimensions.timeCount → problem.FiniteRow

/-- Every adjacent finite row is the literal deterministic local successor. -/
def FiniteTransitions {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau) : Prop :=
  ∀ step : Fin problem.uniformFuel,
    tableau (problem.nextTime step) =
      (tableau (problem.currentTime step)).next

def FiniteAcceptingFrom {language : Language}
    (problem : VerifierTableauProblem language)
    (initial : problem.FiniteRow)
    (tableau : problem.FiniteTableau) : Prop :=
  tableau problem.initialTime = initial ∧
    problem.FiniteTransitions tableau ∧
    (tableau problem.finalTime).state = problem.acceptingState

def decodedTableau {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString) : problem.FiniteTableau :=
  problem.decodedRow assignment

def inputOnlyInitialRow {language : Language}
    (problem : VerifierTableauProblem language) : problem.FiniteRow :=
  { state := problem.startState
    head := problem.initialHeadPosition
    symbol := problem.inputOnlyInitialSymbol }

def pairedInitialRowFor {language : Language}
    (problem : VerifierTableauProblem language)
    (length : Fin (problem.certificateLimit + 1))
    (certificateBit : Fin problem.certificateLimit → Bool) :
    problem.FiniteRow :=
  { state := problem.startState
    head := problem.initialHeadPosition
    symbol := problem.pairedInitialSymbolFor length certificateBit }

def pairedInitialRow {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    problem.FiniteRow :=
  problem.pairedInitialRowFor
    (problem.decodedCertificateLength assignment hVerifierMode)
    (problem.decodedCertificateBit assignment hVerifierMode)

def activeSymbolVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau) :
    List (Fin problem.FormulaWidth) :=
  (finiteIndices problem.dimensions.timeCount).flatMap fun time =>
    (finiteIndices
      (problem.dimensions.tapeWidth problem.tableauInputMode)).map
      fun position => problem.symbolCoordinateVariable time position
        ((tableau time).symbol position)

def activeHeadVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau) :
    List (Fin problem.FormulaWidth) :=
  (finiteIndices problem.dimensions.timeCount).map fun time =>
    problem.headCoordinateVariable time (tableau time).head

def activeStateVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau) :
    List (Fin problem.FormulaWidth) :=
  (finiteIndices problem.dimensions.timeCount).map fun time =>
    problem.stateCoordinateVariable time (tableau time).state

def activeCertificateBitVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool) :
    List (Fin problem.FormulaWidth) :=
  ((finiteIndices problem.certificateLimit).filter certificateBit).map
    (problem.pairedBitCoordinateVariable hMode)

def activeCertificateLengthVariables {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (length : Fin (problem.certificateLimit + 1)) :
    List (Fin problem.FormulaWidth) :=
  [problem.pairedLengthCoordinateVariable hMode length]

theorem activeSymbolVariables_mem_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    problem.symbolCoordinateVariable time position symbol ∈
        problem.activeSymbolVariables tableau ↔
      (tableau time).symbol position = symbol := by
  constructor
  · intro hMem
    rcases List.mem_flatMap.mp hMem with ⟨otherTime, _, hAtTime⟩
    rcases List.mem_map.mp hAtTime with
      ⟨otherPosition, _, hEqual⟩
    have numericEqual :
        problem.layout.symbolVariable otherTime otherPosition
            ((tableau otherTime).symbol otherPosition) =
          problem.layout.symbolVariable time position symbol :=
      congrArg Fin.val hEqual
    rcases problem.layout.symbolVariable_injective numericEqual with
      ⟨hTime, hPosition, hSymbol⟩
    cases hTime
    cases hPosition
    exact hSymbol
  · intro hSymbol
    apply List.mem_flatMap.mpr
    refine ⟨time, finiteIndices_mem time, ?_⟩
    apply List.mem_map.mpr
    refine ⟨position, finiteIndices_mem position, ?_⟩
    rw [hSymbol]

theorem activeHeadVariables_mem_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    problem.headCoordinateVariable time position ∈
        problem.activeHeadVariables tableau ↔
      (tableau time).head = position := by
  constructor
  · intro hMem
    rcases List.mem_map.mp hMem with ⟨otherTime, _, hEqual⟩
    have numericEqual :
        problem.layout.headVariable otherTime (tableau otherTime).head =
          problem.layout.headVariable time position :=
      congrArg Fin.val hEqual
    rcases problem.layout.headVariable_injective numericEqual with
      ⟨hTime, hPosition⟩
    cases hTime
    exact hPosition
  · intro hHead
    apply List.mem_map.mpr
    refine ⟨time, finiteIndices_mem time, ?_⟩
    rw [hHead]

theorem activeStateVariables_mem_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (time : Fin problem.dimensions.timeCount)
    (state : Fin problem.dimensions.stateBound) :
    problem.stateCoordinateVariable time state ∈
        problem.activeStateVariables tableau ↔
      (tableau time).state = state := by
  constructor
  · intro hMem
    rcases List.mem_map.mp hMem with ⟨otherTime, _, hEqual⟩
    have numericEqual :
        problem.layout.stateVariable otherTime (tableau otherTime).state =
          problem.layout.stateVariable time state :=
      congrArg Fin.val hEqual
    rcases problem.layout.stateVariable_injective numericEqual with
      ⟨hTime, hState⟩
    cases hTime
    exact hState
  · intro hState
    apply List.mem_map.mpr
    refine ⟨time, finiteIndices_mem time, ?_⟩
    rw [hState]

theorem activeCertificateBitVariables_mem_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (index : Fin problem.certificateLimit) :
    problem.pairedBitCoordinateVariable hMode index ∈
        problem.activeCertificateBitVariables hMode certificateBit ↔
      certificateBit index = true := by
  constructor
  · intro hMem
    rcases List.mem_map.mp hMem with ⟨otherIndex, hFiltered, hEqual⟩
    have indexEqual :=
      problem.pairedBitCoordinateVariable_injective hMode hEqual
    have hTrue := (List.mem_filter.mp hFiltered).right
    exact indexEqual ▸ hTrue
  · intro hTrue
    apply List.mem_map.mpr
    refine ⟨index, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨finiteIndices_mem index, hTrue⟩

theorem activeCertificateLengthVariables_mem_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (hMode : problem.tableauInputMode = .paired)
    (selected candidate : Fin (problem.certificateLimit + 1)) :
    problem.pairedLengthCoordinateVariable hMode candidate ∈
        problem.activeCertificateLengthVariables hMode selected ↔
      selected = candidate := by
  constructor
  · intro hMem
    cases List.mem_cons.mp hMem with
    | inl hEqual =>
        exact problem.pairedLengthCoordinateVariable_injective hMode
          hEqual.symm
    | inr impossible => cases impossible
  · intro hEqual
    rw [hEqual]
    exact List.Mem.head _

def tableauAssignmentValue {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (index : Nat) : Bool :=
  if index < problem.layout.symbolBlock.endOffset then
    finMembershipValue (problem.activeSymbolVariables tableau) index
  else if index < problem.layout.headBlock.endOffset then
    finMembershipValue (problem.activeHeadVariables tableau) index
  else if index < problem.layout.stateBlock.endOffset then
    finMembershipValue (problem.activeStateVariables tableau) index
  else if index < problem.layout.certificateBitBlock.endOffset then
    finMembershipValue certificateBits index
  else
    finMembershipValue certificateLengths index

def tableauAssignment {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth)) :
    BitString :=
  assignmentOf problem.FormulaWidth
    (problem.tableauAssignmentValue tableau certificateBits certificateLengths)

theorem tableauAssignment_length {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth)) :
    (problem.tableauAssignment tableau certificateBits
      certificateLengths).length = problem.FormulaWidth :=
  assignmentOf_length _ _

theorem trueLiteral_tableauAssignment_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (index : Fin problem.FormulaWidth) :
    (trueLiteral index).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔
      problem.tableauAssignmentValue tableau certificateBits
        certificateLengths index.val = true := by
  unfold BoundedLiteral.Holds trueLiteral tableauAssignment
  rw [assignmentAt_assignmentOf problem.FormulaWidth _ index.val index.isLt]
  constructor
  · exact Option.some.inj
  · exact congrArg Option.some

theorem tableauAssignment_symbol_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    (problem.symbolLiteral time position symbol).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔
      (tableau time).symbol position = symbol := by
  change
    (trueLiteral (problem.symbolCoordinateVariable time position symbol)).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔ _
  rw [problem.trueLiteral_tableauAssignment_holds_iff tableau certificateBits
    certificateLengths]
  unfold tableauAssignmentValue
  have inBlock :
      problem.layout.symbolVariable time position symbol <
        problem.layout.symbolBlock.endOffset :=
    VariableBlock.index_lt_endOffset problem.layout.symbolBlock
      (problem.layout.symbolLocalIndex time position symbol)
  have inBlock' :
      (problem.symbolCoordinateVariable time position symbol).val <
        problem.layout.symbolBlock.endOffset := inBlock
  rw [if_pos inBlock']
  rw [finMembershipValue_eq_true_iff]
  exact problem.activeSymbolVariables_mem_iff tableau time position symbol

theorem tableauAssignment_head_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    (problem.headLiteral time position).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔
      (tableau time).head = position := by
  change
    (trueLiteral (problem.headCoordinateVariable time position)).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔ _
  rw [problem.trueLiteral_tableauAssignment_holds_iff tableau certificateBits
    certificateLengths]
  unfold tableauAssignmentValue
  have afterSymbols :
      ¬ problem.layout.headVariable time position <
        problem.layout.symbolBlock.endOffset := by
    exact Nat.not_lt_of_ge
      (VariableBlock.offset_le_index problem.layout.headBlock
        (problem.layout.headLocalIndex time position))
  have inBlock :
      problem.layout.headVariable time position <
        problem.layout.headBlock.endOffset :=
    VariableBlock.index_lt_endOffset problem.layout.headBlock
      (problem.layout.headLocalIndex time position)
  have afterSymbols' :
      ¬ (problem.headCoordinateVariable time position).val <
        problem.layout.symbolBlock.endOffset := afterSymbols
  have inBlock' :
      (problem.headCoordinateVariable time position).val <
        problem.layout.headBlock.endOffset := inBlock
  rw [if_neg afterSymbols', if_pos inBlock']
  rw [finMembershipValue_eq_true_iff]
  exact problem.activeHeadVariables_mem_iff tableau time position

theorem tableauAssignment_state_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (time : Fin problem.dimensions.timeCount)
    (state : Fin problem.dimensions.stateBound) :
    (problem.stateLiteral time state).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔
      (tableau time).state = state := by
  change
    (trueLiteral (problem.stateCoordinateVariable time state)).Holds
        (problem.tableauAssignment tableau certificateBits
          certificateLengths) ↔ _
  rw [problem.trueLiteral_tableauAssignment_holds_iff tableau certificateBits
    certificateLengths]
  unfold tableauAssignmentValue
  have afterSymbols :
      ¬ problem.layout.stateVariable time state <
        problem.layout.symbolBlock.endOffset := by
    exact Nat.not_lt_of_ge
      (Nat.le_trans
        (Nat.le_add_right problem.layout.symbolBlock.endOffset
          problem.layout.headBlock.width)
        (VariableBlock.offset_le_index problem.layout.stateBlock
          (problem.layout.stateLocalIndex time state)))
  have afterHeads :
      ¬ problem.layout.stateVariable time state <
        problem.layout.headBlock.endOffset := by
    exact Nat.not_lt_of_ge
      (VariableBlock.offset_le_index problem.layout.stateBlock
        (problem.layout.stateLocalIndex time state))
  have inBlock :
      problem.layout.stateVariable time state <
        problem.layout.stateBlock.endOffset :=
    VariableBlock.index_lt_endOffset problem.layout.stateBlock
      (problem.layout.stateLocalIndex time state)
  have afterSymbols' :
      ¬ (problem.stateCoordinateVariable time state).val <
        problem.layout.symbolBlock.endOffset := afterSymbols
  have afterHeads' :
      ¬ (problem.stateCoordinateVariable time state).val <
        problem.layout.headBlock.endOffset := afterHeads
  have inBlock' :
      (problem.stateCoordinateVariable time state).val <
        problem.layout.stateBlock.endOffset := inBlock
  rw [if_neg afterSymbols', if_neg afterHeads', if_pos inBlock']
  rw [finMembershipValue_eq_true_iff]
  exact problem.activeStateVariables_mem_iff tableau time state

theorem tableauAssignment_certificateBit_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (length : Fin (problem.certificateLimit + 1))
    (index : Fin problem.certificateLimit) :
    (problem.pairedBitLiteral hMode index).Holds
        (problem.tableauAssignment tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode length)) ↔
      certificateBit index = true := by
  change
    (trueLiteral (problem.pairedBitCoordinateVariable hMode index)).Holds
        (problem.tableauAssignment tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode length)) ↔ _
  rw [problem.trueLiteral_tableauAssignment_holds_iff tableau
    (problem.activeCertificateBitVariables hMode certificateBit)
    (problem.activeCertificateLengthVariables hMode length)]
  unfold tableauAssignmentValue
  let bitIndex := problem.pairedCertificateBitIndex hMode index
  have afterSymbols :
      ¬ problem.layout.certificateBitVariable bitIndex <
        problem.layout.symbolBlock.endOffset :=
    Nat.not_lt_of_ge (Nat.le_trans
      problem.layout.symbolEnd_le_certificateBitOffset
      (VariableBlock.offset_le_index
        problem.layout.certificateBitBlock bitIndex))
  have afterHeads :
      ¬ problem.layout.certificateBitVariable bitIndex <
        problem.layout.headBlock.endOffset :=
    Nat.not_lt_of_ge (Nat.le_trans
      problem.layout.headEnd_le_certificateBitOffset
      (VariableBlock.offset_le_index
        problem.layout.certificateBitBlock bitIndex))
  have afterStates :
      ¬ problem.layout.certificateBitVariable bitIndex <
        problem.layout.stateBlock.endOffset :=
    Nat.not_lt_of_ge
      (VariableBlock.offset_le_index
        problem.layout.certificateBitBlock bitIndex)
  have inBlock :
      problem.layout.certificateBitVariable bitIndex <
        problem.layout.certificateBitBlock.endOffset :=
    VariableBlock.index_lt_endOffset
      problem.layout.certificateBitBlock bitIndex
  have afterSymbols' :
      ¬ (problem.pairedBitCoordinateVariable hMode index).val <
        problem.layout.symbolBlock.endOffset := afterSymbols
  have afterHeads' :
      ¬ (problem.pairedBitCoordinateVariable hMode index).val <
        problem.layout.headBlock.endOffset := afterHeads
  have afterStates' :
      ¬ (problem.pairedBitCoordinateVariable hMode index).val <
        problem.layout.stateBlock.endOffset := afterStates
  have inBlock' :
      (problem.pairedBitCoordinateVariable hMode index).val <
        problem.layout.certificateBitBlock.endOffset := inBlock
  rw [if_neg afterSymbols', if_neg afterHeads', if_neg afterStates',
    if_pos inBlock']
  rw [finMembershipValue_eq_true_iff]
  exact problem.activeCertificateBitVariables_mem_iff hMode certificateBit index

theorem tableauAssignment_certificateLength_holds_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected candidate : Fin (problem.certificateLimit + 1)) :
    (problem.pairedLengthLiteral hMode candidate).Holds
        (problem.tableauAssignment tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode selected)) ↔
      selected = candidate := by
  change
    (trueLiteral
      (problem.pairedLengthCoordinateVariable hMode candidate)).Holds
        (problem.tableauAssignment tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode selected)) ↔ _
  rw [problem.trueLiteral_tableauAssignment_holds_iff tableau
    (problem.activeCertificateBitVariables hMode certificateBit)
    (problem.activeCertificateLengthVariables hMode selected)]
  unfold tableauAssignmentValue
  let lengthIndex := problem.pairedCertificateLengthIndex hMode candidate
  have afterSymbols :
      ¬ problem.layout.certificateLengthVariable lengthIndex <
        problem.layout.symbolBlock.endOffset :=
    Nat.not_lt_of_ge (Nat.le_trans
      problem.layout.symbolEnd_le_certificateLengthOffset
      (VariableBlock.offset_le_index
        problem.layout.certificateLengthBlock lengthIndex))
  have afterHeads :
      ¬ problem.layout.certificateLengthVariable lengthIndex <
        problem.layout.headBlock.endOffset :=
    Nat.not_lt_of_ge (Nat.le_trans
      problem.layout.headEnd_le_certificateLengthOffset
      (VariableBlock.offset_le_index
        problem.layout.certificateLengthBlock lengthIndex))
  have afterStates :
      ¬ problem.layout.certificateLengthVariable lengthIndex <
        problem.layout.stateBlock.endOffset :=
    Nat.not_lt_of_ge (Nat.le_trans
      problem.layout.stateEnd_le_certificateLengthOffset
      (VariableBlock.offset_le_index
        problem.layout.certificateLengthBlock lengthIndex))
  have afterBits :
      ¬ problem.layout.certificateLengthVariable lengthIndex <
        problem.layout.certificateBitBlock.endOffset :=
    Nat.not_lt_of_ge
      (VariableBlock.offset_le_index
        problem.layout.certificateLengthBlock lengthIndex)
  have afterSymbols' :
      ¬ (problem.pairedLengthCoordinateVariable hMode candidate).val <
        problem.layout.symbolBlock.endOffset := afterSymbols
  have afterHeads' :
      ¬ (problem.pairedLengthCoordinateVariable hMode candidate).val <
        problem.layout.headBlock.endOffset := afterHeads
  have afterStates' :
      ¬ (problem.pairedLengthCoordinateVariable hMode candidate).val <
        problem.layout.stateBlock.endOffset := afterStates
  have afterBits' :
      ¬ (problem.pairedLengthCoordinateVariable hMode candidate).val <
        problem.layout.certificateBitBlock.endOffset := afterBits
  rw [if_neg afterSymbols', if_neg afterHeads', if_neg afterStates',
    if_neg afterBits']
  rw [finMembershipValue_eq_true_iff]
  exact problem.activeCertificateLengthVariables_mem_iff hMode selected
    candidate

theorem tableauAssignment_certificateBit_negate_holds_iff
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (length : Fin (problem.certificateLimit + 1))
    (index : Fin problem.certificateLimit) :
    (problem.pairedBitLiteral hMode index).negate.Holds
        (problem.tableauAssignment tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode length)) ↔
      certificateBit index = false := by
  let assignment := problem.tableauAssignment tableau
    (problem.activeCertificateBitVariables hMode certificateBit)
    (problem.activeCertificateLengthVariables hMode length)
  have hAssignmentLength : assignment.length = problem.FormulaWidth :=
    problem.tableauAssignment_length tableau
      (problem.activeCertificateBitVariables hMode certificateBit)
      (problem.activeCertificateLengthVariables hMode length)
  constructor
  · intro hNegative
    have hNotPositive := (BoundedLiteral.negate_holds_iff_not
      (problem.pairedBitLiteral hMode index) assignment
      hAssignmentLength).mp hNegative
    cases hBit : certificateBit index with
    | false => rfl
    | true =>
        exact False.elim (hNotPositive
          ((problem.tableauAssignment_certificateBit_holds_iff tableau hMode
            certificateBit length index).mpr hBit))
  · intro hFalse
    apply (BoundedLiteral.negate_holds_iff_not
      (problem.pairedBitLiteral hMode index) assignment
      hAssignmentLength).mpr
    intro hPositive
    have hTrue :=
      (problem.tableauAssignment_certificateBit_holds_iff tableau hMode
        certificateBit length index).mp hPositive
    rw [hFalse] at hTrue
    cases hTrue

theorem tableauAssignment_certificateLengthExactlyOne
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected : Fin (problem.certificateLimit + 1)) :
    ExactlyOneTrue (problem.pairedLengthVariables hMode)
      (problem.tableauAssignment tableau
        (problem.activeCertificateBitVariables hMode certificateBit)
        (problem.activeCertificateLengthVariables hMode selected)) := by
  let assignment := problem.tableauAssignment tableau
    (problem.activeCertificateBitVariables hMode certificateBit)
    (problem.activeCertificateLengthVariables hMode selected)
  let selectedVariable :=
    problem.pairedLengthCoordinateVariable hMode selected
  apply ExactlyOneTrue.of_selected assignment
    (problem.pairedLengthVariables_nodup hMode) selectedVariable
  · apply List.mem_map.mpr
    exact ⟨selected, finiteIndices_mem selected, rfl⟩
  · change (problem.pairedLengthLiteral hMode selected).Holds assignment
    exact (problem.tableauAssignment_certificateLength_holds_iff tableau hMode
      certificateBit selected selected).mpr rfl
  · intro candidateVariable hCandidate hTrue
    rcases List.mem_map.mp hCandidate with ⟨candidate, _, hEqual⟩
    rw [← hEqual] at hTrue
    have selectedEqual :=
      (problem.tableauAssignment_certificateLength_holds_iff tableau hMode
        certificateBit selected candidate).mp hTrue
    rw [← hEqual]
    dsimp [selectedVariable]
    rw [selectedEqual]
    rfl

theorem tableauAssignment_symbolExactlyOne {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (time : Fin problem.dimensions.timeCount)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    ExactlyOneTrue (problem.symbolVariables time position)
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  let selected := problem.symbolCoordinateVariable time position
    ((tableau time).symbol position)
  apply ExactlyOneTrue.of_selected
    (problem.tableauAssignment tableau certificateBits certificateLengths)
    (problem.symbolVariables_nodup time position) selected
  · apply List.mem_map.mpr
    exact ⟨(tableau time).symbol position,
      tapeSymbols_mem ((tableau time).symbol position), rfl⟩
  · change
      (problem.symbolLiteral time position
        ((tableau time).symbol position)).Holds
          (problem.tableauAssignment tableau certificateBits
            certificateLengths)
    exact (problem.tableauAssignment_symbol_holds_iff tableau
      certificateBits certificateLengths time position
      ((tableau time).symbol position)).mpr rfl
  · intro candidate hCandidate hTrue
    rcases List.mem_map.mp hCandidate with ⟨symbol, _, hEqual⟩
    rw [← hEqual] at hTrue
    have hSymbol := (problem.tableauAssignment_symbol_holds_iff tableau
      certificateBits certificateLengths time position symbol).mp hTrue
    rw [← hEqual]
    dsimp [selected]
    rw [hSymbol]
    rfl

theorem tableauAssignment_headExactlyOne {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (time : Fin problem.dimensions.timeCount) :
    ExactlyOneTrue (problem.headVariables time)
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  let selected := problem.headCoordinateVariable time (tableau time).head
  apply ExactlyOneTrue.of_selected
    (problem.tableauAssignment tableau certificateBits certificateLengths)
    (problem.headVariables_nodup time) selected
  · apply List.mem_map.mpr
    exact ⟨(tableau time).head, finiteIndices_mem (tableau time).head, rfl⟩
  · change
      (problem.headLiteral time (tableau time).head).Holds
        (problem.tableauAssignment tableau certificateBits certificateLengths)
    exact (problem.tableauAssignment_head_holds_iff tableau certificateBits
      certificateLengths time (tableau time).head).mpr rfl
  · intro candidate hCandidate hTrue
    rcases List.mem_map.mp hCandidate with ⟨position, _, hEqual⟩
    rw [← hEqual] at hTrue
    have hHead := (problem.tableauAssignment_head_holds_iff tableau
      certificateBits certificateLengths time position).mp hTrue
    rw [← hEqual]
    dsimp [selected]
    rw [hHead]
    rfl

theorem tableauAssignment_stateExactlyOne {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (time : Fin problem.dimensions.timeCount) :
    ExactlyOneTrue (problem.stateVariables time)
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  let selected := problem.stateCoordinateVariable time (tableau time).state
  apply ExactlyOneTrue.of_selected
    (problem.tableauAssignment tableau certificateBits certificateLengths)
    (problem.stateVariables_nodup time) selected
  · apply List.mem_map.mpr
    exact ⟨(tableau time).state, finiteIndices_mem (tableau time).state, rfl⟩
  · change
      (problem.stateLiteral time (tableau time).state).Holds
        (problem.tableauAssignment tableau certificateBits certificateLengths)
    exact (problem.tableauAssignment_state_holds_iff tableau certificateBits
      certificateLengths time (tableau time).state).mpr rfl
  · intro candidate hCandidate hTrue
    rcases List.mem_map.mp hCandidate with ⟨state, _, hEqual⟩
    rw [← hEqual] at hTrue
    have hState := (problem.tableauAssignment_state_holds_iff tableau
      certificateBits certificateLengths time state).mp hTrue
    rw [← hEqual]
    dsimp [selected]
    rw [hState]
    rfl

theorem tableauAssignment_shapeProgram_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth)) :
    LocalProgram.Holds problem.shapeProgram
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  apply LocalProgram.holds_of_all
  intro constraint hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨time, _, hAtTime⟩
  cases List.mem_append.mp hAtTime with
  | inl hSymbolRow =>
      rcases List.mem_map.mp hSymbolRow with ⟨position, _, hEqual⟩
      cases hEqual
      exact problem.tableauAssignment_symbolExactlyOne tableau
        certificateBits certificateLengths time position
  | inr hControlShape =>
      cases List.mem_cons.mp hControlShape with
      | inl hHead =>
          cases hHead
          exact problem.tableauAssignment_headExactlyOne tableau
            certificateBits certificateLengths time
      | inr hStateTail =>
          cases List.mem_cons.mp hStateTail with
          | inl hState =>
              cases hState
              exact problem.tableauAssignment_stateExactlyOne tableau
                certificateBits certificateLengths time
          | inr impossible => cases impossible

theorem tableauAssignment_controlConstraints_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (hTransitions : problem.FiniteTransitions tableau)
    (step : Fin problem.uniformFuel)
    (state : Fin problem.dimensions.stateBound)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (symbol : TapeSymbol) :
    LocalProgram.Holds
      (problem.controlConstraints step state position symbol)
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  let assignment := problem.tableauAssignment tableau certificateBits
    certificateLengths
  let current := tableau (problem.currentTime step)
  let next := tableau (problem.nextTime step)
  let action := problem.localAction state symbol
  have stateImplication :
      LocalConstraint.Holds
        (problem.stateTransitionConstraint step state position symbol)
        assignment := by
    intro premises
    have hState := (problem.tableauAssignment_state_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step) state).mp
        premises.left
    have hHead := (problem.tableauAssignment_head_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      position).mp premises.right.left
    have hSymbol := (problem.tableauAssignment_symbol_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      position symbol).mp premises.right.right.left
    subst state
    subst position
    subst symbol
    apply (problem.tableauAssignment_state_holds_iff tableau certificateBits
      certificateLengths (problem.nextTime step)
      (problem.localAction current.state
        (current.symbol current.head)).targetState).mpr
    exact congrArg FiniteRow.state (hTransitions step)
  have headImplication :
      LocalConstraint.Holds
        (problem.headTransitionConstraint step state position symbol)
        assignment := by
    intro premises
    have hState := (problem.tableauAssignment_state_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step) state).mp
        premises.left
    have hHead := (problem.tableauAssignment_head_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      position).mp premises.right.left
    have hSymbol := (problem.tableauAssignment_symbol_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      position symbol).mp premises.right.right.left
    subst state
    subst position
    subst symbol
    apply (problem.tableauAssignment_head_holds_iff tableau certificateBits
      certificateLengths (problem.nextTime step)
      (movePosition current.head
        (problem.localAction current.state
          (current.symbol current.head)).move)).mpr
    exact congrArg FiniteRow.head (hTransitions step)
  have writeImplication :
      LocalConstraint.Holds
        (problem.writeTransitionConstraint step state position symbol)
        assignment := by
    intro premises
    have hState := (problem.tableauAssignment_state_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step) state).mp
        premises.left
    have hHead := (problem.tableauAssignment_head_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      position).mp premises.right.left
    have hSymbol := (problem.tableauAssignment_symbol_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      position symbol).mp premises.right.right.left
    subst state
    subst position
    subst symbol
    apply (problem.tableauAssignment_symbol_holds_iff tableau certificateBits
      certificateLengths (problem.nextTime step) current.head
      (problem.localAction current.state
        (current.symbol current.head)).writeSymbol).mpr
    calc
      next.symbol current.head = current.next.symbol current.head :=
        congrArg (fun row : problem.FiniteRow => row.symbol current.head)
          (hTransitions step)
      _ = (problem.localAction current.state
          (current.symbol current.head)).writeSymbol :=
        FiniteRow.next_symbol_at_head current
  exact ⟨stateImplication, ⟨headImplication, ⟨writeImplication, True.intro⟩⟩⟩

theorem tableauAssignment_controlTransitionProgram_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (hTransitions : problem.FiniteTransitions tableau) :
    LocalProgram.Holds problem.controlTransitionProgram
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  apply LocalProgram.holds_of_all
  intro constraint hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨step, _, hAtStep⟩
  rcases List.mem_flatMap.mp hAtStep with ⟨position, _, hAtPosition⟩
  rcases List.mem_flatMap.mp hAtPosition with ⟨state, _, hAtState⟩
  rcases List.mem_flatMap.mp hAtState with ⟨symbol, _, hLocal⟩
  exact LocalProgram.holds_of_mem
    (problem.tableauAssignment_controlConstraints_holds tableau
      certificateBits certificateLengths hTransitions step state position
      symbol) hLocal

theorem tableauAssignment_preservationConstraints_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (hTransitions : problem.FiniteTransitions tableau)
    (step : Fin problem.uniformFuel)
    (headPosition otherPosition :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.Holds
      (problem.preservationConstraints step headPosition otherPosition)
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  by_cases hSame : headPosition = otherPosition
  · unfold preservationConstraints
    rw [if_pos hSame]
    exact True.intro
  · unfold preservationConstraints
    rw [if_neg hSame]
    apply LocalProgram.holds_of_all
    intro constraint hConstraint
    rcases List.mem_map.mp hConstraint with ⟨symbol, _, hEqual⟩
    cases hEqual
    intro premises
    have hHead := (problem.tableauAssignment_head_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      headPosition).mp premises.left
    have hSymbol := (problem.tableauAssignment_symbol_holds_iff tableau
      certificateBits certificateLengths (problem.currentTime step)
      otherPosition symbol).mp premises.right.left
    apply (problem.tableauAssignment_symbol_holds_iff tableau certificateBits
      certificateLengths (problem.nextTime step) otherPosition symbol).mpr
    have otherDifferent : otherPosition ≠
        (tableau (problem.currentTime step)).head := by
      intro hEqualHead
      exact hSame (hHead.symm.trans hEqualHead.symm)
    calc
      (tableau (problem.nextTime step)).symbol otherPosition =
          ((tableau (problem.currentTime step)).next).symbol otherPosition :=
        congrArg (fun row : problem.FiniteRow => row.symbol otherPosition)
          (hTransitions step)
      _ = (tableau (problem.currentTime step)).symbol otherPosition :=
        FiniteRow.next_symbol_of_ne
          (tableau (problem.currentTime step)) otherPosition otherDifferent
      _ = symbol := hSymbol

theorem tableauAssignment_preservationProgram_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (hTransitions : problem.FiniteTransitions tableau) :
    LocalProgram.Holds problem.preservationProgram
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  apply LocalProgram.holds_of_all
  intro constraint hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨step, _, hAtStep⟩
  rcases List.mem_flatMap.mp hAtStep with
    ⟨headPosition, _, hAtHead⟩
  rcases List.mem_flatMap.mp hAtHead with
    ⟨otherPosition, _, hLocal⟩
  exact LocalProgram.holds_of_mem
    (problem.tableauAssignment_preservationConstraints_holds tableau
      certificateBits certificateLengths hTransitions step headPosition
      otherPosition) hLocal

theorem tableauAssignment_transitionProgram_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (hTransitions : problem.FiniteTransitions tableau) :
    LocalProgram.Holds problem.transitionProgram
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  apply (LocalProgram.holds_append problem.controlTransitionProgram
    problem.preservationProgram
    (problem.tableauAssignment tableau certificateBits
      certificateLengths)).mpr
  exact ⟨problem.tableauAssignment_controlTransitionProgram_holds tableau
      certificateBits certificateLengths hTransitions,
    problem.tableauAssignment_preservationProgram_holds tableau
      certificateBits certificateLengths hTransitions⟩

theorem tableauAssignment_inputOnlyInitialSymbols_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hInitial : tableau problem.initialTime = problem.inputOnlyInitialRow) :
    LocalProgram.Holds problem.inputOnlyInitialSymbolsProgram
      (problem.tableauAssignment tableau [] []) := by
  apply LocalProgram.holds_of_all
  intro constraint hConstraint
  rcases List.mem_flatMap.mp hConstraint with ⟨position, _, hLocal⟩
  rw [problem.inputOnlyCellProgram_eq position] at hLocal
  cases List.mem_cons.mp hLocal with
  | inl hEqual =>
      cases hEqual
      apply (problem.tableauAssignment_symbol_holds_iff tableau [] []
        problem.initialTime position
        (problem.inputOnlyInitialSymbol position)).mpr
      exact congrArg (fun row : problem.FiniteRow => row.symbol position)
        hInitial
  | inr impossible => cases impossible

theorem tableauAssignment_inputOnlyInitialProgram_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly)
    (hInitial : tableau problem.initialTime = problem.inputOnlyInitialRow) :
    LocalProgram.Holds problem.initialProgram
      (problem.tableauAssignment tableau [] []) := by
  have hState :
      (problem.stateLiteral problem.initialTime problem.startState).Holds
        (problem.tableauAssignment tableau [] []) := by
    apply (problem.tableauAssignment_state_holds_iff tableau [] []
      problem.initialTime problem.startState).mpr
    exact congrArg FiniteRow.state hInitial
  have hHead :
      (problem.headLiteral problem.initialTime
        problem.initialHeadPosition).Holds
        (problem.tableauAssignment tableau [] []) := by
    apply (problem.tableauAssignment_head_holds_iff tableau [] []
      problem.initialTime problem.initialHeadPosition).mpr
    exact congrArg FiniteRow.head hInitial
  have hSymbols : LocalProgram.Holds problem.initialSymbolsProgram
      (problem.tableauAssignment tableau [] []) := by
    unfold initialSymbolsProgram
    split
    next hInputOnly =>
      exact problem.tableauAssignment_inputOnlyInitialSymbols_holds tableau
        hInitial
    next hPaired =>
      have impossible :
          VerifierInputMode.paired = VerifierInputMode.inputOnly :=
        hPaired.symm.trans hVerifierMode
      cases impossible
  exact ⟨hState, ⟨hHead, hSymbols⟩⟩

theorem tableauAssignment_pairedCellProgram_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected candidate : Fin (problem.certificateLimit + 1))
    (hInitial : tableau problem.initialTime =
      problem.pairedInitialRowFor selected certificateBit)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode)) :
    LocalProgram.Holds
      (problem.pairedCellProgram hMode candidate position)
      (problem.tableauAssignment tableau
        (problem.activeCertificateBitVariables hMode certificateBit)
        (problem.activeCertificateLengthVariables hMode selected)) := by
  let assignment := problem.tableauAssignment tableau
    (problem.activeCertificateBitVariables hMode certificateBit)
    (problem.activeCertificateLengthVariables hMode selected)
  unfold pairedCellProgram
  generalize hCell : initialCellAt
    (pairedInitialCells problem.input problem.certificateLimit candidate)
    problem.uniformFuel position.val = cell
  cases cell with
  | blank =>
      refine ⟨?_, True.intro⟩
      intro premises
      have hLength :=
        (problem.tableauAssignment_certificateLength_holds_iff tableau hMode
          certificateBit selected candidate).mp premises.left
      rw [← hLength] at hCell
      apply (problem.tableauAssignment_symbol_holds_iff tableau
        (problem.activeCertificateBitVariables hMode certificateBit)
        (problem.activeCertificateLengthVariables hMode selected)
        problem.initialTime position .blank).mpr
      have rowSymbol := congrArg
        (fun row : problem.FiniteRow => row.symbol position) hInitial
      change (tableau problem.initialTime).symbol position =
        problem.pairedInitialSymbolFor selected certificateBit position
        at rowSymbol
      unfold pairedInitialSymbolFor at rowSymbol
      rw [hCell] at rowSymbol
      exact rowSymbol
  | fixed value =>
      refine ⟨?_, True.intro⟩
      intro premises
      have hLength :=
        (problem.tableauAssignment_certificateLength_holds_iff tableau hMode
          certificateBit selected candidate).mp premises.left
      rw [← hLength] at hCell
      apply (problem.tableauAssignment_symbol_holds_iff tableau
        (problem.activeCertificateBitVariables hMode certificateBit)
        (problem.activeCertificateLengthVariables hMode selected)
        problem.initialTime position (symbolOfFixedBit value)).mpr
      have rowSymbol := congrArg
        (fun row : problem.FiniteRow => row.symbol position) hInitial
      change (tableau problem.initialTime).symbol position =
        problem.pairedInitialSymbolFor selected certificateBit position
        at rowSymbol
      unfold pairedInitialSymbolFor at rowSymbol
      rw [hCell] at rowSymbol
      exact rowSymbol
  | certificate index =>
      refine ⟨?_, ⟨?_, True.intro⟩⟩
      · intro premises
        have hLength :=
          (problem.tableauAssignment_certificateLength_holds_iff tableau hMode
            certificateBit selected candidate).mp premises.left
        have hBit :=
          (problem.tableauAssignment_certificateBit_holds_iff tableau hMode
            certificateBit selected index).mp premises.right.left
        rw [← hLength] at hCell
        apply (problem.tableauAssignment_symbol_holds_iff tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode selected)
          problem.initialTime position .one).mpr
        have rowSymbol := congrArg
          (fun row : problem.FiniteRow => row.symbol position) hInitial
        change (tableau problem.initialTime).symbol position =
          problem.pairedInitialSymbolFor selected certificateBit position
          at rowSymbol
        unfold pairedInitialSymbolFor at rowSymbol
        rw [hCell] at rowSymbol
        simp [initialCellSymbol, hBit] at rowSymbol
        exact rowSymbol
      · intro premises
        have hLength :=
          (problem.tableauAssignment_certificateLength_holds_iff tableau hMode
            certificateBit selected candidate).mp premises.left
        have hBit :=
          (problem.tableauAssignment_certificateBit_negate_holds_iff tableau
            hMode certificateBit selected index).mp premises.right.left
        rw [← hLength] at hCell
        apply (problem.tableauAssignment_symbol_holds_iff tableau
          (problem.activeCertificateBitVariables hMode certificateBit)
          (problem.activeCertificateLengthVariables hMode selected)
          problem.initialTime position .zero).mpr
        have rowSymbol := congrArg
          (fun row : problem.FiniteRow => row.symbol position) hInitial
        change (tableau problem.initialTime).symbol position =
          problem.pairedInitialSymbolFor selected certificateBit position
          at rowSymbol
        unfold pairedInitialSymbolFor at rowSymbol
        rw [hCell] at rowSymbol
        simp [initialCellSymbol, hBit] at rowSymbol
        exact rowSymbol

theorem tableauAssignment_pairedInitialSymbols_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hMode : problem.tableauInputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected : Fin (problem.certificateLimit + 1))
    (hInitial : tableau problem.initialTime =
      problem.pairedInitialRowFor selected certificateBit) :
    LocalProgram.Holds (problem.pairedInitialSymbolsProgram hMode)
      (problem.tableauAssignment tableau
        (problem.activeCertificateBitVariables hMode certificateBit)
        (problem.activeCertificateLengthVariables hMode selected)) := by
  constructor
  · exact problem.tableauAssignment_certificateLengthExactlyOne tableau hMode
      certificateBit selected
  · apply LocalProgram.holds_of_all
    intro constraint hConstraint
    rcases List.mem_flatMap.mp hConstraint with
      ⟨candidate, _, hAtLength⟩
    exact LocalProgram.holds_of_mem
      (LocalProgram.holds_of_all
        (fun cellConstraint hLocal =>
          by
            rcases List.mem_flatMap.mp hLocal with
              ⟨position, _, hAtPosition⟩
            exact LocalProgram.holds_of_mem
              (problem.tableauAssignment_pairedCellProgram_holds tableau hMode
                certificateBit selected candidate hInitial position)
              hAtPosition))
      hAtLength

theorem tableauAssignment_pairedInitialProgram_holds
    {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected : Fin (problem.certificateLimit + 1))
    (hInitial : tableau problem.initialTime =
      problem.pairedInitialRowFor selected certificateBit) :
    LocalProgram.Holds problem.initialProgram
      (problem.tableauAssignment tableau
        (problem.activeCertificateBitVariables
          (problem.tableauInputMode_of_paired hVerifierMode) certificateBit)
        (problem.activeCertificateLengthVariables
          (problem.tableauInputMode_of_paired hVerifierMode) selected)) := by
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  let assignment := problem.tableauAssignment tableau
    (problem.activeCertificateBitVariables hMode certificateBit)
    (problem.activeCertificateLengthVariables hMode selected)
  have hState :
      (problem.stateLiteral problem.initialTime problem.startState).Holds
        assignment := by
    apply (problem.tableauAssignment_state_holds_iff tableau
      (problem.activeCertificateBitVariables hMode certificateBit)
      (problem.activeCertificateLengthVariables hMode selected)
      problem.initialTime problem.startState).mpr
    exact congrArg FiniteRow.state hInitial
  have hHead :
      (problem.headLiteral problem.initialTime
        problem.initialHeadPosition).Holds assignment := by
    apply (problem.tableauAssignment_head_holds_iff tableau
      (problem.activeCertificateBitVariables hMode certificateBit)
      (problem.activeCertificateLengthVariables hMode selected)
      problem.initialTime problem.initialHeadPosition).mpr
    exact congrArg FiniteRow.head hInitial
  have hSymbols : LocalProgram.Holds problem.initialSymbolsProgram
      assignment := by
    unfold initialSymbolsProgram
    split
    next hInputOnly =>
      have impossible :
          VerifierInputMode.inputOnly = VerifierInputMode.paired :=
        hInputOnly.symm.trans hVerifierMode
      cases impossible
    next hPaired =>
      exact problem.tableauAssignment_pairedInitialSymbols_holds tableau hMode
        certificateBit selected hInitial
  exact ⟨hState, ⟨hHead, hSymbols⟩⟩

theorem tableauAssignment_acceptanceProgram_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (certificateBits certificateLengths : List (Fin problem.FormulaWidth))
    (hAccepting : (tableau problem.finalTime).state =
      problem.acceptingState) :
    LocalProgram.Holds problem.acceptanceProgram
      (problem.tableauAssignment tableau certificateBits
        certificateLengths) := by
  exact ⟨(problem.tableauAssignment_state_holds_iff tableau certificateBits
      certificateLengths problem.finalTime problem.acceptingState).mpr
      hAccepting,
    True.intro⟩

theorem finiteAccepting_inputOnly_program_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly)
    (hAccepting : problem.FiniteAcceptingFrom
      problem.inputOnlyInitialRow tableau) :
    LocalProgram.Holds problem.program
      (problem.tableauAssignment tableau [] []) := by
  rcases hAccepting with ⟨hInitial, hTransitions, hFinal⟩
  let assignment := problem.tableauAssignment tableau [] []
  apply (LocalProgram.holds_append
    (problem.shapeProgram ++ problem.initialProgram ++
      problem.transitionProgram)
    problem.acceptanceProgram assignment).mpr
  constructor
  · apply (LocalProgram.holds_append
      (problem.shapeProgram ++ problem.initialProgram)
      problem.transitionProgram assignment).mpr
    constructor
    · apply (LocalProgram.holds_append problem.shapeProgram
        problem.initialProgram assignment).mpr
      exact ⟨problem.tableauAssignment_shapeProgram_holds tableau [] [],
        problem.tableauAssignment_inputOnlyInitialProgram_holds tableau
          hVerifierMode hInitial⟩
    · exact problem.tableauAssignment_transitionProgram_holds tableau [] []
        hTransitions
  · exact problem.tableauAssignment_acceptanceProgram_holds tableau [] []
      hFinal

theorem finiteAccepting_paired_program_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected : Fin (problem.certificateLimit + 1))
    (hAccepting : problem.FiniteAcceptingFrom
      (problem.pairedInitialRowFor selected certificateBit) tableau) :
    LocalProgram.Holds problem.program
      (problem.tableauAssignment tableau
        (problem.activeCertificateBitVariables
          (problem.tableauInputMode_of_paired hVerifierMode) certificateBit)
        (problem.activeCertificateLengthVariables
          (problem.tableauInputMode_of_paired hVerifierMode) selected)) := by
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  let certificateBits :=
    problem.activeCertificateBitVariables hMode certificateBit
  let certificateLengths :=
    problem.activeCertificateLengthVariables hMode selected
  let assignment := problem.tableauAssignment tableau certificateBits
    certificateLengths
  rcases hAccepting with ⟨hInitial, hTransitions, hFinal⟩
  apply (LocalProgram.holds_append
    (problem.shapeProgram ++ problem.initialProgram ++
      problem.transitionProgram)
    problem.acceptanceProgram assignment).mpr
  constructor
  · apply (LocalProgram.holds_append
      (problem.shapeProgram ++ problem.initialProgram)
      problem.transitionProgram assignment).mpr
    constructor
    · apply (LocalProgram.holds_append problem.shapeProgram
        problem.initialProgram assignment).mpr
      exact ⟨problem.tableauAssignment_shapeProgram_holds tableau
          certificateBits certificateLengths,
        problem.tableauAssignment_pairedInitialProgram_holds tableau
          hVerifierMode certificateBit selected hInitial⟩
    · exact problem.tableauAssignment_transitionProgram_holds tableau
        certificateBits certificateLengths hTransitions
  · exact problem.tableauAssignment_acceptanceProgram_holds tableau
      certificateBits certificateLengths hFinal

theorem finiteAccepting_inputOnly_formula_satisfied {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly)
    (hAccepting : problem.FiniteAcceptingFrom
      problem.inputOnlyInitialRow tableau) :
    problem.formula.Satisfied (problem.tableauAssignment tableau [] []) := by
  apply (problem.formula_satisfied_iff
    (problem.tableauAssignment tableau [] [])).mpr
  exact ⟨problem.tableauAssignment_length tableau [] [],
    problem.finiteAccepting_inputOnly_program_holds tableau hVerifierMode
      hAccepting⟩

theorem finiteAccepting_paired_formula_satisfied {language : Language}
    (problem : VerifierTableauProblem language)
    (tableau : problem.FiniteTableau)
    (hVerifierMode : problem.verifier.program.inputMode = .paired)
    (certificateBit : Fin problem.certificateLimit → Bool)
    (selected : Fin (problem.certificateLimit + 1))
    (hAccepting : problem.FiniteAcceptingFrom
      (problem.pairedInitialRowFor selected certificateBit) tableau) :
    problem.formula.Satisfied
      (problem.tableauAssignment tableau
        (problem.activeCertificateBitVariables
          (problem.tableauInputMode_of_paired hVerifierMode) certificateBit)
        (problem.activeCertificateLengthVariables
          (problem.tableauInputMode_of_paired hVerifierMode) selected)) := by
  let hMode := problem.tableauInputMode_of_paired hVerifierMode
  let certificateBits :=
    problem.activeCertificateBitVariables hMode certificateBit
  let certificateLengths :=
    problem.activeCertificateLengthVariables hMode selected
  let assignment := problem.tableauAssignment tableau certificateBits
    certificateLengths
  apply (problem.formula_satisfied_iff assignment).mpr
  exact ⟨problem.tableauAssignment_length tableau certificateBits
      certificateLengths,
    problem.finiteAccepting_paired_program_holds tableau hVerifierMode
      certificateBit selected hAccepting⟩

theorem decodedInitialRow_eq_inputOnly {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly) :
    problem.decodedRow assignment problem.initialTime =
      problem.inputOnlyInitialRow := by
  apply FiniteRow.extensionality
  · exact problem.decodedInitialState assignment hProgram
  · exact problem.decodedInitialHead assignment hProgram
  · intro position
    exact problem.decodedInputOnlyInitialSymbol assignment hProgram
      hVerifierMode position

theorem decodedInitialRow_eq_paired {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hAssignmentLength : assignment.length = problem.FormulaWidth)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    problem.decodedRow assignment problem.initialTime =
      problem.pairedInitialRow assignment hVerifierMode := by
  apply FiniteRow.extensionality
  · exact problem.decodedInitialState assignment hProgram
  · exact problem.decodedInitialHead assignment hProgram
  · intro position
    exact problem.decodedPairedInitialSymbol assignment hAssignmentLength
      hProgram hVerifierMode position

theorem decodedControlPremises_hold {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (step : Fin problem.uniformFuel) :
    BoundedClause.AllHold
      (problem.controlPremises step
        (problem.decodedState assignment (problem.currentTime step))
        (problem.decodedHead assignment (problem.currentTime step))
        (problem.decodedSymbol assignment (problem.currentTime step)
          (problem.decodedHead assignment (problem.currentTime step))))
      assignment := by
  exact
    ⟨problem.decodedState_literal_holds assignment hProgram
        (problem.currentTime step),
      ⟨problem.decodedHead_literal_holds assignment hProgram
          (problem.currentTime step),
        ⟨problem.decodedSymbol_literal_holds assignment hProgram
            (problem.currentTime step)
            (problem.decodedHead assignment (problem.currentTime step)),
          True.intro⟩⟩⟩

theorem decodedState_next {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (step : Fin problem.uniformFuel) :
    problem.decodedState assignment (problem.nextTime step) =
      (problem.localAction
        (problem.decodedState assignment (problem.currentTime step))
        (problem.decodedSymbol assignment (problem.currentTime step)
          (problem.decodedHead assignment
            (problem.currentTime step)))).targetState := by
  let state := problem.decodedState assignment (problem.currentTime step)
  let position := problem.decodedHead assignment (problem.currentTime step)
  let symbol := problem.decodedSymbol assignment
    (problem.currentTime step) position
  have constraintHolds := LocalProgram.holds_of_mem hProgram
    (problem.controlConstraint_mem_program
      (problem.controlConstraint_mem_controlTransitionProgram step state
        position symbol
        (problem.stateTransitionConstraint_mem_controlConstraints step state
          position symbol)))
  have conclusion := constraintHolds
    (problem.decodedControlPremises_hold assignment hProgram step)
  exact (problem.stateLiteral_holds_iff assignment hProgram
    (problem.nextTime step) (problem.localAction state symbol).targetState).mp
      conclusion

theorem decodedHead_next {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (step : Fin problem.uniformFuel) :
    problem.decodedHead assignment (problem.nextTime step) =
      movePosition
        (problem.decodedHead assignment (problem.currentTime step))
        (problem.localAction
          (problem.decodedState assignment (problem.currentTime step))
          (problem.decodedSymbol assignment (problem.currentTime step)
            (problem.decodedHead assignment
              (problem.currentTime step)))).move := by
  let state := problem.decodedState assignment (problem.currentTime step)
  let position := problem.decodedHead assignment (problem.currentTime step)
  let symbol := problem.decodedSymbol assignment
    (problem.currentTime step) position
  have constraintHolds := LocalProgram.holds_of_mem hProgram
    (problem.controlConstraint_mem_program
      (problem.controlConstraint_mem_controlTransitionProgram step state
        position symbol
        (problem.headTransitionConstraint_mem_controlConstraints step state
          position symbol)))
  have conclusion := constraintHolds
    (problem.decodedControlPremises_hold assignment hProgram step)
  exact (problem.headLiteral_holds_iff assignment hProgram
    (problem.nextTime step)
    (movePosition position (problem.localAction state symbol).move)).mp
      conclusion

theorem decodedSymbol_next_at_head {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (step : Fin problem.uniformFuel) :
    problem.decodedSymbol assignment (problem.nextTime step)
        (problem.decodedHead assignment (problem.currentTime step)) =
      (problem.localAction
        (problem.decodedState assignment (problem.currentTime step))
        (problem.decodedSymbol assignment (problem.currentTime step)
          (problem.decodedHead assignment
            (problem.currentTime step)))).writeSymbol := by
  let state := problem.decodedState assignment (problem.currentTime step)
  let position := problem.decodedHead assignment (problem.currentTime step)
  let symbol := problem.decodedSymbol assignment
    (problem.currentTime step) position
  have constraintHolds := LocalProgram.holds_of_mem hProgram
    (problem.controlConstraint_mem_program
      (problem.controlConstraint_mem_controlTransitionProgram step state
        position symbol
        (problem.writeTransitionConstraint_mem_controlConstraints step state
          position symbol)))
  have conclusion := constraintHolds
    (problem.decodedControlPremises_hold assignment hProgram step)
  exact (problem.symbolLiteral_holds_iff assignment hProgram
    (problem.nextTime step) position
    (problem.localAction state symbol).writeSymbol).mp conclusion

theorem decodedSymbol_next_of_ne {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (step : Fin problem.uniformFuel)
    (position :
      Fin (problem.dimensions.tapeWidth problem.tableauInputMode))
    (hDifferent :
      problem.decodedHead assignment (problem.currentTime step) ≠ position) :
    problem.decodedSymbol assignment (problem.nextTime step) position =
      problem.decodedSymbol assignment (problem.currentTime step) position := by
  let headPosition :=
    problem.decodedHead assignment (problem.currentTime step)
  let symbol := problem.decodedSymbol assignment
    (problem.currentTime step) position
  have constraintHolds := LocalProgram.holds_of_mem hProgram
    (problem.preservationConstraint_mem_program step headPosition position
      hDifferent symbol)
  have premises : BoundedClause.AllHold
      [problem.headLiteral (problem.currentTime step) headPosition,
       problem.symbolLiteral (problem.currentTime step) position symbol]
      assignment :=
    ⟨problem.decodedHead_literal_holds assignment hProgram
        (problem.currentTime step),
      ⟨problem.decodedSymbol_literal_holds assignment hProgram
          (problem.currentTime step) position,
        True.intro⟩⟩
  have conclusion := constraintHolds premises
  exact (problem.symbolLiteral_holds_iff assignment hProgram
    (problem.nextTime step) position symbol).mp conclusion

theorem decodedRow_next {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (step : Fin problem.uniformFuel) :
    problem.decodedRow assignment (problem.nextTime step) =
      (problem.decodedRow assignment (problem.currentTime step)).next := by
  apply FiniteRow.extensionality
  · exact problem.decodedState_next assignment hProgram step
  · exact problem.decodedHead_next assignment hProgram step
  · intro position
    by_cases hPosition : position =
        problem.decodedHead assignment (problem.currentTime step)
    · subst position
      exact (problem.decodedSymbol_next_at_head assignment hProgram step).trans
        (FiniteRow.next_symbol_at_head
          (problem.decodedRow assignment (problem.currentTime step))).symm
    · exact (problem.decodedSymbol_next_of_ne assignment hProgram step position
          (Ne.symm hPosition)).trans
        (FiniteRow.next_symbol_of_ne
          (problem.decodedRow assignment (problem.currentTime step))
          position hPosition).symm

theorem decodedTableau_transitions {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment) :
    problem.FiniteTransitions (problem.decodedTableau assignment) := by
  intro step
  exact problem.decodedRow_next assignment hProgram step

theorem program_holds_finiteAccepting_inputOnly {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .inputOnly) :
    problem.FiniteAcceptingFrom problem.inputOnlyInitialRow
      (problem.decodedTableau assignment) := by
  exact ⟨problem.decodedInitialRow_eq_inputOnly assignment hProgram
      hVerifierMode,
    problem.decodedTableau_transitions assignment hProgram,
    problem.decodedFinalAccepting assignment hProgram⟩

theorem program_holds_finiteAccepting_paired {language : Language}
    (problem : VerifierTableauProblem language)
    (assignment : BitString)
    (hAssignmentLength : assignment.length = problem.FormulaWidth)
    (hProgram : LocalProgram.Holds problem.program assignment)
    (hVerifierMode : problem.verifier.program.inputMode = .paired) :
    problem.FiniteAcceptingFrom
      (problem.pairedInitialRow assignment hVerifierMode)
      (problem.decodedTableau assignment) := by
  exact ⟨problem.decodedInitialRow_eq_paired assignment hAssignmentLength
      hProgram hVerifierMode,
    problem.decodedTableau_transitions assignment hProgram,
    problem.decodedFinalAccepting assignment hProgram⟩

/-- Intrinsic finite semantics of the whole formula.  Paired verifiers expose
only finite certificate data; no accepting answer or proof object is supplied
to the formula builder. -/
def HasFiniteAcceptingTableau {language : Language}
    (problem : VerifierTableauProblem language) : Prop :=
  match problem.verifier.program.inputMode with
  | .inputOnly =>
      ∃ tableau, problem.FiniteAcceptingFrom
        problem.inputOnlyInitialRow tableau
  | .paired =>
      ∃ length certificateBit tableau,
        problem.FiniteAcceptingFrom
          (problem.pairedInitialRowFor length certificateBit) tableau

theorem formula_satisfiable_iff_finiteAccepting {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formula.Satisfiable ↔ problem.HasFiniteAcceptingTableau := by
  cases hMode : problem.verifier.program.inputMode with
  | inputOnly =>
      unfold HasFiniteAcceptingTableau
      rw [hMode]
      constructor
      · intro hSatisfiable
        rcases problem.formula_satisfiable_iff.mp hSatisfiable with
          ⟨assignment, _, hProgram⟩
        exact ⟨problem.decodedTableau assignment,
          problem.program_holds_finiteAccepting_inputOnly assignment hProgram
            hMode⟩
      · intro hFinite
        rcases hFinite with ⟨tableau, hAccepting⟩
        exact ⟨problem.tableauAssignment tableau [] [],
          problem.finiteAccepting_inputOnly_formula_satisfied tableau hMode
            hAccepting⟩
  | paired =>
      unfold HasFiniteAcceptingTableau
      rw [hMode]
      constructor
      · intro hSatisfiable
        rcases problem.formula_satisfiable_iff.mp hSatisfiable with
          ⟨assignment, hAssignmentLength, hProgram⟩
        exact
          ⟨problem.decodedCertificateLength assignment hMode,
            problem.decodedCertificateBit assignment hMode,
            problem.decodedTableau assignment,
            problem.program_holds_finiteAccepting_paired assignment
              hAssignmentLength hProgram hMode⟩
      · intro hFinite
        rcases hFinite with
          ⟨selected, certificateBit, tableau, hAccepting⟩
        exact
          ⟨problem.tableauAssignment tableau
              (problem.activeCertificateBitVariables
                (problem.tableauInputMode_of_paired hMode) certificateBit)
              (problem.activeCertificateLengthVariables
                (problem.tableauInputMode_of_paired hMode) selected),
            problem.finiteAccepting_paired_formula_satisfied tableau hMode
              certificateBit selected hAccepting⟩

theorem encodedFormula_mem_CNFSAT_iff_finiteAccepting
    {language : Language}
    (problem : VerifierTableauProblem language) :
    CNFSAT problem.encodedFormula ↔ problem.HasFiniteAcceptingTableau := by
  rw [problem.encodedFormula_mem_CNFSAT_iff]
  exact problem.formula_satisfiable_iff_finiteAccepting

end VerifierTableauProblem

end CookLevin

end PNP.Concrete
