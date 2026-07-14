/-
Copyright (c) 2026 PNP Labs.

Finite dimensions, collision-free Boolean-variable namespaces, elementary CNF
combinators, and fuel-padding lemmas for the concrete Cook--Levin route.

This file does not construct a tableau formula or a reduction.  It fixes the
numeric layout that later files must use and proves that extending a fuel
budget after a halted or stuck endpoint cannot change the raw execution.
-/

import PNP.Concrete.CNF
import PNP.Concrete.WorkMachine

namespace PNP.Concrete

namespace CookLevin

/-! ### Stable raw runs and fuel padding -/

/-- Constructive subtraction-free decomposition of a natural inequality. -/
theorem exists_add_of_le {small large : Nat} (hLe : small ≤ large) :
    ∃ rest, large = small + rest := by
  induction hLe with
  | refl => exact ⟨0, rfl⟩
  | @step next hPrevious ih =>
      rcases ih with ⟨rest, hRest⟩
      refine ⟨rest + 1, ?_⟩
      rw [hRest]
      rfl

/-- Once the smaller run is halted, every larger fuel budget has the same
endpoint. -/
theorem run_pad_of_halted (machine : Machine) (config : Configuration)
    {small large : Nat} (hLe : small ≤ large)
    (hHalted : machine.isHalted (run machine small config) = true) :
    run machine large config = run machine small config := by
  rcases exists_add_of_le hLe with ⟨rest, hLarge⟩
  rw [hLarge, run_add]
  exact run_eq_self_of_isHalted machine (run machine small config) rest hHalted

/-- A stuck nonhalting endpoint is also stable under every larger fuel
budget.  This is deliberately separate from halting: a stuck endpoint remains
a timeout rather than being reclassified as rejection. -/
theorem run_pad_of_stuck (machine : Machine) (config : Configuration)
    {small large : Nat} (hLe : small ≤ large)
    (hStuck : step? machine (run machine small config) = none) :
    run machine large config = run machine small config := by
  rcases exists_add_of_le hLe with ⟨rest, hLarge⟩
  rw [hLarge, run_add]
  exact run_eq_self_of_step?_eq_none machine (run machine small config) rest hStuck

/-- Padding a bounded decision after a designated halt preserves the exact
verdict. -/
theorem boundedDecide_pad_of_halted (machine : Machine) (input : BitString)
    {small large : Nat} (hLe : small ≤ large)
    (hHalted : machine.isHalted
      (run machine small (startConfig machine input)) = true) :
    boundedDecide machine large input = boundedDecide machine small input := by
  unfold boundedDecide
  rw [run_pad_of_halted machine (startConfig machine input) hLe hHalted]

/-- Padding after a stuck endpoint preserves the exact timeout verdict. -/
theorem boundedDecide_pad_of_stuck (machine : Machine) (input : BitString)
    {small large : Nat} (hLe : small ≤ large)
    (hStuck : step? machine
      (run machine small (startConfig machine input)) = none) :
    boundedDecide machine large input = boundedDecide machine small input := by
  unfold boundedDecide
  rw [run_pad_of_stuck machine (startConfig machine input) hLe hStuck]

/-! ### Finite state and space dimensions -/

/-- Maximum state mentioned by a single transition, before adding the strict
upper-bound successor. -/
def ruleStateCeiling (rule : Rule) : Nat :=
  Nat.max rule.sourceState rule.targetState

/-- Maximum state mentioned by a finite rule table. -/
def rulesStateCeiling : List Rule → Nat
  | [] => 0
  | rule :: rest => Nat.max (ruleStateCeiling rule) (rulesStateCeiling rest)

/-- One strict upper bound covering the complete rule table and all three
distinguished states. -/
def machineStateBound (machine : Machine) : Nat :=
  Nat.succ (Nat.max machine.startState
    (Nat.max machine.acceptState
      (Nat.max machine.rejectState (rulesStateCeiling machine.rules))))

/-- Constructive left injection into `Nat.max`, avoiding simplifier-oriented
library dependencies in the audited state-bound closure. -/
theorem le_max_left_constructive (left right : Nat) :
    left ≤ Nat.max left right := by
  change left ≤ max left right
  rw [Nat.max_def]
  by_cases hLe : left ≤ right
  · rw [if_pos hLe]
    exact hLe
  · rw [if_neg hLe]
    exact Nat.le_refl left

/-- Constructive right injection into `Nat.max`. -/
theorem le_max_right_constructive (left right : Nat) :
    right ≤ Nat.max left right := by
  change right ≤ max left right
  rw [Nat.max_def]
  by_cases hLe : left ≤ right
  · rw [if_pos hLe]
    exact Nat.le_refl right
  · rw [if_neg hLe]
    exact Nat.le_of_lt (Nat.lt_of_not_ge hLe)

theorem rule_source_le_ruleStateCeiling (rule : Rule) :
    rule.sourceState ≤ ruleStateCeiling rule :=
  le_max_left_constructive _ _

theorem rule_target_le_ruleStateCeiling (rule : Rule) :
    rule.targetState ≤ ruleStateCeiling rule :=
  le_max_right_constructive _ _

theorem ruleStateCeiling_le_rulesStateCeiling {rule : Rule}
    {rules : List Rule} (hMem : rule ∈ rules) :
    ruleStateCeiling rule ≤ rulesStateCeiling rules := by
  induction rules with
  | nil => cases hMem
  | cons first rest ih =>
      cases hMem with
      | head => exact le_max_left_constructive _ _
      | tail _ hTail =>
          exact Nat.le_trans (ih hTail) (le_max_right_constructive _ _)

theorem machine_startState_lt_bound (machine : Machine) :
    machine.startState < machineStateBound machine := by
  apply Nat.lt_succ_of_le
  exact le_max_left_constructive _ _

theorem machine_acceptState_lt_bound (machine : Machine) :
    machine.acceptState < machineStateBound machine := by
  apply Nat.lt_succ_of_le
  exact Nat.le_trans (le_max_left_constructive _ _)
    (le_max_right_constructive _ _)

theorem machine_rejectState_lt_bound (machine : Machine) :
    machine.rejectState < machineStateBound machine := by
  apply Nat.lt_succ_of_le
  exact Nat.le_trans
    (Nat.le_trans (le_max_left_constructive _ _)
      (le_max_right_constructive _ _))
    (le_max_right_constructive _ _)

theorem rule_source_lt_machineStateBound (machine : Machine) (rule : Rule)
    (hMem : rule ∈ machine.rules) :
    rule.sourceState < machineStateBound machine := by
  apply Nat.lt_succ_of_le
  exact Nat.le_trans
    (Nat.le_trans (rule_source_le_ruleStateCeiling rule)
      (ruleStateCeiling_le_rulesStateCeiling hMem))
    (Nat.le_trans (le_max_right_constructive _ _) (Nat.le_trans
      (le_max_right_constructive _ _) (le_max_right_constructive _ _)))

theorem rule_target_lt_machineStateBound (machine : Machine) (rule : Rule)
    (hMem : rule ∈ machine.rules) :
    rule.targetState < machineStateBound machine := by
  apply Nat.lt_succ_of_le
  exact Nat.le_trans
    (Nat.le_trans (rule_target_le_ruleStateCeiling rule)
      (ruleStateCeiling_le_rulesStateCeiling hMem))
    (Nat.le_trans (le_max_right_constructive _ _) (Nat.le_trans
      (le_max_right_constructive _ _) (le_max_right_constructive _ _)))

/-- Whether the simulated verifier receives the source string directly or a
canonical pair of source string and certificate. -/
inductive InputMode where
  | inputOnly
  | paired
deriving BEq, DecidableEq, Repr

/-- Concrete numeric dimensions for one bounded tableau. -/
structure Dimensions where
  inputLength : Nat
  certificateBound : Nat
  timeBound : Nat
  stateBound : Nat
deriving DecidableEq, Repr

namespace Dimensions

/-- Maximum raw verifier-input length.  Pair framing contributes two copies
of each payload length and one delimiter per frame. -/
def encodedInputLength (dimensions : Dimensions) : InputMode → Nat
  | .inputOnly => dimensions.inputLength
  | .paired =>
      2 * dimensions.inputLength + 2 * dimensions.certificateBound + 2

/-- Number of represented time instants, including time zero. -/
def timeCount (dimensions : Dimensions) : Nat := dimensions.timeBound + 1

/-- A head moving at most once per transition remains inside this symmetric
window around the encoded input. -/
def tapeWidth (dimensions : Dimensions) (mode : InputMode) : Nat :=
  dimensions.encodedInputLength mode + 2 * dimensions.timeBound + 1

theorem timeCount_positive (dimensions : Dimensions) :
    0 < dimensions.timeCount := by
  exact Nat.zero_lt_succ dimensions.timeBound

theorem tapeWidth_positive (dimensions : Dimensions) (mode : InputMode) :
    0 < dimensions.tapeWidth mode := by
  unfold tapeWidth
  exact Nat.zero_lt_succ
    (dimensions.encodedInputLength mode + 2 * dimensions.timeBound)

end Dimensions

/-- Polynomial syntax for the maximum encoded verifier input. -/
def encodedInputPolynomial (mode : InputMode)
    (certificateBound : NatPolynomial) : NatPolynomial :=
  match mode with
  | .inputOnly => .variable
  | .paired =>
      .add
        (.add (.mul (.constant 2) .variable)
          (.mul (.constant 2) certificateBound))
        (.constant 2)

/-- Polynomial syntax for the complete tape window. -/
def tapeWidthPolynomial (mode : InputMode)
    (certificateBound runtimeBound : NatPolynomial) : NatPolynomial :=
  .add
    (.add (encodedInputPolynomial mode certificateBound)
      (.mul (.constant 2) runtimeBound))
    (.constant 1)

theorem eval_encodedInputPolynomial (mode : InputMode)
    (certificateBound : NatPolynomial) (inputLength : Nat) :
    NatPolynomial.eval (encodedInputPolynomial mode certificateBound) inputLength =
      (match mode with
       | .inputOnly => inputLength
       | .paired =>
           2 * inputLength +
             2 * NatPolynomial.eval certificateBound inputLength + 2) := by
  cases mode <;> rfl

theorem eval_tapeWidthPolynomial (mode : InputMode)
    (certificateBound runtimeBound : NatPolynomial) (inputLength : Nat) :
    NatPolynomial.eval
        (tapeWidthPolynomial mode certificateBound runtimeBound) inputLength =
      NatPolynomial.eval
          (encodedInputPolynomial mode certificateBound) inputLength +
        2 * NatPolynomial.eval runtimeBound inputLength + 1 := by
  rfl

/-- Instantiate all tableau dimensions from the two explicit polynomial
bounds and one fixed raw machine. -/
def dimensionsAt (machine : Machine) (mode : InputMode)
    (certificateBound runtimeBound : NatPolynomial)
    (inputLength : Nat) : Dimensions :=
  { inputLength := inputLength
    certificateBound := certificateBound.eval inputLength
    timeBound := runtimeBound.eval
      ((encodedInputPolynomial mode certificateBound).eval inputLength)
    stateBound := machineStateBound machine }

/-! ### Collision-free Boolean-variable blocks -/

/-- One contiguous half-open block of zero-based Boolean variable indices. -/
structure VariableBlock where
  offset : Nat
  width : Nat
deriving DecidableEq, Repr

namespace VariableBlock

def endOffset (block : VariableBlock) : Nat := block.offset + block.width

def index (block : VariableBlock) (coordinate : Fin block.width) : Nat :=
  block.offset + coordinate.val

theorem offset_le_index (block : VariableBlock)
    (coordinate : Fin block.width) :
    block.offset ≤ block.index coordinate :=
  Nat.le_add_right _ _

theorem index_lt_endOffset (block : VariableBlock)
    (coordinate : Fin block.width) :
    block.index coordinate < block.endOffset := by
  exact Nat.add_lt_add_left coordinate.isLt block.offset

/-- Ordered half-open blocks have disjoint variable images. -/
theorem index_ne_of_end_le_offset (left right : VariableBlock)
    (hBefore : left.endOffset ≤ right.offset)
    (leftLocal : Fin left.width) (rightLocal : Fin right.width) :
    left.index leftLocal ≠ right.index rightLocal := by
  intro hEqual
  have hLeft : left.index leftLocal < right.offset :=
    Nat.lt_of_lt_of_le (index_lt_endOffset left leftLocal) hBefore
  have hRight : right.offset ≤ left.index leftLocal := by
    rw [hEqual]
    exact offset_le_index right rightLocal
  exact (Nat.not_lt_of_ge hRight) hLeft

end VariableBlock

/-- Complete contiguous allocation for a bounded verifier tableau. -/
structure VariableLayout where
  dimensions : Dimensions
  mode : InputMode
deriving DecidableEq, Repr

namespace VariableLayout

def symbolWidth (layout : VariableLayout) : Nat :=
  layout.dimensions.timeCount * layout.dimensions.tapeWidth layout.mode * 3

def headWidth (layout : VariableLayout) : Nat :=
  layout.dimensions.timeCount * layout.dimensions.tapeWidth layout.mode

def stateWidth (layout : VariableLayout) : Nat :=
  layout.dimensions.timeCount * layout.dimensions.stateBound

def certificateBitWidth (layout : VariableLayout) : Nat :=
  match layout.mode with
  | .inputOnly => 0
  | .paired => layout.dimensions.certificateBound

def certificateLengthWidth (layout : VariableLayout) : Nat :=
  match layout.mode with
  | .inputOnly => 0
  | .paired => layout.dimensions.certificateBound + 1

def symbolBlock (layout : VariableLayout) : VariableBlock :=
  { offset := 0, width := layout.symbolWidth }

def headBlock (layout : VariableLayout) : VariableBlock :=
  { offset := layout.symbolBlock.endOffset, width := layout.headWidth }

def stateBlock (layout : VariableLayout) : VariableBlock :=
  { offset := layout.headBlock.endOffset, width := layout.stateWidth }

def certificateBitBlock (layout : VariableLayout) : VariableBlock :=
  { offset := layout.stateBlock.endOffset,
    width := layout.certificateBitWidth }

def certificateLengthBlock (layout : VariableLayout) : VariableBlock :=
  { offset := layout.certificateBitBlock.endOffset,
    width := layout.certificateLengthWidth }

def variableCount (layout : VariableLayout) : Nat :=
  layout.certificateLengthBlock.endOffset

/-- Row-major flattening of a bounded rectangular coordinate. -/
def flattenTwo (outer inner innerCount : Nat) : Nat :=
  outer * innerCount + inner

theorem flattenTwo_lt {outer inner outerCount innerCount : Nat}
    (hOuter : outer < outerCount) (hInner : inner < innerCount) :
    flattenTwo outer inner innerCount < outerCount * innerCount := by
  have hWithinRow : outer * innerCount + inner <
      outer * innerCount + innerCount :=
    Nat.add_lt_add_left hInner (outer * innerCount)
  have hNextRow : outer * innerCount + innerCount =
      (outer + 1) * innerCount := by
    exact (Nat.succ_mul outer innerCount).symm
  have hRows : (outer + 1) * innerCount ≤ outerCount * innerCount :=
    Nat.mul_le_mul_right innerCount
      ((Nat.succ_le_iff).mpr hOuter)
  rw [hNextRow] at hWithinRow
  exact Nat.lt_of_lt_of_le hWithinRow hRows

/-- Fixed code for the three raw tape symbols. -/
def tapeSymbolCode : TapeSymbol → Nat
  | .blank => 0
  | .zero => 1
  | .one => 2

theorem tapeSymbolCode_lt_three (symbol : TapeSymbol) :
    tapeSymbolCode symbol < 3 := by
  cases symbol <;> decide

def symbolLocalIndex (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode))
    (symbol : TapeSymbol) : Fin layout.symbolWidth :=
  ⟨flattenTwo
      (flattenTwo time.val position.val
        (layout.dimensions.tapeWidth layout.mode))
      (tapeSymbolCode symbol) 3,
    flattenTwo_lt
      (flattenTwo_lt time.isLt position.isLt)
      (tapeSymbolCode_lt_three symbol)⟩

def headLocalIndex (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode)) :
    Fin layout.headWidth :=
  ⟨flattenTwo time.val position.val
      (layout.dimensions.tapeWidth layout.mode),
    flattenTwo_lt time.isLt position.isLt⟩

def stateLocalIndex (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (state : Fin layout.dimensions.stateBound) : Fin layout.stateWidth :=
  ⟨flattenTwo time.val state.val layout.dimensions.stateBound,
    flattenTwo_lt time.isLt state.isLt⟩

def symbolVariable (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode))
    (symbol : TapeSymbol) : Nat :=
  layout.symbolBlock.index (layout.symbolLocalIndex time position symbol)

def headVariable (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode)) : Nat :=
  layout.headBlock.index (layout.headLocalIndex time position)

def stateVariable (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (state : Fin layout.dimensions.stateBound) : Nat :=
  layout.stateBlock.index (layout.stateLocalIndex time state)

def certificateBitVariable (layout : VariableLayout)
    (index : Fin layout.certificateBitWidth) : Nat :=
  layout.certificateBitBlock.index index

def certificateLengthVariable (layout : VariableLayout)
    (length : Fin layout.certificateLengthWidth) : Nat :=
  layout.certificateLengthBlock.index length

theorem symbolBlock_before_headBlock (layout : VariableLayout) :
    layout.symbolBlock.endOffset ≤ layout.headBlock.offset :=
  Nat.le_refl _

theorem headBlock_before_stateBlock (layout : VariableLayout) :
    layout.headBlock.endOffset ≤ layout.stateBlock.offset :=
  Nat.le_refl _

theorem stateBlock_before_certificateBitBlock (layout : VariableLayout) :
    layout.stateBlock.endOffset ≤ layout.certificateBitBlock.offset :=
  Nat.le_refl _

theorem certificateBitBlock_before_certificateLengthBlock
    (layout : VariableLayout) :
    layout.certificateBitBlock.endOffset ≤
      layout.certificateLengthBlock.offset :=
  Nat.le_refl _

theorem symbolVariable_ne_headVariable (layout : VariableLayout)
    (time₁ : Fin layout.dimensions.timeCount)
    (position₁ : Fin (layout.dimensions.tapeWidth layout.mode))
    (symbol : TapeSymbol)
    (time₂ : Fin layout.dimensions.timeCount)
    (position₂ : Fin (layout.dimensions.tapeWidth layout.mode)) :
    layout.symbolVariable time₁ position₁ symbol ≠
      layout.headVariable time₂ position₂ :=
  VariableBlock.index_ne_of_end_le_offset
    layout.symbolBlock layout.headBlock
    (symbolBlock_before_headBlock layout)
    (layout.symbolLocalIndex time₁ position₁ symbol)
    (layout.headLocalIndex time₂ position₂)

theorem headVariable_ne_stateVariable (layout : VariableLayout)
    (time₁ : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode))
    (time₂ : Fin layout.dimensions.timeCount)
    (state : Fin layout.dimensions.stateBound) :
    layout.headVariable time₁ position ≠ layout.stateVariable time₂ state :=
  VariableBlock.index_ne_of_end_le_offset
    layout.headBlock layout.stateBlock
    (headBlock_before_stateBlock layout)
    (layout.headLocalIndex time₁ position)
    (layout.stateLocalIndex time₂ state)

theorem stateVariable_ne_certificateBitVariable (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (state : Fin layout.dimensions.stateBound)
    (index : Fin layout.certificateBitWidth) :
    layout.stateVariable time state ≠ layout.certificateBitVariable index :=
  VariableBlock.index_ne_of_end_le_offset
    layout.stateBlock layout.certificateBitBlock
    (stateBlock_before_certificateBitBlock layout)
    (layout.stateLocalIndex time state) index

theorem certificateBitVariable_ne_certificateLengthVariable
    (layout : VariableLayout)
    (index : Fin layout.certificateBitWidth)
    (length : Fin layout.certificateLengthWidth) :
    layout.certificateBitVariable index ≠
      layout.certificateLengthVariable length :=
  VariableBlock.index_ne_of_end_le_offset
    layout.certificateBitBlock layout.certificateLengthBlock
    (certificateBitBlock_before_certificateLengthBlock layout)
    index length

theorem symbolVariable_lt_variableCount (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode))
    (symbol : TapeSymbol) :
    layout.symbolVariable time position symbol < layout.variableCount := by
  exact Nat.lt_of_lt_of_le
    (VariableBlock.index_lt_endOffset layout.symbolBlock
      (layout.symbolLocalIndex time position symbol))
    (Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_trans (Nat.le_add_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))

theorem headVariable_lt_variableCount (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (position : Fin (layout.dimensions.tapeWidth layout.mode)) :
    layout.headVariable time position < layout.variableCount := by
  exact Nat.lt_of_lt_of_le
    (VariableBlock.index_lt_endOffset layout.headBlock
      (layout.headLocalIndex time position))
    (Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))

theorem stateVariable_lt_variableCount (layout : VariableLayout)
    (time : Fin layout.dimensions.timeCount)
    (state : Fin layout.dimensions.stateBound) :
    layout.stateVariable time state < layout.variableCount := by
  exact Nat.lt_of_lt_of_le
    (VariableBlock.index_lt_endOffset layout.stateBlock
      (layout.stateLocalIndex time state))
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem certificateBitVariable_lt_variableCount (layout : VariableLayout)
    (index : Fin layout.certificateBitWidth) :
    layout.certificateBitVariable index < layout.variableCount := by
  exact Nat.lt_of_lt_of_le
    (VariableBlock.index_lt_endOffset layout.certificateBitBlock index)
    (Nat.le_add_right _ _)

theorem certificateLengthVariable_lt_variableCount (layout : VariableLayout)
    (length : Fin layout.certificateLengthWidth) :
    layout.certificateLengthVariable length < layout.variableCount :=
  VariableBlock.index_lt_endOffset layout.certificateLengthBlock length

end VariableLayout

/-! ### Elementary CNF clause combinators -/

def positiveLiteral (variableIndex : Nat) : CNFLiteral :=
  { positive := true, variableIndex := variableIndex }

def negativeLiteral (variableIndex : Nat) : CNFLiteral :=
  { positive := false, variableIndex := variableIndex }

def atLeastOneClause (variables : List Nat) : List CNFLiteral :=
  variables.map positiveLiteral

def excludePairClause (left right : Nat) : List CNFLiteral :=
  [negativeLiteral left, negativeLiteral right]

def excludeWithClauses (first : Nat) : List Nat → List (List CNFLiteral)
  | [] => []
  | next :: rest => excludePairClause first next :: excludeWithClauses first rest

def atMostOneClauses : List Nat → List (List CNFLiteral)
  | [] => []
  | first :: rest => excludeWithClauses first rest ++ atMostOneClauses rest

def exactlyOneClauses (variables : List Nat) : List (List CNFLiteral) :=
  atLeastOneClause variables :: atMostOneClauses variables

theorem literalSatisfied_positiveLiteral_iff (variableIndex : Nat)
    (assignment : BitString) :
    LiteralSatisfied (positiveLiteral variableIndex) assignment ↔
      assignmentAt assignment variableIndex = some true := by
  exact Iff.rfl

theorem literalSatisfied_negativeLiteral_iff (variableIndex : Nat)
    (assignment : BitString) :
    LiteralSatisfied (negativeLiteral variableIndex) assignment ↔
      assignmentAt assignment variableIndex = some false := by
  exact Iff.rfl

theorem atLeastOneClause_satisfied_iff (variables : List Nat)
    (assignment : BitString) :
    ClauseSatisfied (atLeastOneClause variables) assignment ↔
      ∃ variableIndex, variableIndex ∈ variables ∧
        assignmentAt assignment variableIndex = some true := by
  induction variables with
  | nil =>
      constructor
      · intro impossible
        exact False.elim impossible
      · intro witness
        rcases witness with ⟨variableIndex, hMem, _⟩
        cases hMem
  | cons first rest ih =>
      change
        (LiteralSatisfied (positiveLiteral first) assignment ∨
          ClauseSatisfied (atLeastOneClause rest) assignment) ↔
        ∃ variableIndex, variableIndex ∈ first :: rest ∧
          assignmentAt assignment variableIndex = some true
      constructor
      · intro satisfied
        cases satisfied with
        | inl hFirst =>
            exact ⟨first, List.Mem.head rest,
              (literalSatisfied_positiveLiteral_iff first assignment).mp hFirst⟩
        | inr hRest =>
            rcases ih.mp hRest with ⟨variableIndex, hMem, hValue⟩
            exact ⟨variableIndex, List.Mem.tail first hMem, hValue⟩
      · intro witness
        rcases witness with ⟨variableIndex, hMem, hValue⟩
        cases hMem with
        | head =>
            exact Or.inl
              ((literalSatisfied_positiveLiteral_iff first assignment).mpr hValue)
        | tail _ hTail =>
            exact Or.inr (ih.mpr ⟨variableIndex, hTail, hValue⟩)

theorem excludePairClause_satisfied_of_left_false (left right : Nat)
    (assignment : BitString)
    (hLeft : assignmentAt assignment left = some false) :
    ClauseSatisfied (excludePairClause left right) assignment := by
  exact Or.inl
    ((literalSatisfied_negativeLiteral_iff left assignment).mpr hLeft)

theorem excludePairClause_satisfied_of_right_false (left right : Nat)
    (assignment : BitString)
    (hRight : assignmentAt assignment right = some false) :
    ClauseSatisfied (excludePairClause left right) assignment := by
  exact Or.inr (Or.inl
    ((literalSatisfied_negativeLiteral_iff right assignment).mpr hRight))

theorem excludePairClause_not_satisfied_of_both_true (left right : Nat)
    (assignment : BitString)
    (hLeft : assignmentAt assignment left = some true)
    (hRight : assignmentAt assignment right = some true) :
    ¬ ClauseSatisfied (excludePairClause left right) assignment := by
  intro satisfied
  cases satisfied with
  | inl leftFalse =>
      have hFalse :=
        (literalSatisfied_negativeLiteral_iff left assignment).mp leftFalse
      rw [hLeft] at hFalse
      exact Bool.noConfusion (Option.some.inj hFalse)
  | inr tail =>
      cases tail with
      | inl rightFalse =>
          have hFalse :=
            (literalSatisfied_negativeLiteral_iff right assignment).mp rightFalse
          rw [hRight] at hFalse
          exact Bool.noConfusion (Option.some.inj hFalse)
      | inr impossible => exact False.elim impossible

end CookLevin

end PNP.Concrete
