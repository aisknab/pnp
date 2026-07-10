/-
Copyright (c) 2026 PNP Labs.

Finite truth-table semantics for exact-width direct-wire NAND candidates.
Every input tuple and output position is checked explicitly; no function-space
enumeration or nonconstructive extensionality is used.
-/

import PNP.NANDEnumerator

namespace PNP
namespace DirectWire

/-- A recursively typed Boolean tuple. -/
inductive BoolTuple : Nat → Type where
  | nil : BoolTuple 0
  | cons {width : Nat} : Bool → BoolTuple width → BoolTuple (width + 1)

/-- Pointwise lookup in a Boolean tuple. -/
def BoolTuple.get {width : Nat} (tuple : BoolTuple width) : Fin width → Bool :=
  match tuple with
  | .nil => fun index => False.elim (Nat.not_lt_zero index.val index.isLt)
  | .cons head tail => fun index =>
      match index with
      | ⟨0, _⟩ => head
      | ⟨position + 1, isLt⟩ =>
          tail.get ⟨position, Nat.lt_of_succ_lt_succ isLt⟩

/-- Interpret a Boolean tuple as a finite valuation. -/
def BoolTuple.toValuation {width : Nat} (tuple : BoolTuple width) :
    Valuation width :=
  tuple.get

@[simp] theorem BoolTuple.get_cons_zero {width : Nat}
    (head : Bool) (tail : BoolTuple width) :
    (BoolTuple.cons head tail).get ⟨0, Nat.zero_lt_succ width⟩ = head := rfl

@[simp] theorem BoolTuple.get_cons_succ {width : Nat}
    (head : Bool) (tail : BoolTuple width) (index : Fin width) :
    (BoolTuple.cons head tail).get index.succ = tail.get index := by
  cases index
  rfl

/-- Reify a finite valuation as a recursively typed tuple. -/
def BoolTuple.ofFn : {width : Nat} → Valuation width → BoolTuple width
  | 0, _ => .nil
  | width + 1, valuation =>
      .cons (valuation ⟨0, Nat.zero_lt_succ width⟩)
        (BoolTuple.ofFn fun index => valuation index.succ)

/-- Pointwise-equal valuations reify to the same recursive tuple. -/
theorem BoolTuple.ofFn_congr {width : Nat}
    {left right : Valuation width}
    (pointwise : ∀ index, left index = right index) :
    BoolTuple.ofFn left = BoolTuple.ofFn right := by
  induction width with
  | zero => rfl
  | succ width ih =>
      change BoolTuple.cons (left ⟨0, Nat.zero_lt_succ width⟩)
          (BoolTuple.ofFn fun index => left index.succ) =
        BoolTuple.cons (right ⟨0, Nat.zero_lt_succ width⟩)
          (BoolTuple.ofFn fun index => right index.succ)
      rw [pointwise ⟨0, Nat.zero_lt_succ width⟩]
      rw [ih (fun index => pointwise index.succ)]

/-- Reification followed by interpretation preserves every point. -/
theorem BoolTuple.toValuation_ofFn {width : Nat}
    (valuation : Valuation width) (index : Fin width) :
    (BoolTuple.ofFn valuation).toValuation index = valuation index := by
  induction width with
  | zero => exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | succ width ih =>
      cases index with
      | mk position isLt =>
          cases position with
          | zero => rfl
          | succ earlier =>
              exact ih (fun index => valuation index.succ)
                ⟨earlier, Nat.lt_of_succ_lt_succ isLt⟩

/-- Interpretation followed by reification recovers the recursive tuple. -/
theorem BoolTuple.ofFn_toValuation {width : Nat} (tuple : BoolTuple width) :
    BoolTuple.ofFn tuple.toValuation = tuple := by
  induction tuple with
  | nil => rfl
  | cons head tail ih =>
      change BoolTuple.cons head
        (BoolTuple.ofFn fun index => (BoolTuple.cons head tail).get index.succ) =
          BoolTuple.cons head tail
      apply congrArg (BoolTuple.cons head)
      exact (BoolTuple.ofFn_congr
        (fun index => BoolTuple.get_cons_succ head tail index)).trans ih

/-- Every Boolean tuple of exactly `width`, in recursive binary order. -/
def allBoolTuples : (width : Nat) → List (BoolTuple width)
  | 0 => [.nil]
  | width + 1 =>
      (allBoolTuples width).map (BoolTuple.cons false) ++
        (allBoolTuples width).map (BoolTuple.cons true)

/-- The finite tuple enumeration is complete. -/
theorem mem_allBoolTuples {width : Nat} (tuple : BoolTuple width) :
    tuple ∈ allBoolTuples width := by
  induction tuple with
  | nil => exact List.Mem.head _
  | cons head tail ih =>
      cases head with
      | false =>
          exact List.mem_append_left _
            (mem_map_of_mem (BoolTuple.cons false) ih)
      | true =>
          exact List.mem_append_right _
            (mem_map_of_mem (BoolTuple.cons true) ih)

/-- A small Boolean equality test with fully transparent truth cases. -/
def boolEqual : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

theorem boolEqual_eq_true_iff (left right : Bool) :
    boolEqual left right = true ↔ left = right := by
  cases left with
  | false =>
      cases right with
      | false =>
          constructor
          · intro _
            rfl
          · intro _
            rfl
      | true => exact Iff.rfl
  | true =>
      cases right with
      | false =>
          constructor
          · intro impossible
            exact Bool.noConfusion impossible
          · intro impossible
            exact Bool.noConfusion impossible
      | true =>
          constructor
          · intro _
            rfl
          · intro _
            rfl

/-- Boolean universal quantification over a concrete finite list. -/
def allTrue {alpha : Type} : List alpha → (alpha → Bool) → Bool
  | [], _ => true
  | item :: items, predicate =>
      predicate item && allTrue items predicate

theorem allTrue_sound {alpha : Type} {items : List alpha}
    {predicate : alpha → Bool} (checked : allTrue items predicate = true)
    {item : alpha} (member : item ∈ items) : predicate item = true := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      change (predicate head && allTrue tail predicate) = true at checked
      have headCheck : predicate head = true := by
        cases result : predicate head with
      | false =>
          rw [result] at checked
          exact Bool.noConfusion checked
        | true => rfl
      rw [headCheck] at checked
      cases member with
      | head => exact headCheck
      | tail _ tailMember => exact ih checked tailMember

theorem allTrue_complete {alpha : Type} (items : List alpha)
    (predicate : alpha → Bool)
    (checked : ∀ item, item ∈ items → predicate item = true) :
    allTrue items predicate = true := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change (predicate head && allTrue tail predicate) = true
      rw [checked head (List.Mem.head _)]
      exact ih (fun item member => checked item (List.Mem.tail head member))

/-- Source evaluation respects pointwise-equal input and gate valuations. -/
theorem Source.eval_congr {inputs gates : Nat} (source : Source inputs gates)
    {leftInput rightInput : Valuation inputs}
    {leftGates rightGates : Valuation gates}
    (inputEqual : ∀ index, leftInput index = rightInput index)
    (gatesEqual : ∀ index, leftGates index = rightGates index) :
    source.eval leftInput leftGates = source.eval rightInput rightGates := by
  cases source with
  | input index => exact inputEqual index
  | constant value => rfl
  | gate index => exact gatesEqual index

/-- Gate evaluation respects pointwise-equal available values. -/
theorem Gate.eval_congr {inputs gates : Nat} (gate : Gate inputs gates)
    {leftInput rightInput : Valuation inputs}
    {leftGates rightGates : Valuation gates}
    (inputEqual : ∀ index, leftInput index = rightInput index)
    (gatesEqual : ∀ index, leftGates index = rightGates index) :
    gate.eval leftInput leftGates = gate.eval rightInput rightGates := by
  unfold Gate.eval
  rw [gate.left.eval_congr inputEqual gatesEqual]
  rw [gate.right.eval_congr inputEqual gatesEqual]

/-- Program evaluation respects pointwise-equal primary inputs. -/
theorem Program.eval_input_congr {inputs gates : Nat}
    (program : Program inputs gates)
    {leftInput rightInput : Valuation inputs}
    (inputEqual : ∀ index, leftInput index = rightInput index)
    (gateIndex : Fin gates) :
    program.eval leftInput gateIndex = program.eval rightInput gateIndex := by
  induction program with
  | empty => exact Fin.elim0 gateIndex
  | snoc initial gate ih =>
      unfold Program.eval Valuation.snoc
      split
      · exact ih _
      · exact gate.eval_congr inputEqual (fun index => ih index)

/-- Candidate semantics respects pointwise-equal primary inputs. -/
theorem Candidate.semantics_input_congr {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    {leftInput rightInput : Valuation inputs}
    (inputEqual : ∀ index, leftInput index = rightInput index)
    (output : Fin outputs) :
    candidate.semantics leftInput output =
      candidate.semantics rightInput output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  apply Source.eval_congr
  · exact inputEqual
  · intro gateIndex
    exact candidate.program.eval_input_congr inputEqual gateIndex

/-- Exhaustively compare two candidates, even when their gate counts differ. -/
def equivalentBool {inputs outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates outputs)
    (right : Candidate inputs rightGates outputs) : Bool :=
  allTrue (allBoolTuples inputs) fun input =>
    allTrue (allFin outputs) fun output =>
      boolEqual (left.semantics input.toValuation output)
        (right.semantics input.toValuation output)

/-- A successful exhaustive comparison is semantically sound. -/
theorem equivalentBool_sound {inputs outputs leftGates rightGates : Nat}
    {left : Candidate inputs leftGates outputs}
    {right : Candidate inputs rightGates outputs}
    (checked : equivalentBool left right = true) :
    Equivalent left.program left.directWireWord
      right.program right.directWireWord := by
  intro input output
  let tuple := BoolTuple.ofFn input
  have tupleChecked := allTrue_sound checked (mem_allBoolTuples tuple)
  have outputChecked := allTrue_sound tupleChecked (mem_allFin output)
  have tableEqual : left.semantics tuple.toValuation output =
      right.semantics tuple.toValuation output :=
    (boolEqual_eq_true_iff _ _).mp outputChecked
  exact (left.semantics_input_congr
      (fun index => BoolTuple.toValuation_ofFn input index) output).symm.trans
    (tableEqual.trans
      (right.semantics_input_congr
        (fun index => BoolTuple.toValuation_ofFn input index) output))

/-- Pointwise semantic equivalence makes the finite comparison succeed. -/
theorem equivalentBool_complete {inputs outputs leftGates rightGates : Nat}
    {left : Candidate inputs leftGates outputs}
    {right : Candidate inputs rightGates outputs}
    (equivalent : Equivalent left.program left.directWireWord
      right.program right.directWireWord) :
    equivalentBool left right = true := by
  apply allTrue_complete
  intro input _inputMember
  apply allTrue_complete
  intro output _outputMember
  exact (boolEqual_eq_true_iff _ _).mpr
    (equivalent input.toValuation output)

/-- The executable truth-table test exactly decides semantic equivalence. -/
theorem equivalentBool_eq_true_iff {inputs outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates outputs)
    (right : Candidate inputs rightGates outputs) :
    equivalentBool left right = true ↔
      Equivalent left.program left.directWireWord
        right.program right.directWireWord :=
  ⟨equivalentBool_sound, equivalentBool_complete⟩

/-- Exhaustive candidate comparison is reflexive. -/
theorem equivalentBool_refl {inputs outputs gates : Nat}
    (candidate : Candidate inputs gates outputs) :
    equivalentBool candidate candidate = true :=
  equivalentBool_complete
    (Equivalent.refl candidate.program candidate.directWireWord)

/-- Exhaustive candidate comparison is symmetric. -/
theorem equivalentBool_symm {inputs outputs leftGates rightGates : Nat}
    {left : Candidate inputs leftGates outputs}
    {right : Candidate inputs rightGates outputs}
    (checked : equivalentBool left right = true) :
    equivalentBool right left = true :=
  equivalentBool_complete (Equivalent.symm (equivalentBool_sound checked))

/-- Successful comparison is symmetric in both directions. -/
theorem equivalentBool_eq_true_symm {inputs outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates outputs)
    (right : Candidate inputs rightGates outputs) :
    equivalentBool left right = true ↔ equivalentBool right left = true := by
  constructor
  · exact equivalentBool_symm
  · exact equivalentBool_symm

/-- Swapping the candidates leaves the executable Boolean result unchanged. -/
theorem equivalentBool_comm {inputs outputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates outputs)
    (right : Candidate inputs rightGates outputs) :
    equivalentBool left right = equivalentBool right left := by
  cases leftResult : equivalentBool left right with
  | false =>
      cases rightResult : equivalentBool right left with
      | false => rfl
      | true =>
          have impossible : equivalentBool left right = true :=
            equivalentBool_symm rightResult
          rw [leftResult] at impossible
          exact Bool.noConfusion impossible
  | true =>
      cases rightResult : equivalentBool right left with
      | false =>
          have impossible : equivalentBool right left = true :=
            equivalentBool_symm leftResult
          rw [rightResult] at impossible
          exact Bool.noConfusion impossible
      | true => rfl

/-- With no outputs, every pair of candidates is equivalent. -/
theorem equivalentBool_zero_outputs {inputs leftGates rightGates : Nat}
    (left : Candidate inputs leftGates 0)
    (right : Candidate inputs rightGates 0) :
    equivalentBool left right = true := by
  apply allTrue_complete
  intro input _inputMember
  rfl

end DirectWire
end PNP
