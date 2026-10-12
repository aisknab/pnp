/-
Copyright (c) 2026 PNP Labs.

Closed vertex-kind parsing and dispatch. Two leading bits are read as
endpoint tags, and the remaining packet is parsed by the verified data
loader. Clause-to-variable and variable-to-clause queries use their actual
data; equal-kind pairs return false. Empty malformed tags default to false.
-/

import PNP.Concrete.NormalizerEdgeBranches

namespace PNP.Concrete.NormalizerBlocks.EdgeKinds

open BitRegister

theorem branch_head {count : Nat} (source : Fin count) (before : Store count)
    (zero one : Block count) (zeroFuel oneFuel : Nat) (zeroAfter oneAfter : Store count)
    (checkedZero : Exec zero before zeroFuel zeroAfter)
    (checkedOne : Exec one before oneFuel oneAfter) :
    Exec (.branch source zero zero one) before
      (1 + if (before.get source).headD false then oneFuel else zeroFuel)
      (if (before.get source).headD false then oneAfter else zeroAfter) := by
  cases read : before.get source with
  | nil =>
      simp only [List.headD, Bool.false_eq_true, ite_false]
      exact Exec.empty read checkedZero
  | cons bit rest =>
      cases bit with
      | false =>
          simp only [List.headD, Bool.false_eq_true, ite_false]
          exact Exec.zero read checkedZero
      | true =>
          simp only [List.headD, ite_true]
          exact Exec.one read checkedOne

structure State where
  core : ForwardEdge.State
  first : BitString
  second : BitString

def State.frame (r : State) : Store 2 := .cons r.first (.cons r.second .nil)
def State.store (r : State) : Store 16 := Frame.join r.core.store r.frame

def initial (input : BitString) : State := ⟨ForwardEdge.initial input, [], []⟩
def tags : Block 16 :=
  .seq (.action (.copy 14 0)) <| .seq (.action (.pop 0)) <|
    .seq (.action (.copy 15 0)) (.action (.pop 0))
def tagged (input : BitString) : State := ⟨ForwardEdge.initial input.tail.tail, input, input.tail⟩

theorem tags_exec (input : BitString) : Exec tags (initial input).store 4 (tagged input).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def loader : Block 16 := .seq tags (Frame.block 2 ForwardEdge.loader)
def loaded (input : BitString) : State := ⟨ForwardEdge.loaded input.tail.tail, input, input.tail⟩
def loaderFuel (input : BitString) : Nat := 4 + ForwardEdge.loaderFuel input.tail.tail

theorem loader_exec (input : BitString) :
    Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (tags_exec input) (Frame.execution (ForwardEdge.loader_exec input.tail.tail) (tagged input).frame)

def rejected (r : State) : State := {r with core := ForwardEdge.emitted false r.core}
def reversed (r : State) : State := {r with core := reverseResult r.core}
def forwarded (r : State) : State := {r with core := forwardResult r.core}
def reject : Block 16 := Frame.block 2 (ForwardEdge.emit false)
def reverseBranch : Block 16 := Frame.block 2 reverse
def forwardBranch : Block 16 := Frame.block 2 forward

theorem reject_exec (r : State) : Exec reject r.store 2 (rejected r).store :=
  Frame.execution (ForwardEdge.emit_exec false r.core) r.frame
theorem reverseBranch_exec (r : State) : Exec reverseBranch r.store (reverseFuel r.core) (reversed r).store :=
  Frame.execution (reverse_exec r.core) r.frame
theorem forwardBranch_exec (r : State) : Exec forwardBranch r.store (forwardFuel r.core) (forwarded r).store :=
  Frame.execution (forward_exec r.core) r.frame

def variableCase : Block 16 := .branch 15 reject reject reverseBranch
def clauseCase : Block 16 := .branch 15 forwardBranch forwardBranch reject
def dispatch : Block 16 := .branch 14 variableCase variableCase clauseCase
def dispatchResult (r : State) : State :=
  if ForwardEdge.present r.first then
    if ForwardEdge.present r.second then rejected r else forwarded r
  else if ForwardEdge.present r.second then reversed r else rejected r
def dispatchFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.first then
    1 + if ForwardEdge.present r.second then 2 else forwardFuel r.core
  else 1 + if ForwardEdge.present r.second then reverseFuel r.core else 2

theorem dispatch_exec (r : State) : Exec dispatch r.store (dispatchFuel r) (dispatchResult r).store := by
  have low := branch_head (15 : Fin 16) r.store reject reverseBranch 2 (reverseFuel r.core)
    (rejected r).store (reversed r).store (reject_exec r) (reverseBranch_exec r)
  have high := branch_head (15 : Fin 16) r.store forwardBranch reject (forwardFuel r.core) 2
    (forwarded r).store (rejected r).store (forwardBranch_exec r) (reject_exec r)
  change Exec variableCase r.store
    (1 + if ForwardEdge.present r.second then reverseFuel r.core else 2)
    (if ForwardEdge.present r.second then (reversed r).store else (rejected r).store) at low
  change Exec clauseCase r.store
    (1 + if ForwardEdge.present r.second then 2 else forwardFuel r.core)
    (if ForwardEdge.present r.second then (rejected r).store else (forwarded r).store) at high
  have checked := branch_head (14 : Fin 16) r.store variableCase clauseCase _ _ _ _ low high
  change Exec dispatch r.store (dispatchFuel r)
    (if ForwardEdge.present r.first then
      if ForwardEdge.present r.second then (rejected r).store else (forwarded r).store
    else if ForwardEdge.present r.second then (reversed r).store else (rejected r).store) at checked
  cases first : ForwardEdge.present r.first <;> cases second : ForwardEdge.present r.second <;>
    simpa only [dispatchResult, first, second, Bool.false_eq_true, ite_false, ite_true] using checked

theorem dispatchFuel_bound (r : State) : dispatchFuel r ≤ branchBound r.core + 2 := by
  have reverse := reverseFuel_bound r.core
  have forward := forwardFuel_bound r.core
  have reject := branchBound_pos r.core
  cases first : ForwardEdge.present r.first <;> cases second : ForwardEdge.present r.second <;>
    simp only [dispatchFuel, first, second, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem dispatch_output (r : State) :
    (dispatchResult r).core.core.output =
      if ForwardEdge.present r.first then
        if ForwardEdge.present r.second then [false] else (forwardResult r.core).core.output
      else if ForwardEdge.present r.second then (reverseResult r.core).core.output else [false] := by
  cases first : ForwardEdge.present r.first <;> cases second : ForwardEdge.present r.second <;>
    simp only [dispatchResult, first, second, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem tail_length_le (input : BitString) : input.tail.tail.length ≤ input.length := by
  cases input with
  | nil => exact Nat.le_refl _
  | cons first rest =>
      cases rest <;> simp only [List.tail_cons, List.tail_nil, List.length_nil, List.length_cons] <;> omega

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 41 * input.length + 86 := by
  have bound := ForwardEdge.loaderFuel_bound input.tail.tail
  have length := tail_length_le input
  change 4 + ForwardEdge.loaderFuel input.tail.tail ≤ _
  omega

theorem loaded_size (input : BitString) :
    (loaded input).core.target.length ≤ 5 * input.length + 6 ∧
      (loaded input).core.index.length ≤ 5 * input.length + 6 ∧
        (loaded input).core.formula.length ≤ input.length ∧ (loaded input).core.matching.length ≤ input.length := by
  have bounds := ForwardEdge.loaded_size input.tail.tail
  have length := tail_length_le input
  change (ForwardEdge.loaded input.tail.tail).target.length ≤ _ ∧
    (ForwardEdge.loaded input.tail.tail).index.length ≤ _ ∧
    (ForwardEdge.loaded input.tail.tail).formula.length ≤ _ ∧ (ForwardEdge.loaded input.tail.tail).matching.length ≤ _
  exact ⟨by omega, by omega, by omega, by omega⟩

def encode (first second : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : BitString :=
  first.positive :: second.positive :: ForwardEdge.encode first.variableIndex second.variableIndex clauses entries

theorem loaded_first (first second : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    ForwardEdge.present (loaded (encode first second clauses entries)).first = first.positive := rfl
theorem loaded_second (first second : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    ForwardEdge.present (loaded (encode first second clauses entries)).second = second.positive := rfl
theorem loaded_core (first second : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    (loaded (encode first second clauses entries)).core =
      ForwardEdge.loaded (ForwardEdge.encode first.variableIndex second.variableIndex clauses entries) := rfl

end PNP.Concrete.NormalizerBlocks.EdgeKinds
