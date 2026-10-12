/-
Copyright (c) 2026 PNP Labs.

Typed finite stores and their exact tape representation. A selected register
is derived from its finite index, not supplied as a decomposition witness.
The canonical tape operations implement the original Store updates exactly.
All registers, including any compiler-owned scratch, count towards the span.
-/

import PNP.Concrete.BitRegisterCopyProgram
import PNP.Concrete.BitRegisterCanonical

namespace PNP.Concrete.BitRegister

open TapePrimitive Mutation Operation

namespace Operation

theorem fieldWord_append (first second : List BitString) :
    fieldWord (first ++ second) = fieldWord first ++ fieldWord second := by
  induction first with
  | nil => rfl
  | cons bits rest ih =>
      simp only [List.cons_append, fieldWord_cons, ih, List.append_assoc]

end Operation

namespace Store

def fields {count : Nat} (store : Store count) : List BitString :=
  match store with
  | .nil => []
  | .cons first rest => first :: fields rest
termination_by structural store

def beforeFields {count : Nat} (store : Store count) (index : Fin count) : List BitString :=
  match store with
  | .nil => Fin.elim0 index
  | .cons first rest =>
      indexCases (motive := fun _ => List BitString) [] (fun next => first :: beforeFields rest next) index
termination_by structural store

def afterFields {count : Nat} (store : Store count) (index : Fin count) : List BitString :=
  match store with
  | .nil => Fin.elim0 index
  | .cons _ rest =>
      indexCases (motive := fun _ => List BitString) (fields rest) (fun next => afterFields rest next) index
termination_by structural store

@[simp] theorem beforeFields_cons_zero {count : Nat} (first : BitString) (rest : Store count) :
    (Store.cons first rest).beforeFields (0 : Fin (count + 1)) = [] := by rfl

@[simp] theorem beforeFields_cons_succ {count : Nat} (first : BitString) (rest : Store count)
    (index : Fin count) :
    (Store.cons first rest).beforeFields index.succ = first :: rest.beforeFields index := by rfl

@[simp] theorem afterFields_cons_zero {count : Nat} (first : BitString) (rest : Store count) :
    (Store.cons first rest).afterFields (0 : Fin (count + 1)) = rest.fields := by rfl

@[simp] theorem afterFields_cons_succ {count : Nat} (first : BitString) (rest : Store count)
    (index : Fin count) :
    (Store.cons first rest).afterFields index.succ = rest.afterFields index := by rfl

theorem fields_length {count : Nat} (store : Store count) : store.fields.length = count := by
  induction store with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

theorem fields_encode {count : Nat} (store : Store count) :
    fieldWord store.fields = store.encode := by
  induction store with
  | nil => rfl
  | cons first rest ih =>
      change fieldWord (first :: rest.fields) = first.map bitSymbol ++ separator :: rest.encode
      rw [fieldWord_cons, ih]

theorem beforeFields_length {count : Nat} (store : Store count) (index : Fin count) :
    (store.beforeFields index).length = index.val := by
  induction store with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          change (first :: rest.beforeFields index).length = index.val + 1
          exact congrArg Nat.succ (ih index)

theorem fields_set_split {count : Nat} (store : Store count) (index : Fin count)
    (value : BitString) :
    (store.set index value).fields = store.beforeFields index ++ value :: store.afterFields index := by
  induction store with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          simp only [set_cons_succ, fields, beforeFields_cons_succ, afterFields_cons_succ,
            List.cons_append, ih]

theorem fields_split {count : Nat} (store : Store count) (index : Fin count) :
    store.fields = store.beforeFields index ++ store.get index :: store.afterFields index := by
  have h := fields_set_split store index (store.get index)
  simpa only [set_get] using h

theorem span_split {count : Nat} (store : Store count) (index : Fin count) :
    store.span = (fieldCells (store.beforeFields index)).length + (store.get index).length + 1 +
      (fieldCells (store.afterFields index)).length := by
  have h := congrArg (fun values => (fieldWord values).length) (fields_split store index)
  simp only [fields_encode, encode_length, fieldWord_append, fieldWord_cons,
    List.length_append, List.length_map, List.length_cons, fieldWord_length] at h
  omega

theorem bankSpan_selected {count : Nat} (store : Store count) (index : Fin count) :
    bankSpan (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index)) =
      store.span + 2 := by
  unfold bankSpan
  rw [span_split store index]
  omega

/-- The complete encoded store, explicit exterior, and represented blank slack. -/
def tape {count : Nat} (store : Store count) (outside : List WorkSymbol) (slack : Nat) : WorkTape :=
  ⟨outside, WorkSymbol.blankZero, store.encode ++ tail slack⟩

theorem tape_initial {count : Nat} (store : Store count) : store.tape [] 0 = store.initialTape := by rfl

theorem set_tape_boundary {count : Nat} (store : Store count) (index : Fin count)
    (value : BitString) (outside : List WorkSymbol) (slack : Nat) :
    (store.set index value).tape outside slack =
      atBoundary (store.beforeFields index) value (fieldCells (store.afterFields index)) outside slack := by
  unfold tape atBoundary content
  rw [← fields_encode (store.set index value), fields_set_split, fieldWord_append, fieldWord_cons]
  simp only [List.append_assoc, List.cons_append, fieldWord]

theorem tape_boundary {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    store.tape outside slack =
      atBoundary (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index)) outside slack := by
  have h := set_tape_boundary store index (store.get index) outside slack
  simpa only [set_get] using h

def pushSteps {count : Nat} (store : Store count) (index : Fin count) : Nat :=
  pushAtSteps (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index))

def popSteps {count : Nat} (store : Store count) (index : Fin count) : Nat :=
  popAtSteps (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index))

def clearSteps {count : Nat} (store : Store count) (index : Fin count) : Nat :=
  clearAtSteps (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index))

theorem push_run {count : Nat} (store : Store count) (index : Fin count) (bit : Bool)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (pushAt index.val bit) (store.pushSteps index)
      ⟨(pushAt index.val bit).startState, store.tape outside slack⟩ =
    some ⟨(pushAt index.val bit).acceptState,
      (store.set index (bit :: store.get index)).tape outside (slack - 1)⟩ := by
  rw [tape_boundary store index outside slack, set_tape_boundary]
  simpa only [pushSteps, beforeFields_length] using
    pushAt_run (store.beforeFields index) bit (store.get index) (fieldCells (store.afterFields index)) outside slack

theorem pop_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (popAt index.val) (store.popSteps index)
      ⟨(popAt index.val).startState, store.tape outside slack⟩ =
    some ⟨(popAt index.val).acceptState,
      (store.set index (store.get index).tail).tape outside (popSlack (store.get index) slack)⟩ := by
  rw [tape_boundary store index outside slack, set_tape_boundary]
  simpa only [popSteps, beforeFields_length] using
    popAt_run (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index)) outside slack

theorem clear_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (clearAt index.val) (store.clearSteps index)
      ⟨(clearAt index.val).startState, store.tape outside slack⟩ =
    some ⟨(clearAt index.val).acceptState,
      (store.set index []).tape outside (slack + (store.get index).length)⟩ := by
  rw [tape_boundary store index outside slack, set_tape_boundary]
  simpa only [clearSteps, beforeFields_length] using
    clearAt_run (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index)) outside slack

theorem push_raw_run {count : Nat} (store : Store count) (index : Fin count) (bit : Bool)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (pushAt index.val bit)) (6 * store.pushSteps index)
      (encodeWorkConfiguration ⟨(pushAt index.val bit).startState, store.tape outside slack⟩) =
    encodeWorkConfiguration ⟨(pushAt index.val bit).acceptState,
      (store.set index (bit :: store.get index)).tape outside (slack - 1)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (push_run store index bit outside slack)

theorem pop_raw_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (popAt index.val)) (6 * store.popSteps index)
      (encodeWorkConfiguration ⟨(popAt index.val).startState, store.tape outside slack⟩) =
    encodeWorkConfiguration ⟨(popAt index.val).acceptState,
      (store.set index (store.get index).tail).tape outside (popSlack (store.get index) slack)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (pop_run store index outside slack)

theorem clear_raw_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (clearAt index.val)) (6 * store.clearSteps index)
      (encodeWorkConfiguration ⟨(clearAt index.val).startState, store.tape outside slack⟩) =
    encodeWorkConfiguration ⟨(clearAt index.val).acceptState,
      (store.set index []).tape outside (slack + (store.get index).length)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (clear_run store index outside slack)

theorem pushSteps_le {count : Nat} (store : Store count) (index : Fin count) :
    store.pushSteps index ≤ 3 * (store.span + 2) + 2 := by
  have h := pushAtSteps_le (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index))
  rw [bankSpan_selected] at h
  exact h

theorem popSteps_le {count : Nat} (store : Store count) (index : Fin count) :
    store.popSteps index ≤ 4 * (store.span + 2) := by
  have h := popAtSteps_le (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index))
  rw [bankSpan_selected] at h
  exact h

theorem clearSteps_le {count : Nat} (store : Store count) (index : Fin count) :
    store.clearSteps index ≤ 9 * (store.span + 2) * (store.span + 2) + 15 * (store.span + 2) + 8 := by
  have h := clearAtSteps_le (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index))
  rw [bankSpan_selected] at h
  exact h

end Store
end PNP.Concrete.BitRegister
