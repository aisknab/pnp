/-
Copyright (c) 2026 PNP Labs.

Finite bit-register syntax for the normalizer implementation. Instructions
contain only finite register indices, bits, and control addresses. A source
step is not a tape transition: the storage bound proved here is an input to
the still-required literal tape compiler, not a concrete runtime theorem.
-/

import PNP.Concrete.WorkMachine

namespace PNP.Concrete.BitRegister

/-- A fixed finite bank of finite strings, not a function-valued store. -/
inductive Store : Nat → Type where
  | nil : Store 0
  | cons {count : Nat} : BitString → Store count → Store (count + 1)
deriving Repr

namespace Store

/-- Constructor case analysis without the library's propositional-extensionality
dependency. The only data being inspected is the finite index. -/
def indexCases {count : Nat} {motive : Fin (count + 1) → Sort u}
    (atZero : motive ⟨0, Nat.zero_lt_succ count⟩)
    (atSuccessor : (index : Fin count) → motive index.succ)
    (index : Fin (count + 1)) : motive index :=
  match index with
  | ⟨0, _⟩ => atZero
  | ⟨value + 1, h⟩ => atSuccessor ⟨value, Nat.lt_of_succ_lt_succ h⟩

def get {count : Nat} (store : Store count) (index : Fin count) : BitString :=
  match store with
  | .nil => Fin.elim0 index
  | .cons first rest =>
      indexCases (motive := fun _ => BitString) first (fun next => get rest next) index
termination_by structural store

def set {count : Nat} (store : Store count) (index : Fin count)
    (value : BitString) : Store count :=
  match store with
  | .nil => Fin.elim0 index
  | @Store.cons width first rest =>
      indexCases (motive := fun _ => Store (width + 1)) (Store.cons value rest)
        (fun next => Store.cons first (set rest next value)) index
termination_by structural store

def empty : (count : Nat) → Store count
  | 0 => .nil
  | count + 1 => .cons [] (empty count)

/-- Every register, including scratch space, is included in this bound. -/
def Bounded {count : Nat} (store : Store count) (bound : Nat) : Prop :=
  match store with
  | .nil => True
  | .cons first rest => first.length ≤ bound ∧ rest.Bounded bound
termination_by structural store

theorem bounded_mono {count : Nat} {store : Store count} {small large : Nat} :
    store.Bounded small → small ≤ large → store.Bounded large := by
  induction store with
  | nil => intro _ _; exact True.intro
  | cons first rest ih =>
      intro h hle
      exact ⟨Nat.le_trans h.1 hle, ih h.2 hle⟩

theorem get_length_le {count : Nat} (store : Store count) (index : Fin count)
    {bound : Nat} (h : store.Bounded bound) :
    (store.get index).length ≤ bound := by
  induction store with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      exact indexCases
        (motive := fun selected => ((Store.cons first rest).get selected).length ≤ bound)
        h.1 (fun next => ih next h.2) index

theorem set_bounded {count : Nat} (store : Store count) (index : Fin count)
    (value : BitString) {bound : Nat} (h : store.Bounded bound)
    (hv : value.length ≤ bound) : (store.set index value).Bounded bound := by
  induction store with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      exact indexCases
        (motive := fun selected => ((Store.cons first rest).set selected value).Bounded bound)
        (And.intro hv h.2) (fun next => And.intro h.1 (ih next h.2)) index

theorem empty_bounded (count bound : Nat) : (empty count).Bounded bound := by
  induction count with
  | zero => exact True.intro
  | succ count ih => exact ⟨Nat.zero_le bound, ih⟩

theorem get_set_same {count : Nat} (store : Store count) (index : Fin count)
    (value : BitString) : (store.set index value).get index = value := by
  induction store with
  | nil => exact Fin.elim0 index
  | cons first rest ih =>
      exact indexCases
        (motive := fun selected =>
          ((Store.cons first rest).set selected value).get selected = value)
        (Eq.refl value) (fun next => ih next) index

/-- Delimiters count towards the occupied tape span. -/
def span {count : Nat} (store : Store count) : Nat :=
  match store with
  | .nil => 0
  | .cons first rest => first.length + 1 + rest.span
termination_by structural store

theorem span_le {count : Nat} (store : Store count) {bound : Nat}
    (h : store.Bounded bound) : store.span ≤ count * (bound + 1) := by
  induction store with
  | nil => exact Nat.zero_le _
  | @cons count first rest ih =>
      calc
        first.length + 1 + rest.span
            ≤ (bound + 1) + count * (bound + 1) :=
          Nat.add_le_add (Nat.add_le_add_right h.1 1) (ih h.2)
        _ = (count + 1) * (bound + 1) := by
          rw [Nat.succ_mul, Nat.add_comm]

def bitSymbol (bit : Bool) : WorkSymbol :=
  ⟨TapeSymbol.ofBool bit, .blank⟩

def separator : WorkSymbol := WorkSymbol.blankOne

def encode {count : Nat} (store : Store count) : List WorkSymbol :=
  match store with
  | .nil => []
  | .cons first rest => first.map bitSymbol ++ separator :: rest.encode
termination_by structural store

theorem word_length_append (left right : List WorkSymbol) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons first rest ih =>
      change Nat.succ (rest ++ right).length = Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

theorem bitWord_length (bits : BitString) :
    (bits.map bitSymbol).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

theorem encode_length {count : Nat} (store : Store count) :
    store.encode.length = store.span := by
  induction store with
  | nil => rfl
  | cons first rest ih =>
      change (first.map bitSymbol ++ separator :: rest.encode).length =
        first.length + 1 + rest.span
      rw [word_length_append, bitWord_length]
      change first.length + (rest.encode.length + 1) = first.length + 1 + rest.span
      rw [ih, Nat.add_comm rest.span 1, Nat.add_assoc]

/-- Both exterior markers are explicit; neither is an encoded data symbol. -/
def initialTape {count : Nat} (store : Store count) : WorkTape :=
  { left := []
    head := WorkSymbol.blankZero
    right := store.encode ++ [WorkSymbol.zeroZero] }

theorem initialTape_span_le {count : Nat} (store : Store count) {bound : Nat}
    (h : store.Bounded bound) :
    store.initialTape.left.length + 1 + store.initialTape.right.length
      ≤ count * (bound + 1) + 2 := by
  change 0 + 1 + (store.encode ++ [WorkSymbol.zeroZero]).length ≤ _
  rw [word_length_append, encode_length]
  change 1 + (store.span + 1) ≤ _
  rw [← Nat.add_assoc, Nat.add_comm 1 store.span, Nat.add_assoc]
  exact Nat.add_le_add_right (span_le store h) 2

end Store

/-- All source-language executable data are finite syntax. -/
inductive Instruction (registers : Nat) where
  | clear (destination : Fin registers) (next : Nat)
  | copy (destination source : Fin registers) (next : Nat)
  | push (destination : Fin registers) (bit : Bool) (next : Nat)
  | pop (destination : Fin registers) (next : Nat)
  | branch (source : Fin registers) (empty zeroBranch oneBranch : Nat)
  | jump (next : Nat)
  | accept
  | reject
deriving Repr

inductive Control where
  | running (address : Nat)
  | accepted
  | rejected
deriving BEq, DecidableEq, Repr

structure Program (registers : Nat) where
  code : List (Instruction registers)
  entry : Nat
  input : Fin registers
  output : Fin registers
deriving Repr

structure Configuration (registers : Nat) where
  control : Control
  store : Store registers
deriving Repr

namespace Instruction

def update {count : Nat} (instruction : Instruction count)
    (store : Store count) : Store count :=
  match instruction with
  | .clear destination _ => store.set destination []
  | .copy destination source _ => store.set destination (store.get source)
  | .push destination bit _ => store.set destination (bit :: store.get destination)
  | .pop destination _ => store.set destination (store.get destination).tail
  | .branch _ _ _ _ => store
  | .jump _ => store
  | .accept => store
  | .reject => store

def nextControl {count : Nat} : Instruction count → Store count → Control
  | .clear _ next, _ => .running next
  | .copy _ _ next, _ => .running next
  | .push _ _ next, _ => .running next
  | .pop _ next, _ => .running next
  | .branch source empty zeroBranch oneBranch, store =>
      match store.get source with
      | [] => .running empty
      | false :: _ => .running zeroBranch
      | true :: _ => .running oneBranch
  | .jump next, _ => .running next
  | .accept, _ => .accepted
  | .reject, _ => .rejected

def execute {count : Nat} (instruction : Instruction count)
    (store : Store count) : Configuration count :=
  ⟨instruction.nextControl store, instruction.update store⟩

/-- Only push can increase the maximum register length, and only by one. -/
theorem update_bounded {count bound : Nat} (instruction : Instruction count)
    (store : Store count) (h : store.Bounded bound) :
    (instruction.update store).Bounded (bound + 1) := by
  have hmono : store.Bounded (bound + 1) :=
    Store.bounded_mono h (Nat.le_succ bound)
  cases instruction with
  | clear destination next =>
      exact Store.set_bounded store destination [] hmono (Nat.zero_le _)
  | copy destination source next =>
      exact Store.set_bounded store destination (store.get source) hmono
        (Nat.le_trans (Store.get_length_le store source h) (Nat.le_succ bound))
  | push destination bit next =>
      exact Store.set_bounded store destination (bit :: store.get destination) hmono
        (Nat.succ_le_succ (Store.get_length_le store destination h))
  | pop destination next =>
      apply Store.set_bounded store destination (store.get destination).tail hmono
      have hlength := Store.get_length_le store destination h
      cases hvalue : store.get destination with
      | nil => exact Nat.zero_le _
      | cons bit rest =>
          change rest.length ≤ bound + 1
          rw [hvalue] at hlength
          change rest.length + 1 ≤ bound at hlength
          exact Nat.le_trans (Nat.le_trans (Nat.le_succ rest.length) hlength)
            (Nat.le_succ bound)
  | branch source empty zeroBranch oneBranch => exact hmono
  | jump next => exact hmono
  | accept => exact hmono
  | reject => exact hmono

end Instruction

/-- Finite list lookup by constructors, without an extensionality dependency. -/
def lookup {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | first :: _, 0 => some first
  | _ :: rest, address + 1 => lookup rest address

/-- A missing instruction rejects. Running out of interpreter fuel does not
accept or manufacture a termination result. -/
def step {count : Nat} (program : Program count)
    (configuration : Configuration count) : Configuration count :=
  match configuration.control with
  | .accepted => configuration
  | .rejected => configuration
  | .running address =>
      match lookup program.code address with
      | none => ⟨.rejected, configuration.store⟩
      | some instruction => instruction.execute configuration.store

def run {count : Nat} (program : Program count) :
    Nat → Configuration count → Configuration count
  | 0, configuration => configuration
  | fuel + 1, configuration => run program fuel (step program configuration)

def initial {count : Nat} (program : Program count)
    (input : BitString) : Configuration count :=
  ⟨.running program.entry, (Store.empty count).set program.input input⟩

theorem initial_bounded {count : Nat} (program : Program count) (input : BitString) :
    (initial program input).store.Bounded input.length :=
  Store.set_bounded (Store.empty count) program.input input
    (Store.empty_bounded count input.length) (Nat.le_refl _)

theorem step_bounded {count bound : Nat} (program : Program count)
    (configuration : Configuration count) (h : configuration.store.Bounded bound) :
    (step program configuration).store.Bounded (bound + 1) := by
  cases configuration with
  | mk control store =>
      cases control with
      | accepted => exact Store.bounded_mono h (Nat.le_succ bound)
      | rejected => exact Store.bounded_mono h (Nat.le_succ bound)
      | running address =>
          change (match lookup program.code address with
            | none => (⟨.rejected, store⟩ : Configuration count)
            | some instruction => instruction.execute store).store.Bounded (bound + 1)
          cases hcode : lookup program.code address with
          | none => exact Store.bounded_mono h (Nat.le_succ bound)
          | some instruction => exact Instruction.update_bounded instruction store h

theorem run_bounded {count : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) {bound : Nat}
    (h : configuration.store.Bounded bound) :
    (run program fuel configuration).store.Bounded (bound + fuel) := by
  induction fuel generalizing configuration bound with
  | zero => exact h
  | succ fuel ih =>
      change (run program fuel (step program configuration)).store.Bounded
        (bound + (fuel + 1))
      have hsum : bound + (fuel + 1) = (bound + 1) + fuel := by
        rw [Nat.add_assoc, Nat.add_comm 1 fuel]
      rw [hsum]
      exact ih (step program configuration) (step_bounded program configuration h)

theorem run_add {count : Nat} (program : Program count) (first second : Nat)
    (configuration : Configuration count) :
    run program (first + second) configuration =
      run program second (run program first configuration) := by
  induction first generalizing configuration with
  | zero => rw [Nat.zero_add]; rfl
  | succ first ih =>
      rw [Nat.succ_add]
      exact ih (step program configuration)

theorem run_accepted {count : Nat} (program : Program count) (fuel : Nat)
    (store : Store count) :
    run program fuel ⟨.accepted, store⟩ = ⟨.accepted, store⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem run_rejected {count : Nat} (program : Program count) (fuel : Nat)
    (store : Store count) :
    run program fuel ⟨.rejected, store⟩ = ⟨.rejected, store⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

/-- A bound on representation size only, not on concrete tape transitions. -/
theorem input_run_encoded_span {count : Nat} (program : Program count)
    (input : BitString) (fuel : Nat) :
    (run program fuel (initial program input)).store.encode.length
      ≤ count * (input.length + fuel + 1) := by
  rw [Store.encode_length]
  exact Store.span_le _ (run_bounded program fuel _ (initial_bounded program input))

theorem input_run_tape_span {count : Nat} (program : Program count)
    (input : BitString) (fuel : Nat) :
    let tape := (run program fuel (initial program input)).store.initialTape
    tape.left.length + 1 + tape.right.length
      ≤ count * (input.length + fuel + 1) + 2 :=
  Store.initialTape_span_le _
    (run_bounded program fuel _ (initial_bounded program input))

end PNP.Concrete.BitRegister
