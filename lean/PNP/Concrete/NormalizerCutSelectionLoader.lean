/-
Copyright (c) 2026 PNP Labs.

Read a finite count followed by the trace and select the complete range.
Malformed inputs still have bounded decoded counts and trace bytes. The
front-end bound includes loading and every membership/selection iteration.
-/
import PNP.Concrete.NormalizerCutSelectionSemantics

namespace PNP.Concrete.NormalizerBlocks.CutSelection
open BitRegister Occurrence

def initial (input : BitString) : State := ⟨ParentQuery.initial input, [], [], []⟩
def start (tag : Bool) : Block 24 :=
  .seq (.action (.copy 22 1)) <| .seq (.action (.copy 21 0)) <|
    .seq (.action (.clear 17)) <| .seq (.action (.clear 18)) <|
      .seq (.action (.push 18 tag)) (.action (.clear 23))
def started (tag : Bool) (r : State) : State :=
  { r with
    trace := r.registers.input
    remaining := r.registers.target
    buffer := []
    core := {r.core with targetIndex := [], targetTag := [tag]} }
theorem start_exec (tag : Bool) (r : State) : Exec (start tag) r.store 6 (started tag r).store := by
  dsimp only [start, started, State.store, State.frame, State.registers,
    ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers,
    EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame,
    Occurrence.Registers.store, Frame.join]
  exact Exec.seq (.action _ _) <| Exec.seq (.action _ _) <| Exec.seq (.action _ _) <|
    Exec.seq (.action _ _) <| Exec.seq (.action _ _) (.action _ _)

def headerResult (input : BitString) : State :=
  (initial input).withCore (ParentQuery.headerResult (initial input).core)
def loaded (tag : Bool) (input : BitString) : State := started tag (headerResult input)
def loader (tag : Bool) : Block 24 := .seq (liftMember ParentQuery.readHeader) (start tag)
def loaderFuel (input : BitString) : Nat := 8 + TableInit.headerFuel input + 6
theorem loader_exec (tag : Bool) (input : BitString) :
    Exec (loader tag) (initial input).store (loaderFuel input) (loaded tag input).store :=
  Exec.seq (liftMember_exec _ (initial input) _ _ (ParentQuery.readHeader_exec _)) (start_exec tag _)

theorem loaded_fields (tag : Bool) (input : BitString) :
    (loaded tag input).trace = (TableInit.readCount input).state.input ∧
      (loaded tag input).remaining = (TableInit.readCount input).state.target ∧
      (loaded tag input).core.targetIndex = [] ∧
      (loaded tag input).core.targetTag = [tag] ∧ (loaded tag input).buffer = [] :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem loaded_size (tag : Bool) (input : BitString) :
    (loaded tag input).trace.length ≤ input.length ∧
      (loaded tag input).remaining.length ≤ 5 * input.length + 6 := by
  rw [(loaded_fields tag input).1, (loaded_fields tag input).2.1]
  exact ⟨Occurrence.header_input_bound input (TableInit.seeded input), TableInit.count_length_bound input⟩
theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 4 * input.length + 21 := by
  have bound := TableInit.headerFuel_bound input
  unfold loaderFuel
  omega

def encode (count : Nat) (trace : List TraceData.Row) : BitString :=
  TableInit.encodeCount count (TraceData.encode trace)
theorem loaded_canonical (tag : Bool) (count : Nat) (trace : List TraceData.Row) :
    (loaded tag (encode count trace)).trace = TraceData.encode trace ∧
      (loaded tag (encode count trace)).remaining = List.replicate count true := by
  rw [(loaded_fields tag _).1, (loaded_fields tag _).2.1, encode, BatchPacket.header_canonical]
  exact ⟨rfl,rfl⟩

def front (tag : Bool) : Block 24 := .seq (loader tag) (loop tag)
def scanned (tag : Bool) (input : BitString) : State := (whole tag (loaded tag input)).state
def frontSteps (tag : Bool) (input : BitString) : Nat :=
  loaderFuel input + (whole tag (loaded tag input)).fuel
theorem front_exec (tag : Bool) (input : BitString) :
    Exec (front tag) (initial input).store (frontSteps tag input) (scanned tag input).store :=
  Exec.seq (loader_exec tag input) (whole_exec tag (loaded tag input))

def frontFuel : NatPolynomial :=
  .add (.linear 4 22) (.mul
    (.add (.mul (.linear 28 81) (.linear 1 1)) (.linear 20 45)) (.linear 5 6))
theorem frontFuel_eval (size : Nat) :
    frontFuel.eval size =
      4 * size + 22 + ((28 * size + 81) * (size + 1) + 20 * size + 45) * (5 * size + 6) := by
  change 4 * size + 22 + ((28 * size + 81) * (1 * size + 1) + (20 * size + 45)) * (5 * size + 6) = _
  simp only [Nat.one_mul, Nat.add_assoc]

theorem frontSteps_bound (tag : Bool) (input : BitString) :
    frontSteps tag input ≤ frontFuel.eval input.length := by
  have loading := loaderFuel_bound input
  have size := loaded_size tag input
  have loopBound := whole_fuel_bound tag (loaded tag input)
  rw [(loaded_fields tag input).2.2.1, List.length_nil] at loopBound
  have queryProduct := Nat.mul_le_mul
    (show 28 * (loaded tag input).trace.length + 81 ≤ 28 * input.length + 81 by omega)
    (show (loaded tag input).trace.length + 1 ≤ input.length + 1 by omega)
  have factor : stepBound (loaded tag input).trace.length
      (0 + (loaded tag input).remaining.length) + 1 ≤
      (28 * input.length + 81) * (input.length + 1) + 20 * input.length + 45 := by
    unfold stepBound
    omega
  have product := Nat.mul_le_mul factor size.2
  rw [frontFuel_eval]
  unfold frontSteps
  omega

theorem scanned_buffer (tag : Bool) (count : Nat) (trace : List TraceData.Row) :
    (scanned tag (encode count trace)).buffer =
      (selectedBits tag trace count 0).reverse := by
  have fields := loaded_fields tag (encode count trace)
  have canonical := loaded_canonical tag count trace
  have tagRead : ForwardEdge.present (loaded tag (encode count trace)).core.targetTag = tag := by
    rw [fields.2.2.2.1]
    rfl
  have result := whole_buffer tag (loaded tag (encode count trace)) 0 trace
    fields.2.2.1 tagRead canonical.1
  rw [canonical.2, List.length_replicate, fields.2.2.2.2, List.append_nil] at result
  exact result

end PNP.Concrete.NormalizerBlocks.CutSelection
