/-
Copyright (c) 2026 PNP Labs.

Ordered row-packet semantics. Counts describe packets, not bytes; reversing
the buffer preserves every packet, repeated term and source-order position.
-/
import PNP.Concrete.NormalizerSystemRowsE

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence

def bytes : List BitString → BitString
  | [] => []
  | packet::rest => packet ++ bytes rest
theorem bytes_append (xs ys : List BitString) : bytes (xs++ys) = bytes xs ++ bytes ys := by
  induction xs with
  | nil => rfl
  | cons packet rest ih =>
      rw [List.cons_append,bytes,bytes,ih,List.append_assoc]
def Produced (before after : State) (packets : List BitString) : Prop :=
  after.count = List.replicate packets.length true ++ before.count ∧
  after.buffer = (bytes packets).reverse ++ before.buffer
theorem produced_none (before after : State) (count : after.count = before.count)
    (buffer : after.buffer = before.buffer) : Produced before after [] := ⟨count,buffer⟩
theorem produced_one (before after : State) (packet : BitString)
    (count : after.count = true::before.count)
    (buffer : after.buffer = packet.reverse ++ before.buffer) :
    Produced before after [packet] := by
  exact ⟨count,by simpa only [bytes,List.append_nil] using buffer⟩
theorem produced_trans (a b c : State) (xs ys : List BitString)
    (first : Produced a b xs) (second : Produced b c ys) : Produced a c (xs++ys) := by
  constructor
  · rw [List.length_append]
    calc c.count = List.replicate ys.length true ++ (List.replicate xs.length true ++ a.count) := by
            rw [second.1,first.1]
         _ = List.replicate (ys.length+xs.length) true ++ a.count := by
            rw [Coefficient.replicate_sum,List.append_assoc]
         _ = List.replicate (xs.length+ys.length) true ++ a.count := by
            rw [Nat.add_comm ys.length xs.length]
  · rw [second.2,first.2,bytes_append,List.reverse_append,List.append_assoc]
theorem emit_produced (routine : Coefficient.Routine) (r : State) (packet : BitString)
    (output : (result routine r).registers.output = packet) :
    Produced r (emitted routine r) [packet] := by
  apply produced_one
  · exact (emitted_frame routine r).2.2.2.1
  · rw [(emitted_frame routine r).2.2.2.2,output]
theorem advance_produced (r : State) : Produced r (advanced r) [] :=
  produced_none _ _ rfl rfl

def input (r : State) : Coefficient.State := Coefficient.cleared (loaded r).core
theorem input_encoded (ctx : Coefficient.Context) (r : State) (encoded : ctx.Encoded r.core) :
    ctx.Encoded (input r) :=
  (loaded_encoded ctx r encoded).transport (Coefficient.cleared_data (loaded r).core)
theorem input_row (r : State) : (input r).row = r.counter := rfl
theorem result_output (routine : Coefficient.Routine) (r : State) :
    (result routine r).registers.output = (routine.result (input r)).registers.output := rfl

def packetsFrom (packets : Nat → List BitString) : Nat → Nat → List BitString
  | 0,_ => []
  | count+1,start => packets start ++ packetsFrom packets count (start+1)

theorem scan_produced (iteration : Iteration) (ctx : Coefficient.Context)
    (packets : Nat → List BitString) (limit : Nat)
    (step : ∀ r index, ctx.Encoded r.core → r.counter = List.replicate index true →
      index < limit → Produced r (iteration.result r) (packets index))
    (word : BitString) (r : State) (start : Nat)
    (encoded : ctx.Encoded r.core) (counter : r.counter = List.replicate start true)
    (within : start + word.length ≤ limit) :
    Produced r (scan iteration word r).state (packetsFrom packets word.length start) := by
  induction word generalizing r start with
  | nil => exact produced_none _ _ rfl rfl
  | cons bit rest ih =>
      let before := {r with remaining := bit::rest}
      let next := iteration.result before
      have eligible : start < limit := by
        simp only [List.length_cons] at within
        omega
      have head := step before start encoded counter eligible
      have nextEncoded : ctx.Encoded next.core :=
        encoded_transport ctx before next encoded (iteration.shared before)
      have nextCounter : next.counter = List.replicate (start+1) true := by
        rw [show next.counter = true::r.counter from iteration.counter before,counter,List.replicate_succ]
      have nextWithin : start+1+rest.length ≤ limit := by
        simp only [List.length_cons] at within
        omega
      have tail := ih next (start+1) nextEncoded nextCounter nextWithin
      exact produced_trans r next _ _ _ head tail

end PNP.Concrete.NormalizerBlocks.SystemRows
