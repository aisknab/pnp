/-
Copyright (c) 2026 PNP Labs.

Each runtime iteration emits the exact ordered source packets. Representation
witnesses appear only in proofs; the closed A and E programs read their cache.
-/
import PNP.Concrete.NormalizerSystemRowsPackets

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence
attribute [local irreducible] Coefficient.entry Coefficient.imageTerms Coefficient.eligibleRow

def aPacket (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) : BitString :=
  CoefficientRow.bits row tag ++ Coefficient.encodeRows ((row,tag)::ctx.companionRows anchor literals tag)
def imageBytes (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (first : ctx.Literal row 0) : BitString :=
  Coefficient.encodeRows ((row,false)::ctx.literalRows anchor first)
def eligible (ctx : Coefficient.Context) (row : Nat) : Bool :=
  Coefficient.eligibleValue (MatchingTable.read ctx.modes row) row ctx.failed

theorem entry_packet (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) (r : State)
    (encoded : ctx.Encoded r.core) (counter : r.counter = List.replicate row true) :
    (result (Coefficient.entry tag) r).registers.output = aPacket ctx anchor row literals tag := by
  rw [result_output]
  exact Coefficient.entry_output ctx anchor row literals tag (input r)
    (input_encoded ctx r encoded) counter
theorem a_produced (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (r : State)
    (encoded : ctx.Encoded r.core) (counter : r.counter = List.replicate row true) :
    Produced r (aResult r) [aPacket ctx anchor row literals false,aPacket ctx anchor row literals true] := by
  let middle := emitted (Coefficient.entry false) r
  have first := emit_produced (Coefficient.entry false) r _ (entry_packet ctx anchor row literals false r encoded counter)
  have nextEncoded : ctx.Encoded middle.core :=
    encoded_transport ctx r middle encoded (emitted_shared _ (Coefficient.entry_data false) r)
  have second := emit_produced (Coefficient.entry true) middle _
    (entry_packet ctx anchor row literals true middle nextEncoded counter)
  exact produced_trans r middle (emitted (Coefficient.entry true) middle) _ _ first second

theorem image_packet (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (first : ctx.Literal row 0) (r : State)
    (encoded : ctx.Encoded r.core) (counter : r.counter = List.replicate row true) :
    (result imagePacket r).registers.output = imageBytes ctx anchor row first := by
  rw [result_output]
  have inputEncoded := input_encoded ctx r encoded
  have emitted := Coefficient.imageTerms_emits ctx anchor row first (Coefficient.started (input r))
    (inputEncoded.transport (Coefficient.start_data (input r))) counter
  exact Coefficient.packet_output Coefficient.imageTerms (input r) _ emitted
theorem eligible_output (ctx : Coefficient.Context) (row : Nat) (r : State)
    (encoded : ctx.Encoded r.core) (counter : r.counter = List.replicate row true) :
    (result Coefficient.eligibleRow r).registers.output = [eligible ctx row] := by
  rw [result_output]
  have fields := input_encoded ctx r encoded
  exact Coefficient.eligibleRow_canonical (input r) ctx.modes row ctx.failed
    fields.modes counter fields.failed
theorem eligible_iff (ctx : Coefficient.Context) (row : Nat) :
    eligible ctx row = true ↔ MatchingTable.read ctx.modes row = none ∧ row ≠ ctx.failed :=
  Coefficient.eligibleValue_iff _ _ _

theorem e_produced (ctx : Coefficient.Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (first : ctx.Literal row 0) (r : State)
    (encoded : ctx.Encoded r.core) (counter : r.counter = List.replicate row true) :
    Produced r (eResult r) (if eligible ctx row then [imageBytes ctx anchor row first] else []) := by
  let tested := result Coefficient.eligibleRow r
  have read : tested.registers.output = [eligible ctx row] := eligible_output ctx row r encoded counter
  have nextEncoded : ctx.Encoded tested.core :=
    encoded_transport ctx r tested encoded (result_shared _ Coefficient.eligibleRow_data r)
  have packet := emit_produced imagePacket tested _ (image_packet ctx anchor row first tested nextEncoded counter)
  have quiet : Produced r tested [] := produced_none _ _ rfl rfl
  change Produced r (advanced (eBranchResult tested)) _
  unfold eBranchResult
  rw [read]
  simp only [List.headD_cons]
  cases h : eligible ctx row
  · simp only [Bool.false_eq_true,ite_false]
    exact quiet
  · simp only [ite_true]
    exact produced_trans r tested (emitted imagePacket tested) [] _ quiet packet

end PNP.Concrete.NormalizerBlocks.SystemRows
