/-
Copyright (c) 2026 PNP Labs.

Actual physical ownership through literal carrier recoding. The encoder and
decoder receive disjoint derived phase identities, and both normalization maps
come from the existing physical compiler. A removed allocation remains charged.

This local accounting does not supply full manuscript profiles, a successful
global strategy, complete mixed-program integration or polynomial execution.
-/

import PNP.NANDWireRecodingState
import PNP.NANDWireOpenPrimitiveOwnership

namespace PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting

open WireObligationHistory (PhysicalOrigin PhysicalOwnership)
open PhysicalGateProvenance (normalizedOrigin)
open WireHistoryAmbientOwnership (ambientOriginals)
open WireDescendantHistory (PersistentOwnership originalOrigins)
open WireOpenProgram.PrimitiveOwnership (lift lift_injective)

variable {inputs outputs fields : Nat}

/-- Separate local phases are derived here, never supplied by the caller. -/
def allocations (sourceGates phase count : Nat) : List (PhysicalOrigin sourceGates) :=
  List.ofFn (fun gate : Fin count => .allocated phase gate.val)

def encoderLedger (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields) :
    PhysicalOwnership carrier.implementation.gateCount
      (appendMap carrier encoder).implementation.gateCount :=
  (PhysicalOwnership.initial carrier.implementation.gateCount).append 0 encoder.gateCount

def encodedLedger (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields) :
    PhysicalOwnership carrier.implementation.gateCount
      (encoded carrier encoder).implementation.gateCount :=
  PhysicalOwnership.normalize (appendMap carrier encoder).exposed (encoderLedger carrier encoder)

def decoderLedger (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    PhysicalOwnership carrier.implementation.gateCount
      (expanded carrier encoder decoder).implementation.gateCount :=
  (encodedLedger carrier encoder).append 1 decoder.gateCount

def ledger (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    PhysicalOwnership carrier.implementation.gateCount
      (result carrier encoder decoder).implementation.gateCount :=
  PhysicalOwnership.normalize (expanded carrier encoder decoder).exposed
    (decoderLedger carrier encoder decoder)

/-- Coordinates before the first normalizer follow the actual concatenated word. -/
theorem encoder_positions (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields) :
    (∀ gate : Fin carrier.implementation.gateCount,
      (encoderLedger carrier encoder).origin (Fin.castAdd encoder.gateCount gate) =
        .original gate) ∧
    (∀ gate : Fin encoder.gateCount,
      (encoderLedger carrier encoder).origin
        (Fin.natAdd carrier.implementation.gateCount gate) = .allocated 0 gate.val) := by
  constructor
  · intro gate
    exact (PhysicalOwnership.initial carrier.implementation.gateCount).append_origin_left
      0 encoder.gateCount gate
  · intro gate
    exact (PhysicalOwnership.initial carrier.implementation.gateCount).append_origin_right
      0 encoder.gateCount gate

theorem encoded_origin (carrier : WireCarrier inputs outputs fields)
    (encoder : Implementation fields fields)
    (gate : Fin (encoded carrier encoder).implementation.gateCount) :
    (encodedLedger carrier encoder).origin gate =
      (encoderLedger carrier encoder).origin
        (normalizedOrigin (appendMap carrier encoder).exposed gate) := rfl

/-- Decoder allocations use phase one even when their local positions coincide
with phase-zero encoder allocations. The surviving prefix retains its map. -/
theorem decoder_positions (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (∀ gate : Fin (encoded carrier encoder).implementation.gateCount,
      (decoderLedger carrier encoder decoder).origin (Fin.castAdd decoder.gateCount gate) =
        (encodedLedger carrier encoder).origin gate) ∧
    (∀ gate : Fin decoder.gateCount,
      (decoderLedger carrier encoder decoder).origin
        (Fin.natAdd (encoded carrier encoder).implementation.gateCount gate) =
          .allocated 1 gate.val) := by
  constructor
  · intro gate
    exact (encodedLedger carrier encoder).append_origin_left 1 decoder.gateCount gate
  · intro gate
    exact (encodedLedger carrier encoder).append_origin_right 1 decoder.gateCount gate

theorem ledger_origin (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields)
    (gate : Fin (result carrier encoder decoder).implementation.gateCount) :
    (ledger carrier encoder decoder).origin gate =
      (decoderLedger carrier encoder decoder).origin
        (normalizedOrigin (expanded carrier encoder decoder).exposed gate) := rfl

/-- Both literal allocations remain charged, including gates later removed. -/
theorem ledger_charged (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (ledger carrier encoder decoder).charged =
      allocations carrier.implementation.gateCount 0 encoder.gateCount ++
        allocations carrier.implementation.gateCount 1 decoder.gateCount := rfl

theorem ledger_removed_length (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (ledger carrier encoder decoder).removed.length = removed carrier encoder decoder := by
  have first := PhysicalOwnership.normalize_removed_length
    (appendMap carrier encoder).exposed (encoderLedger carrier encoder)
  have second := PhysicalOwnership.normalize_removed_length
    (expanded carrier encoder decoder).exposed (decoderLedger carrier encoder decoder)
  change (encodedLedger carrier encoder).removed.length =
    0 + (runPhysicalNormalization (appendMap carrier encoder).exposed).trace.savedGates at first
  change (ledger carrier encoder decoder).removed.length =
    (encodedLedger carrier encoder).removed.length +
      (runPhysicalNormalization (expanded carrier encoder decoder).exposed).trace.savedGates at second
  rw [first, Nat.zero_add] at second
  exact second

private theorem swap_suffixes {alpha : Type} (first middle last : List alpha) :
    ((first ++ middle) ++ last).Perm ((first ++ last) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := last)).append_left first

private theorem append_partition {sourceGates physicalGates : Nat}
    (before : PhysicalOwnership sourceGates physicalGates) (phase count : Nat) :
    ((before.append phase count).live ++ (before.append phase count).removed).Perm
      ((before.live ++ before.removed) ++ allocations sourceGates phase count) := by
  change ((before.append phase count).live ++ before.removed).Perm _
  rw [PhysicalOwnership.append_live]
  exact swap_suffixes _ _ _

theorem ledger_partition (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    ((ledger carrier encoder decoder).live ++ (ledger carrier encoder decoder).removed).Perm
      (ambientOriginals carrier.implementation.gateCount ++
        (ledger carrier encoder decoder).charged) := by
  have first := PhysicalOwnership.normalize_partition
    (appendMap carrier encoder).exposed (encoderLedger carrier encoder)
  have middle := append_partition (encodedLedger carrier encoder) 1 decoder.gateCount
  have last := PhysicalOwnership.normalize_partition
    (expanded carrier encoder decoder).exposed (decoderLedger carrier encoder decoder)
  have combined := last.trans (middle.trans
    (first.append_right (allocations carrier.implementation.gateCount 1 decoder.gateCount)))
  change ((ledger carrier encoder decoder).live ++ (ledger carrier encoder decoder).removed).Perm
    (((encoderLedger carrier encoder).live ++ []) ++
      allocations carrier.implementation.gateCount 1 decoder.gateCount) at combined
  rw [List.append_nil] at combined
  have firstLive : (encoderLedger carrier encoder).live =
      ambientOriginals carrier.implementation.gateCount ++
        allocations carrier.implementation.gateCount 0 encoder.gateCount :=
    PhysicalOwnership.append_live (PhysicalOwnership.initial carrier.implementation.gateCount)
      0 encoder.gateCount
  rw [firstLive, List.append_assoc] at combined
  rw [ledger_charged]
  exact combined

private theorem ofFn_nodup {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (injective : Function.Injective value) :
    (List.ofFn value).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right leftBound rightBound before same
  have leftValid : left < width := by simpa only [List.length_ofFn] using leftBound
  have rightValid : right < width := by simpa only [List.length_ofFn] using rightBound
  have sameValue : value ⟨left, leftValid⟩ = value ⟨right, rightValid⟩ := by
    simpa only [List.getElem_ofFn] using same
  have sameIndex : left = right := congrArg Fin.val (injective sameValue)
  omega

private theorem allocations_nodup (sourceGates phase count : Nat) :
    (allocations sourceGates phase count).Nodup := by
  apply ofFn_nodup
  intro left right same
  exact Fin.ext (PhysicalOrigin.allocated.inj same).2

theorem allocation_phases_nodup (sourceGates encoderGates decoderGates : Nat) :
    (allocations sourceGates 0 encoderGates ++ allocations sourceGates 1 decoderGates).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨allocations_nodup _ _ _, allocations_nodup _ _ _, ?_⟩
  intro first firstMember second secondMember same
  obtain ⟨left, leftAt⟩ := List.mem_ofFn.mp firstMember
  obtain ⟨right, rightAt⟩ := List.mem_ofFn.mp secondMember
  have impossible : (0 : Nat) = 1 :=
    (PhysicalOrigin.allocated.inj (leftAt.trans (same.trans rightAt.symm))).1
  cases impossible

theorem physical_ownership (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (ledger carrier encoder decoder).live.length =
        (result carrier encoder decoder).implementation.gateCount ∧
    (ledger carrier encoder decoder).charged.length = encoder.gateCount + decoder.gateCount ∧
    (ledger carrier encoder decoder).removed.length = removed carrier encoder decoder ∧
    ((ledger carrier encoder decoder).live ++ (ledger carrier encoder decoder).removed).Nodup ∧
    ((ledger carrier encoder decoder).live ++ (ledger carrier encoder decoder).removed).Perm
      (ambientOriginals carrier.implementation.gateCount ++
        (ledger carrier encoder decoder).charged) := by
  have totalDistinct :
      (ambientOriginals carrier.implementation.gateCount ++
        (ledger carrier encoder decoder).charged).Nodup := by
    rw [ledger_charged]
    apply List.nodup_append.mpr
    refine ⟨ofFn_nodup PhysicalOrigin.original
      (fun _ _ same => PhysicalOrigin.original.inj same), allocation_phases_nodup _ _ _, ?_⟩
    intro old oldMember fresh freshMember same
    obtain ⟨gate, original⟩ := List.mem_ofFn.mp oldMember
    rcases List.mem_append.mp freshMember with encoderMember | decoderMember
    · obtain ⟨localGate, allocated⟩ := List.mem_ofFn.mp encoderMember
      have impossible := original.trans (same.trans allocated.symm)
      cases impossible
    · obtain ⟨localGate, allocated⟩ := List.mem_ofFn.mp decoderMember
      have impossible := original.trans (same.trans allocated.symm)
      cases impossible
  refine ⟨List.length_ofFn, ?_, ledger_removed_length carrier encoder decoder,
    (ledger_partition carrier encoder decoder).symm.nodup totalDistinct,
    ledger_partition carrier encoder decoder⟩
  rw [ledger_charged, List.length_append]
  simp only [allocations, List.length_ofFn]

/-- Lift the actual map into the established complete-program local interface. -/
def labelled (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    PersistentOwnership carrier.implementation.gateCount
      (result carrier encoder decoder).implementation.gateCount :=
  ⟨fun gate => lift ((ledger carrier encoder decoder).origin gate),
    (ledger carrier encoder decoder).charged.map lift,
    (ledger carrier encoder decoder).removed.map lift⟩

theorem labelled_live (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (labelled carrier encoder decoder).live = (ledger carrier encoder decoder).live.map lift := by
  rw [PhysicalOwnership.live, List.map_ofFn]
  rfl

theorem labelled_physical_ownership (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (labelled carrier encoder decoder).live.length =
        (result carrier encoder decoder).implementation.gateCount ∧
    (labelled carrier encoder decoder).charged.length = encoder.gateCount + decoder.gateCount ∧
    (labelled carrier encoder decoder).removed.length = removed carrier encoder decoder ∧
    ((labelled carrier encoder decoder).live ++ (labelled carrier encoder decoder).removed).Nodup ∧
    ((labelled carrier encoder decoder).live ++ (labelled carrier encoder decoder).removed).Perm
      (originalOrigins carrier.implementation.gateCount ++
        (labelled carrier encoder decoder).charged) := by
  have checked := physical_ownership carrier encoder decoder
  have distinct : (((ledger carrier encoder decoder).live ++
      (ledger carrier encoder decoder).removed).map lift).Nodup :=
    List.Pairwise.map lift
      (fun _ _ different same => different (lift_injective same)) checked.2.2.2.1
  have partition := checked.2.2.2.2.map lift
  simp only [List.map_append] at distinct partition
  have originals : (ambientOriginals carrier.implementation.gateCount).map lift =
      originalOrigins carrier.implementation.gateCount := by
    rw [ambientOriginals, List.map_ofFn]
    rfl
  rw [originals] at partition
  refine ⟨List.length_ofFn, ?_, ?_, ?_, ?_⟩
  · change ((ledger carrier encoder decoder).charged.map lift).length = _
    rw [List.length_map]
    exact checked.2.1
  · change ((ledger carrier encoder decoder).removed.map lift).length = _
    rw [List.length_map]
    exact checked.2.2.1
  · rw [labelled_live]
    exact distinct
  · rw [labelled_live]
    exact partition

end PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting

namespace PNP.DirectWire.WireRecodingState

open WireObligationHistory (State)
open WireDescendantHistory (PersistentOwnership originalOrigins)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
variable {before : State source} {encoder decoder : Implementation fields fields}

def Receipt.ownership (receipt : Receipt before encoder decoder) :
    PersistentOwnership before.current.implementation.gateCount
      receipt.next.current.implementation.gateCount :=
  WireCarrierRecoding.PhysicalAccounting.labelled before.current encoder decoder

theorem Receipt.physical_ownership (receipt : Receipt before encoder decoder) :
    receipt.ownership.live.length = receipt.next.current.implementation.gateCount ∧
    receipt.ownership.charged.length = encoder.gateCount + decoder.gateCount ∧
    receipt.ownership.removed.length = WireCarrierRecoding.removed before.current encoder decoder ∧
    (receipt.ownership.live ++ receipt.ownership.removed).Nodup ∧
    (receipt.ownership.live ++ receipt.ownership.removed).Perm
      (originalOrigins before.current.implementation.gateCount ++ receipt.ownership.charged) :=
  WireCarrierRecoding.PhysicalAccounting.labelled_physical_ownership before.current encoder decoder

end PNP.DirectWire.WireRecodingState
