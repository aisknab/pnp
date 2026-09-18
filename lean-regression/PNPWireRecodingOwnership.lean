import PNP.NANDWireRecodingOwnership

namespace PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.Regression

open WireObligationHistory (PhysicalOrigin)
open WireHistoryAmbientOwnership (ambientOriginals)

def identity (width : Nat) : Implementation width width :=
  (Candidate.ofDirectWireWord (.empty : Program width 0)
    ⟨fun field => .input field⟩).toImplementation

def negation : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
    (⟨fun _ => .gate 0⟩ : DirectWireWord 1 1 1)).toImplementation

def survivor : WireCarrier 1 1 1 :=
  { implementation := negation
    source := fun _ => .gate ⟨0, by decide⟩ }

def constant : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      (⟨fun _ => .constant true⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun _ => .constant true }

def prunedOriginal : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
      (⟨fun _ => .input 0⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .constant false }

def direct : WireCarrier 1 1 1 :=
  { implementation := identity 1
    source := fun field => .input field }

def empty : WireCarrier 0 0 0 :=
  { implementation := identity 0
    source := Fin.elim0 }

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    ((ledger carrier encoder decoder).live ++ (ledger carrier encoder decoder).removed).Nodup ∧
      ((ledger carrier encoder decoder).live ++ (ledger carrier encoder decoder).removed).Perm
        (ambientOriginals carrier.implementation.gateCount ++
          (ledger carrier encoder decoder).charged) :=
  (physical_ownership carrier encoder decoder).2.2.2

example {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
    {before : WireObligationHistory.State source}
    {encoder decoder : Implementation fields fields}
    (receipt : WireRecodingState.Receipt before encoder decoder) :
    receipt.ownership.charged.length = encoder.gateCount + decoder.gateCount :=
  receipt.physical_ownership.2.1

example (width encoderGates decoderGates : Nat) :
    (allocations width 0 encoderGates ++ allocations width 1 decoderGates).Nodup :=
  allocation_phases_nodup width encoderGates decoderGates

#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.encoder_positions
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.encoded_origin
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.decoder_positions
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_origin
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_charged
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_removed_length
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.ledger_partition
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.allocation_phases_nodup
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.physical_ownership
#print axioms PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.labelled_physical_ownership
#print axioms PNP.DirectWire.WireRecodingState.Receipt.physical_ownership

-- Guarded executable checks are regression evidence only, never proof authority.
def checkPartition {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) : IO Unit := do
  let actual := ledger carrier encoder decoder
  let history := actual.live ++ actual.removed
  let expected := ambientOriginals carrier.implementation.gateCount ++
    allocations carrier.implementation.gateCount 0 encoder.gateCount ++
    allocations carrier.implementation.gateCount 1 decoder.gateCount
  if history.length != expected.length then
    throw (IO.userError "the physical history has the wrong total")
  for origin in expected do
    if history.count origin != 1 then
      throw (IO.userError "an actual origin was duplicated or lost")
  if actual.charged.length != encoder.gateCount + decoder.gateCount ||
      actual.removed.length != removed carrier encoder decoder then
    throw (IO.userError "historical allocation or deletion count differs")
  let lifted := labelled carrier encoder decoder
  if lifted.charged.length != actual.charged.length ||
      lifted.removed.length != actual.removed.length ||
      lifted.live.length != actual.live.length then
    throw (IO.userError "the complete-program adapter lost an identity")

#eval show IO Unit from do
  let encoderStart := encoderLedger survivor negation
  if encoderStart.live !=
      [.original (0 : Fin 1), .allocated 0 0] then
    throw (IO.userError "the literal encoder prefix or suffix has a false origin")
  let decoderStart := decoderLedger direct negation negation
  if decoderStart.live != [.allocated 0 0, .allocated 1 0] then
    throw (IO.userError "encoder and decoder gate zero were aliased")
  let retained := ledger survivor (identity 1) (identity 1)
  if retained.live != [.original (0 : Fin 1)] ||
      !retained.charged.isEmpty || !retained.removed.isEmpty then
    throw (IO.userError "identity recoding changed a surviving original coordinate")
  let discarded := ledger constant negation negation
  if !discarded.live.isEmpty || discarded.charged !=
      [.allocated 0 0, .allocated 1 0] || discarded.removed !=
      [.allocated 0 0, .allocated 1 0] then
    throw (IO.userError "discarded recoder gates escaped historical charges")
  let pruned := ledger prunedOriginal negation negation
  if !pruned.live.isEmpty || pruned.charged.length != 2 || pruned.removed.length != 3 then
    throw (IO.userError "pruning did not retain both allocations and the old gate")
  let vacant := ledger empty (identity 0) (identity 0)
  if !vacant.live.isEmpty || !vacant.charged.isEmpty || !vacant.removed.isEmpty then
    throw (IO.userError "empty recoding fabricated a physical identity")
  checkPartition survivor (identity 1) (identity 1)
  checkPartition constant negation negation
  checkPartition prunedOriginal negation negation
  checkPartition direct negation negation
  checkPartition empty (identity 0) (identity 0)
  IO.println "RECODING_PHYSICAL_OWNERSHIP_RUNTIME_PASSED"

end PNP.DirectWire.WireCarrierRecoding.PhysicalAccounting.Regression
