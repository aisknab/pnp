/-
Copyright (c) 2026 PNP Labs.

One internally derived augmentation in the matching driver. The selected
index is parsed out of the actual search response; the remaining path and
current table are assembled into the verified augmentation packet.
-/
import PNP.Concrete.NormalizerMatchingState

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister Occurrence

def prepareRouteCore : Block 9 := .seq (.action (.copy 0 8)) (.action (.pop 0))
def routeCorePrepared (r : Registers) : Registers := {r with input := r.output.tail}
theorem prepareRouteCore_exec (r : Registers) :
    Exec prepareRouteCore r.store 2 (routeCorePrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def readRouteCore : Block 9 :=
  .seq prepareRouteCore (.seq CandidatePacket.resetCore TableInit.header)
theorem readRouteCore_exec (r : Registers) :
    Exec readRouteCore r.store (10 + TableInit.headerFuel r.output.tail)
      (TableInit.readCount r.output.tail).state.store := by
  have checked := Exec.seq (prepareRouteCore_exec r)
    (Exec.seq (CandidatePacket.resetCore_exec (routeCorePrepared r)) (TableInit.header_exec r.output.tail))
  have cost : 10 + TableInit.headerFuel r.output.tail = 2 + (8 + TableInit.headerFuel r.output.tail) := by omega
  rw [cost]
  exact checked
def readRoute : Block 33 := liftCore readRouteCore
def routeRead (r : State) : State := r.withRegisters (TableInit.readCount r.registers.output.tail).state
def routeFuel (r : State) : Nat := 10 + TableInit.headerFuel r.registers.output.tail
theorem readRoute_exec (r : State) : Exec readRoute r.store (routeFuel r) (routeRead r).store :=
  liftCore_exec _ r _ _ (readRouteCore_exec r.registers)

def pathToOutput : Block 33 := liftCore (.action (.copy 8 0))
def pathOutput (r : State) : State := r.withRegisters {r.registers with output := r.registers.input}
theorem pathToOutput_exec (r : State) : Exec pathToOutput r.store 1 (pathOutput r).store :=
  liftCore_exec _ r _ _ (Exec.action _ _)
def loadTable : Block 33 := .action (.copy 0 31)
def tableLoaded (r : State) : State := r.withRegisters {r.registers with input := r.table}
theorem loadTable_exec (r : State) : Exec loadTable r.store 1 (tableLoaded r).store := by
  dsimp only [loadTable, tableLoaded, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _
def countTable : Block 33 := .action (.copy 2 31)
def tableCounted (r : State) : State := r.withRegisters {r.registers with remaining := r.table}
theorem countTable_exec (r : State) : Exec countTable r.store 1 (tableCounted r).store := by
  dsimp only [countTable, tableCounted, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _

def routeOutput (r : State) : State := pathOutput (routeRead r)
def tablePathPacked (r : State) : State := bitsPrefixed (tableLoaded (routeOutput r))
def augmentationHeaderPacked (r : State) : State := countPrefixed (tableCounted (tablePathPacked r))
def augmentationPacked (r : State) : State := packetSaved (augmentationHeaderPacked r)
def packAugmentation : Block 33 :=
  .seq readRoute <| .seq pathToOutput <| .seq loadTable <| .seq bitsPrefix <|
    .seq countTable (.seq countPrefix savePacket)
def packAugmentationFuel (r : State) : Nat :=
  TableInit.headerFuel r.registers.output.tail + 11 * r.table.length + 25
theorem packAugmentation_exec (r : State) :
    Exec packAugmentation r.store (packAugmentationFuel r) (augmentationPacked r).store := by
  have checked := Exec.seq (readRoute_exec r) <| Exec.seq (pathToOutput_exec (routeRead r)) <|
    Exec.seq (loadTable_exec (routeOutput r)) <| Exec.seq (bitsPrefix_exec (tableLoaded (routeOutput r))) <|
      Exec.seq (countTable_exec (tablePathPacked r)) <| Exec.seq (countPrefix_exec (tableCounted (tablePathPacked r)))
        (savePacket_exec (augmentationHeaderPacked r))
  change Exec packAugmentation r.store ((10 + TableInit.headerFuel r.registers.output.tail) +
    (1 + (1 + ((8 * r.table.length + 7) + (1 + ((3 * r.table.length + 4) + 1))))))
    (augmentationPacked r).store at checked
  have cost : packAugmentationFuel r = (10 + TableInit.headerFuel r.registers.output.tail) +
      (1 + (1 + ((8 * r.table.length + 7) + (1 + ((3 * r.table.length + 4) + 1))))) := by
    unfold packAugmentationFuel; omega
  rw [cost]
  exact checked

def augmentationPacket (table path : BitString) : BitString :=
  TableInit.encodeCount table.length (table ++ path)
theorem augmentationPacked_input (r : State) :
    (augmentationPacked r).registers.input =
      augmentationPacket r.table (TableInit.readCount r.registers.output.tail).state.input := rfl
theorem augmentationPacked_frame (r : State) :
    (augmentationPacked r).width = r.width ∧ (augmentationPacked r).formula = r.formula ∧
      (augmentationPacked r).table = r.table ∧ (augmentationPacked r).remaining = r.remaining := ⟨rfl,rfl,rfl,rfl⟩
theorem augmentationPacked_canonical (r : State) (entries : MatchingTable.Entries)
    (index : Nat) (path : List CNFLiteral) (table : r.table = MatchingTable.encode entries)
    (response : r.registers.output = Search.answer (.augment index path)) :
    (augmentationPacked r).registers.input = Augmentation.encode entries path := by
  rw [augmentationPacked_input, table, response]
  simp only [Search.answer, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader,
    augmentationPacket, Augmentation.encode]

def runAugmentation : Block 33 := liftSearch MatchingCall.augmentation
def augmented (r : State) : State := r.withCore (MatchingCall.augmented r.core)
def augmentationFuel (r : State) : Nat := MatchingCall.augmentationFuel r.core
theorem runAugmentation_exec (r : State) :
    Exec runAugmentation r.store (augmentationFuel r) (augmented r).store :=
  liftSearch_exec _ r _ _ (MatchingCall.augmentation_exec r.core)
def saveTable : Block 33 := .action (.copy 31 8)
def tableSaved (r : State) : State := {r with table := r.registers.output}
theorem saveTable_exec (r : State) : Exec saveTable r.store 1 (tableSaved r).store := by
  dsimp only [saveTable, tableSaved, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _

def advance : Block 33 := .seq packAugmentation (.seq runAugmentation saveTable)
def advanced (r : State) : State := tableSaved (augmented (augmentationPacked r))
def advanceFuel (r : State) : Nat := packAugmentationFuel r + (augmentationFuel (augmentationPacked r) + 1)
theorem advance_exec (r : State) : Exec advance r.store (advanceFuel r) (advanced r).store :=
  Exec.seq (packAugmentation_exec r)
    (Exec.seq (runAugmentation_exec (augmentationPacked r)) (saveTable_exec (augmented (augmentationPacked r))))
theorem advanced_frame (r : State) :
    (advanced r).width = r.width ∧ (advanced r).formula = r.formula ∧
      (advanced r).remaining = r.remaining := ⟨rfl,rfl,rfl⟩
theorem advanced_canonical (r : State) (entries : MatchingTable.Entries) (index : Nat)
    (path : List CNFLiteral) (table : r.table = MatchingTable.encode entries)
    (response : r.registers.output = Search.answer (.augment index path)) :
    (advanced r).table = MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value path)) :=
  MatchingCall.augmented_canonical (augmentationPacked r).core entries path
    (augmentationPacked_canonical r entries index path table response)

end PNP.Concrete.NormalizerBlocks.MatchingDriver
