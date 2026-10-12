/-
Copyright (c) 2026 PNP Labs.

Internal matching initialization. The machine reads width and formula,
counts the actual clauses, creates every empty table entry, and derives
the clause-count-plus-one round budget. No table or round count is input.
-/
import PNP.Concrete.NormalizerMatchingLoop

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister Occurrence

def initial (input : BitString) : State := ⟨Search.initial input, [], [], [], []⟩
def loadMetadata : Block 33 := liftSearch (Search.liftExploration Exploration.loader)
def metadataLoaded (input : BitString) : State := ⟨⟨Exploration.loaded input, []⟩, [], [], [], []⟩
theorem loadMetadata_exec (input : BitString) :
    Exec loadMetadata (initial input).store (Exploration.loaderFuel input) (metadataLoaded input).store :=
  liftSearch_exec _ (initial input) _ _ (Search.liftExploration_exec _ (Search.initial input) _ _
    (Exploration.loader_exec input))

def saveMetadata : Block 33 :=
  .seq (.action (.copy 29 17)) (.seq (.action (.copy 30 11)) (.action (.copy 32 20)))
def metadataSaved (r : State) : State :=
  {r with width := r.core.parent.targetIndex, formula := r.core.parent.graph.core.formula, remaining := r.core.parent.currentIndex}
theorem saveMetadata_exec (r : State) : Exec saveMetadata r.store 3 (metadataSaved r).store := by
  dsimp only [saveMetadata, metadataSaved, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, Search.State.parent]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def captured (input : BitString) : State := metadataSaved (metadataLoaded input)
theorem captured_fields (input : BitString) :
    (captured input).width = Exploration.sourceWidth input ∧
      (captured input).formula = Exploration.sourceFormula input ∧
        (captured input).remaining = List.replicate (Exploration.sourceCount input) true := by
  have fields := Exploration.loaded_fields input
  dsimp only [captured, metadataSaved, metadataLoaded, Search.State.parent]
  exact ⟨fields.1, fields.2.2.1, fields.2.1⟩

def resetTable : Block 33 := liftCore CandidatePacket.resetCore
def tableReset (r : State) : State := r.withRegisters (initialRegisters r.registers.input)
theorem resetTable_exec (r : State) : Exec resetTable r.store 8 (tableReset r).store :=
  liftCore_exec _ r _ _ (CandidatePacket.resetCore_exec r.registers)
def copyInitialCount : Block 33 := .action (.copy 1 32)
def initialCountCopied (r : State) : State := r.withRegisters {r.registers with target := r.remaining}
theorem copyInitialCount_exec (r : State) :
    Exec copyInitialCount r.store 1 (initialCountCopied r).store := by
  dsimp only [copyInitialCount, initialCountCopied, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, Search.State.parent]
  exact .action _ _
def constructEmpty : Block 33 := liftCore TableInit.loop
def emptyConstructed (r : State) : State := r.withRegisters (TableInit.built r.registers.target r.registers)
theorem constructEmpty_exec (r : State) :
    Exec constructEmpty r.store (6 * r.registers.target.length + 1) (emptyConstructed r).store :=
  liftCore_exec _ r _ _ (TableInit.loop_exec r.registers.target r.registers)
def encodeEmpty : Block 33 := liftCore ClauseQuery.pack
def emptyEncoded (r : State) : State := r.withRegisters (ClauseQuery.packed r.registers)
theorem encodeEmpty_exec (r : State) :
    Exec encodeEmpty r.store (ClauseQuery.packFuel r.registers) (emptyEncoded r).store :=
  liftCore_exec _ r _ _ (ClauseQuery.pack_exec r.registers)
def addFinalRound : Block 33 := .action (.push (Frame.frameIndex 29 (3 : Fin 4)) true)
def finalRoundAdded (r : State) : State := {r with remaining := true :: r.remaining}
theorem addFinalRound_exec (r : State) : Exec addFinalRound r.store 1 (finalRoundAdded r).store := by
  have checked := Exec.action (.push (Frame.frameIndex 29 (3 : Fin 4)) true) r.store
  simpa only [addFinalRound, finalRoundAdded, State.store, State.frame, Action.update,
    Action.instruction, Instruction.update, Frame.get_frame, Frame.set_frame,
    Store.get, Store.set, Store.indexCases] using checked

def emptyCounted (r : State) : State := initialCountCopied (tableReset r)
def emptyBuilt (r : State) : State := emptyConstructed (emptyCounted r)
def emptyPacked (r : State) : State := emptyEncoded (emptyBuilt r)
def emptyReady (r : State) : State := finalRoundAdded (tableSaved (emptyPacked r))
def buildEmpty : Block 33 :=
  .seq resetTable <| .seq copyInitialCount <| .seq constructEmpty <| .seq encodeEmpty (.seq saveTable addFinalRound)
def buildEmptyFuel (r : State) : Nat := 22 * r.remaining.length + 24
theorem buildEmpty_exec (r : State) : Exec buildEmpty r.store (buildEmptyFuel r) (emptyReady r).store := by
  have checked := Exec.seq (resetTable_exec r) <| Exec.seq (copyInitialCount_exec (tableReset r)) <|
    Exec.seq (constructEmpty_exec (emptyCounted r)) <| Exec.seq (encodeEmpty_exec (emptyBuilt r)) <|
      Exec.seq (saveTable_exec (emptyPacked r)) (addFinalRound_exec (tableSaved (emptyPacked r)))
  change Exec buildEmpty r.store
    (8 + (1 + ((6 * r.remaining.length + 1) + ((4 * (TableInit.emptyData r.remaining.length ++ []).length + 12) + (1 + 1)))))
    (emptyReady r).store at checked
  rw [List.append_nil, TableInit.emptyData_length] at checked
  have cost : buildEmptyFuel r = 8 + (1 + ((6 * r.remaining.length + 1) +
      ((4 * (4 * r.remaining.length) + 12) + (1 + 1)))) := by unfold buildEmptyFuel; omega
  rw [cost]
  exact checked

theorem emptyReady_table (r : State) :
    (emptyReady r).table = MatchingTable.encode (List.replicate r.remaining.length none) := by
  have checked := TableInit.canonical_bytes r.remaining.length r.registers.input
  change (TableInit.emptyData r.remaining.length ++ []).reverse ++ [true,false] = _
  simpa only [TableInit.canonicalResult, ClauseQuery.packed, TableInit.built,
    TableInit.canonicalHeader, List.length_replicate] using checked
theorem emptyReady_frame (r : State) :
    (emptyReady r).width = r.width ∧ (emptyReady r).formula = r.formula ∧
      (emptyReady r).remaining = true :: r.remaining := ⟨rfl,rfl,rfl⟩

def initializeBlock : Block 33 := .seq loadMetadata (.seq saveMetadata buildEmpty)
def initialized (input : BitString) : State := emptyReady (captured input)
def initializeFuel (input : BitString) : Nat := Exploration.loaderFuel input + (3 + buildEmptyFuel (captured input))
theorem initialize_exec (input : BitString) :
    Exec initializeBlock (initial input).store (initializeFuel input) (initialized input).store :=
  Exec.seq (loadMetadata_exec input) (Exec.seq (saveMetadata_exec (metadataLoaded input)) (buildEmpty_exec (captured input)))
theorem initialized_fields (input : BitString) :
    (initialized input).width = Exploration.sourceWidth input ∧
      (initialized input).formula = Exploration.sourceFormula input ∧
        (initialized input).table = MatchingTable.encode (List.replicate (Exploration.sourceCount input) none) ∧
          (initialized input).remaining.length = Exploration.sourceCount input + 1 := by
  have captured := captured_fields input
  have preserved := emptyReady_frame (MatchingDriver.captured input)
  have table := emptyReady_table (MatchingDriver.captured input)
  rw [captured.2.2, List.length_replicate] at table
  refine ⟨preserved.1.trans captured.1, preserved.2.1.trans captured.2.1, table, ?_⟩
  change (emptyReady (MatchingDriver.captured input)).remaining.length = _
  rw [preserved.2.2, List.length_cons, captured.2.2, List.length_replicate]
theorem initializeFuel_bound (input : BitString) : initializeFuel input ≤ 122 * input.length + 227 := by
  have loader := Exploration.loaderFuel_bound input
  have counts := (Exploration.source_sizes input).2.2.2
  unfold initializeFuel buildEmptyFuel
  rw [(captured_fields input).2.2, List.length_replicate]
  omega

def encode (variables : Nat) (clauses : List (List CNFLiteral)) : BitString :=
  TableInit.encodeCount variables
    (TableInit.encodeCount (GraphQuery.clauseData clauses).length (GraphQuery.clauseData clauses))
theorem input_fields (variables : Nat) (clauses : List (List CNFLiteral)) :
    Exploration.sourceWidth (encode variables clauses) = List.replicate variables true ∧
      Exploration.sourceFormula (encode variables clauses) = GraphQuery.clauseData clauses ∧
        Exploration.sourceCount (encode variables clauses) = clauses.length := by
  have formula := BatchPacket.core_canonical (GraphQuery.clauseData clauses) []
  rw [List.append_nil] at formula
  simp only [Exploration.sourceWidth, Exploration.sourceFormula, Exploration.sourceTail, Exploration.sourceCount,
    encode, BatchPacket.header_canonical, TableInit.canonicalHeader, formula, ClauseCount.count_formula]
  repeat constructor
theorem initialized_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    Canonical variables clauses (List.replicate clauses.length none) (initialized (encode variables clauses)) ∧
      (initialized (encode variables clauses)).remaining.length = clauses.length + 1 := by
  have raw := initialized_fields (encode variables clauses)
  have data := input_fields variables clauses
  rw [data.2.2] at raw
  exact ⟨⟨raw.1.trans data.1, raw.2.1.trans data.2.1, raw.2.2.1⟩, raw.2.2.2⟩

end PNP.Concrete.NormalizerBlocks.MatchingDriver
