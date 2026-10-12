/-
Copyright (c) 2026 PNP Labs.

Protected state for the complete matching driver. Width, formula, current
table and remaining rounds are outside both called machines' scratch
registers. The search packet is assembled from those fields on every call.
-/
import PNP.Concrete.NormalizerMatchingPackets

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister Occurrence

structure State where
  core : Search.State
  width : BitString
  formula : BitString
  table : BitString
  remaining : BitString
def State.frame (r : State) : Store 4 := .cons r.width (.cons r.formula (.cons r.table (.cons r.remaining .nil)))
def State.store (r : State) : Store 33 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : Search.State) : State := {r with core := core}
def State.withRegisters (r : State) (registers : Registers) : State :=
  r.withCore (r.core.withRegisters registers)
def liftSearch (body : Block 29) : Block 33 := Frame.block 4 body
def liftCore (body : Block 9) : Block 33 := liftSearch (Search.liftCore body)
theorem liftSearch_exec (body : Block 29) (r : State) (fuel : Nat) (after : Search.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftSearch body) r.store fuel (r.withCore after).store := Frame.execution checked r.frame
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftSearch_exec _ r _ _ (Search.liftCore_exec body r.core fuel after checked)

def countPrefix : Block 33 := liftCore MatchingPacket.prependCount
def countPrefixed (r : State) : State := r.withRegisters (MatchingPacket.countPrepended r.registers)
theorem countPrefix_exec (r : State) :
    Exec countPrefix r.store (MatchingPacket.countFuel r.registers) (countPrefixed r).store :=
  liftCore_exec _ r _ _ (MatchingPacket.prependCount_exec r.registers)
def bitsPrefix : Block 33 := liftCore MatchingPacket.prependBits
def bitsPrefixed (r : State) : State := r.withRegisters (MatchingPacket.bitsPrepended r.registers)
theorem bitsPrefix_exec (r : State) :
    Exec bitsPrefix r.store (MatchingPacket.bitsFuel r.registers) (bitsPrefixed r).store :=
  liftCore_exec _ r _ _ (MatchingPacket.prependBits_exec r.registers)

def seedTable : Block 33 := .seq (.action (.copy 8 31)) (.action (.copy 2 31))
def tableSeeded (r : State) : State := r.withRegisters {r.registers with output := r.table, remaining := r.table}
theorem seedTable_exec (r : State) : Exec seedTable r.store 2 (tableSeeded r).store := by
  dsimp only [seedTable, tableSeeded, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact Exec.seq (.action _ _) (.action _ _)
def loadFormula : Block 33 := .action (.copy 0 30)
def formulaLoaded (r : State) : State := r.withRegisters {r.registers with input := r.formula}
theorem loadFormula_exec (r : State) : Exec loadFormula r.store 1 (formulaLoaded r).store := by
  dsimp only [loadFormula, formulaLoaded, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _
def countFormula : Block 33 := .action (.copy 2 30)
def formulaCounted (r : State) : State := r.withRegisters {r.registers with remaining := r.formula}
theorem countFormula_exec (r : State) : Exec countFormula r.store 1 (formulaCounted r).store := by
  dsimp only [countFormula, formulaCounted, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _
def countWidth : Block 33 := .action (.copy 2 29)
def widthCounted (r : State) : State := r.withRegisters {r.registers with remaining := r.width}
theorem countWidth_exec (r : State) : Exec countWidth r.store 1 (widthCounted r).store := by
  dsimp only [countWidth, widthCounted, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _
def savePacket : Block 33 := .action (.copy 0 8)
def packetSaved (r : State) : State := r.withRegisters {r.registers with input := r.registers.output}
theorem savePacket_exec (r : State) : Exec savePacket r.store 1 (packetSaved r).store := by
  dsimp only [savePacket, packetSaved, State.store, State.frame, State.withRegisters, State.withCore, State.registers, Search.State.store, Search.State.frame, Search.State.withRegisters, Search.State.withCore, Search.State.registers, Exploration.State.store, Exploration.State.frame, Exploration.State.withRegisters, Exploration.State.withCore, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.withRegisters, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _

def tablePacked (r : State) : State := countPrefixed (tableSeeded r)
def formulaPacked (r : State) : State := bitsPrefixed (formulaLoaded (tablePacked r))
def formulaHeaderPacked (r : State) : State := countPrefixed (formulaCounted (formulaPacked r))
def widthHeaderPacked (r : State) : State := countPrefixed (widthCounted (formulaHeaderPacked r))
def searchPacked (r : State) : State := packetSaved (widthHeaderPacked r)
def packSearch : Block 33 :=
  .seq seedTable <| .seq countPrefix <| .seq loadFormula <| .seq bitsPrefix <|
    .seq countFormula <| .seq countPrefix <| .seq countWidth (.seq countPrefix savePacket)
def packSearchFuel (r : State) : Nat := 3 * r.table.length + 11 * r.formula.length + 3 * r.width.length + 25
theorem packSearch_exec (r : State) : Exec packSearch r.store (packSearchFuel r) (searchPacked r).store := by
  have checked := Exec.seq (seedTable_exec r) <| Exec.seq (countPrefix_exec (tableSeeded r)) <|
    Exec.seq (loadFormula_exec (tablePacked r)) <| Exec.seq (bitsPrefix_exec (formulaLoaded (tablePacked r))) <|
      Exec.seq (countFormula_exec (formulaPacked r)) <| Exec.seq (countPrefix_exec (formulaCounted (formulaPacked r))) <|
        Exec.seq (countWidth_exec (formulaHeaderPacked r)) <|
          Exec.seq (countPrefix_exec (widthCounted (formulaHeaderPacked r))) (savePacket_exec (widthHeaderPacked r))
  change Exec packSearch r.store (2 + ((3 * r.table.length + 4) + (1 + ((8 * r.formula.length + 7) + (1 + ((3 * r.formula.length + 4) + (1 + ((3 * r.width.length + 4) + (1))))))))) (searchPacked r).store at checked
  have cost : packSearchFuel r = 2 + ((3 * r.table.length + 4) + (1 + ((8 * r.formula.length + 7) + (1 + ((3 * r.formula.length + 4) + (1 + ((3 * r.width.length + 4) + (1)))))))) := by
    unfold packSearchFuel; omega
  rw [cost]
  exact checked

def searchPacket (width formula table : BitString) : BitString :=
  TableInit.encodeCount width.length (TableInit.encodeCount formula.length
    (formula ++ TableInit.encodeCount table.length table))
theorem searchPacked_input (r : State) :
    (searchPacked r).registers.input = searchPacket r.width r.formula r.table := rfl
theorem searchPacked_frame (r : State) :
    (searchPacked r).width = r.width ∧ (searchPacked r).formula = r.formula ∧
      (searchPacked r).table = r.table ∧ (searchPacked r).remaining = r.remaining := ⟨rfl,rfl,rfl,rfl⟩
theorem searchPacket_canonical (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    searchPacket (List.replicate variables true) (GraphQuery.clauseData clauses) (MatchingTable.encode entries) =
      Exploration.encode variables clauses entries := by
  simp only [searchPacket, Exploration.encode, List.length_replicate, List.append_nil]

def runSearch : Block 33 := liftSearch MatchingCall.search
def searched (r : State) : State := r.withCore (MatchingCall.searched r.core)
def searchFuel (r : State) : Nat := MatchingCall.searchFuel r.core
theorem runSearch_exec (r : State) : Exec runSearch r.store (searchFuel r) (searched r).store :=
  liftSearch_exec _ r _ _ (MatchingCall.search_exec r.core)
def search : Block 33 := .seq packSearch runSearch
def searchResult (r : State) : State := searched (searchPacked r)
def searchSteps (r : State) : Nat := packSearchFuel r + searchFuel (searchPacked r)
theorem search_exec (r : State) : Exec search r.store (searchSteps r) (searchResult r).store :=
  Exec.seq (packSearch_exec r) (runSearch_exec (searchPacked r))
theorem searchResult_output (r : State) :
    (searchResult r).registers.output = (Search.result (searchPacket r.width r.formula r.table)).registers.output := rfl
theorem searchResult_frame (r : State) :
    (searchResult r).width = r.width ∧ (searchResult r).formula = r.formula ∧
      (searchResult r).table = r.table ∧ (searchResult r).remaining = r.remaining := ⟨rfl,rfl,rfl,rfl⟩

end PNP.Concrete.NormalizerBlocks.MatchingDriver
