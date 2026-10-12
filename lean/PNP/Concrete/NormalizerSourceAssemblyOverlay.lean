/-
Copyright (c) 2026 PNP Labs.

A byte-exact overlay from the completed checker into the assembly register
layout. Two fresh packet registers extend the state; recovery data is not
recomputed or dropped.
-/
import PNP.Concrete.NormalizerSourceCheckPolynomial
import PNP.Concrete.NormalizerSystemAssembly

namespace PNP.Concrete.NormalizerBlocks.SourceAssembly
open BitRegister Occurrence
abbrev State := SystemAssembly.State

def word (r : CutDriver.State) (index : Fin 36) : BitString := r.store.get index
def coefficientView (r : CutDriver.State) : Coefficient.State :=
  ⟨⟨⟨⟨r.registers,word r 9,word r 10,word r 11,word r 12⟩,
      word r 13,word r 14,word r 15⟩,word r 16,word r 17,word r 18⟩,
    word r 19,word r 20,word r 21,word r 22,word r 23⟩
def rowsView (r : CutDriver.State) : SystemRows.State :=
  ⟨coefficientView r,word r 24,word r 25,word r 26,word r 27,word r 28⟩
def recovery (r : CutDriver.State) : Store 7 :=
  .cons r.core.width (.cons r.core.formula (.cons r.core.table (.cons r.core.remaining
    (.cons r.trace (.cons r.clauses (.cons r.variables .nil))))))
def packetFrame : Store 2 := .cons [] (.cons [] .nil)
def extended (r : CutDriver.State) : State := ⟨rowsView r,recovery r,[],[]⟩

theorem extended_store (r : CutDriver.State) :
    (extended r).store = Frame.join r.store packetFrame := by
  dsimp only [extended,rowsView,coefficientView,word,recovery,packetFrame,
    SystemAssembly.State.store,SystemAssembly.State.frame,SystemRows.State.store,SystemRows.State.frame,
    Coefficient.State.store,Coefficient.State.frame,CacheMode.State.store,CacheMode.State.frame,
    DenseClauses.State.store,DenseClauses.State.frame,CompactClause.State.store,CompactClause.State.frame,
    CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,
    ParentQuery.State.store,ParentQuery.State.frame,ParentQuery.State.registers,
    EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,
    Registers.store,Frame.join,Store.get,Store.indexCases]
theorem extended_registers (r : CutDriver.State) : (extended r).registers = r.registers := rfl
theorem extended_recovery (r : CutDriver.State) : (extended r).recovery = recovery r := rfl
theorem extended_inputs (r : CutDriver.State) :
    (extended r).core.buffer = SourceCacheDriver.literals r ∧
    (extended r).core.count = SourceCacheDriver.owners r ∧
    (extended r).core.remaining = SourceCacheDriver.slots r ∧
    (extended r).core.counter = SourceCacheDriver.modes r ∧
    (extended r).core.core.row = SourceCheck.candidate r ∧
    (extended r).core.rows = SourceCacheDriver.rows r := by
  dsimp only [SourceCacheDriver.literals,SourceCacheDriver.owners,SourceCacheDriver.slots,
    SourceCacheDriver.modes,SourceCacheDriver.rows,ModeCacheDriver.literals,ModeCacheDriver.owners,
    OwnerCacheDriver.literals,SourceCheck.candidate,CutDriver.State.selection,extended,rowsView,coefficientView,word,recovery,packetFrame,
    SystemAssembly.State.store,SystemAssembly.State.frame,SystemRows.State.store,SystemRows.State.frame,
    Coefficient.State.store,Coefficient.State.frame,CacheMode.State.store,CacheMode.State.frame,
    DenseClauses.State.store,DenseClauses.State.frame,CompactClause.State.store,CompactClause.State.frame,
    CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,
    ParentQuery.State.store,ParentQuery.State.frame,ParentQuery.State.registers,
    EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,
    Registers.store,Frame.join,Store.get,Store.indexCases]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store
theorem extended_bounded (r : CutDriver.State) (n : Nat) (bounded : r.store.Bounded n) :
    (extended r).store.Bounded n := by
  rw [extended_store]
  exact Frame.join_bounded r.store packetFrame bounded ⟨Nat.zero_le n,⟨Nat.zero_le n,True.intro⟩⟩
def liftCheck (body : Block 36) : Block 38 := Frame.block 2 body
theorem liftCheck_exec (body : Block 36) (before after : CutDriver.State) (fuel : Nat)
    (checked : Exec body before.store fuel after.store) :
    Exec (liftCheck body) (extended before).store fuel (extended after).store := by
  rw [extended_store,extended_store]
  exact Frame.execution checked packetFrame

end PNP.Concrete.NormalizerBlocks.SourceAssembly
