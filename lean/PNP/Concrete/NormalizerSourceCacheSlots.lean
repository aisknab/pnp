/-
Copyright (c) 2026 PNP Labs.

Complete slots from retained owners and modes without recomputing either.
Cache fields use protected registers outside the existing sixteen-register
lookup scratch; original cut data and dense literal bytes remain available.
-/
import PNP.Concrete.NormalizerCacheSlots
import PNP.Concrete.NormalizerModeCachePolynomial

namespace PNP.Concrete.NormalizerBlocks.SourceCacheDriver
open BitRegister
abbrev State := CutDriver.State

def modes (r : State) : BitString := r.core.core.core.core.output
def slots (r : State) : BitString := r.core.core.core.core.active
def owners (r : State) : BitString := ModeCacheDriver.owners r
def literals (r : State) : BitString := ModeCacheDriver.literals r
def columns (r : State) : BitString := r.core.core.core.core.skipped
def rows (r : State) : BitString := r.core.core.core.core.trace
def withFields (r : State) (data : Extraction.State) : State :=
  {r with core := {r.core with core := {r.core.core with core := {r.core.core.core with core := data}}}}
def stashModes : Block 36 := .action (.copy 26 8)
def modesStashed (r : State) : State := withFields r {r.core.core.core.core with output := r.registers.output}
theorem stashModes_exec (r : State) : Exec stashModes r.store 1 (modesStashed r).store := by
  dsimp only [stashModes,modesStashed,withFields,CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.parent,Extraction.State.registers,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Occurrence.Registers.store,Frame.join]
  exact .action _ _
theorem withDense_cache (r : State) (after : DenseClauses.State) :
    modes (PreparedDriver.withDense r after) = modes r ∧
    owners (PreparedDriver.withDense r after) = owners r ∧
    literals (PreparedDriver.withDense r after) = literals r := ⟨rfl,rfl,rfl⟩
def loadSlots : Block 36 := .seq (.action (.copy 13 26)) (.action (.copy 14 27))
def slotsLoaded (r : State) : State :=
  PreparedDriver.withDense r {PreparedDriver.denseView r with formula := modes r, remaining := owners r}
theorem loadSlots_exec (r : State) : Exec loadSlots r.store 2 (slotsLoaded r).store := by
  dsimp only [loadSlots,slotsLoaded,modes,owners,ModeCacheDriver.owners,PreparedDriver.withDense,
    PreparedDriver.denseView,PreparedDriver.graphDense,PreparedDriver.denseGraph,
    CutDriver.State.withSelection,CutDriver.State.selection,CutDriver.State.store,CutDriver.State.frame,
    MatchingDriver.State.store,MatchingDriver.State.frame,Search.State.store,Search.State.frame,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Extraction.State.store,Extraction.State.frame,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    EdgeKinds.State.store,EdgeKinds.State.frame,ForwardEdge.State.store,ForwardEdge.State.frame,
    Occurrence.Registers.store,Frame.join]
  exact .seq (.action _ _) (.action _ _)
def setupSlots : Block 36 := .seq stashModes loadSlots
def slotsReady (r : State) : State := slotsLoaded (modesStashed r)
theorem setupSlots_exec (r : State) : Exec setupSlots r.store 3 (slotsReady r).store :=
  Exec.seq (stashModes_exec r) (loadSlots_exec (modesStashed r))
theorem slotsReady_fields (r : State) :
    (PreparedDriver.denseView (slotsReady r)).formula = r.registers.output ∧
    (PreparedDriver.denseView (slotsReady r)).remaining = owners r := ⟨rfl,rfl⟩
theorem slotsReady_frame (r : State) :
    (slotsReady r).core.width = r.core.width ∧ (slotsReady r).core.formula = r.core.formula ∧
    (slotsReady r).core.table = r.core.table ∧ (slotsReady r).trace = r.trace ∧
    (slotsReady r).clauses = r.clauses ∧ (slotsReady r).variables = r.variables :=
  PreparedDriver.withDense_frame (modesStashed r) _
def deriveSlots : Block 36 := .seq setupSlots (PreparedDriver.liftDense CacheSlots.call)
def slotsDerived (r : State) : State :=
  PreparedDriver.withDense (slotsReady r) (CacheSlots.called (PreparedDriver.denseView (slotsReady r)))
def slotsSteps (r : State) : Nat := 3 + CacheSlots.callSteps (PreparedDriver.denseView (slotsReady r))
theorem deriveSlots_exec (r : State) : Exec deriveSlots r.store (slotsSteps r) (slotsDerived r).store :=
  Exec.seq (setupSlots_exec r)
    (PreparedDriver.liftDense_exec _ (slotsReady r) _ _ (CacheSlots.call_exec _))
theorem slotsDerived_cache (r : State) :
    modes (slotsDerived r) = r.registers.output ∧ owners (slotsDerived r) = owners r ∧
    literals (slotsDerived r) = literals r := withDense_cache (slotsReady r) _
theorem slotsDerived_frame (r : State) :
    (slotsDerived r).core.width = r.core.width ∧ (slotsDerived r).core.formula = r.core.formula ∧
    (slotsDerived r).core.table = r.core.table ∧ (slotsDerived r).trace = r.trace ∧
    (slotsDerived r).clauses = r.clauses ∧ (slotsDerived r).variables = r.variables := by
  have before := slotsReady_frame r
  have after := PreparedDriver.withDense_frame (slotsReady r) (CacheSlots.called (PreparedDriver.denseView (slotsReady r)))
  exact ⟨after.1.trans before.1,after.2.1.trans before.2.1,after.2.2.1.trans before.2.2.1,
    after.2.2.2.1.trans before.2.2.2.1,after.2.2.2.2.1.trans before.2.2.2.2.1,
    after.2.2.2.2.2.trans before.2.2.2.2.2⟩
theorem slotsDerived_output (r : State) (modeData : MatchingTable.Entries) (ownerData : List CNFLiteral)
    (modeRead : r.registers.output = MatchingTable.encode modeData)
    (ownerRead : owners r = SearchVertices.encodeVertices ownerData) :
    (slotsDerived r).registers.output = MatchingTable.encode (CacheSlots.values modeData ownerData) := by
  rw [slotsDerived,PreparedDriver.withDense_registers]
  exact CacheSlots.called_canonical (PreparedDriver.denseView (slotsReady r)) modeData ownerData
    ((slotsReady_fields r).1.trans modeRead) ((slotsReady_fields r).2.trans ownerRead)

attribute [local irreducible] CutDriver.State.store
def slotsBound : NatPolynomial := .add (.constant 3) (CacheSlots.callBound.substitute (.linear 1 3))
theorem slotsBound_eval (n : Nat) : slotsBound.eval n = 3 + CacheSlots.callBound.eval (n + 3) := by
  change 3 + (CacheSlots.callBound.substitute (.linear 1 3)).eval n = _
  rw [NatPolynomial.eval_substitute]
  change 3 + CacheSlots.callBound.eval (1 * n + 3) = _
  rw [Nat.one_mul]
theorem slotsSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    slotsSteps r ≤ slotsBound.eval n := by
  have prepared := (setupSlots_exec r).bounded n bounded
  have scratch := PreparedDriver.denseView_bounded (slotsReady r) (n + 3) prepared
  have complete := CacheSlots.callSteps_bound (PreparedDriver.denseView (slotsReady r)) (n + 3) scratch
  rw [slotsBound_eval]
  exact Nat.add_le_add_left complete 3

end PNP.Concrete.NormalizerBlocks.SourceCacheDriver
