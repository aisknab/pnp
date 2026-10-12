/-
Copyright (c) 2026 PNP Labs.

Pack all four derived cut fields into one length-delimited internal packet.
The packet contains matching, terminal trace, selected clauses and selected
variables. It is an internal normalizer interface, not the final serialized
normalizer output. Packing is charged and the source fields remain available.
-/
import PNP.Concrete.NormalizerCutBounds

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister Occurrence

def countPrefix : Block 36 := liftCore MatchingPacket.prependCount
def countPrefixed (r : State) : State := r.withRegisters (MatchingPacket.countPrepended r.registers)
theorem countPrefix_exec (r : State) :
    Exec countPrefix r.store (MatchingPacket.countFuel r.registers) (countPrefixed r).store :=
  liftCore_exec _ r _ _ (MatchingPacket.prependCount_exec r.registers)
def bitsPrefix : Block 36 := liftCore MatchingPacket.prependBits
def bitsPrefixed (r : State) : State := r.withRegisters (MatchingPacket.bitsPrepended r.registers)
theorem bitsPrefix_exec (r : State) :
    Exec bitsPrefix r.store (MatchingPacket.bitsFuel r.registers) (bitsPrefixed r).store :=
  liftCore_exec _ r _ _ (MatchingPacket.prependBits_exec r.registers)

def seedVariables : Block 36 := .seq (.action (.copy 8 35)) (.action (.copy 2 35))
def variablesSeeded (r : State) : State :=
  r.withRegisters {r.registers with output := r.variables, remaining := r.variables}
theorem seedVariables_exec (r : State) : Exec seedVariables r.store 2 (variablesSeeded r).store := by
  dsimp only [seedVariables, variablesSeeded, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact Exec.seq (.action _ _) (.action _ _)
def loadClauses : Block 36 := .seq (.action (.copy 0 34)) (.action (.copy 2 34))
def clausesLoaded (r : State) : State :=
  r.withRegisters {r.registers with input := r.clauses, remaining := r.clauses}
theorem loadClauses_exec (r : State) : Exec loadClauses r.store 2 (clausesLoaded r).store := by
  dsimp only [loadClauses, clausesLoaded, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact Exec.seq (.action _ _) (.action _ _)
def loadTraceSection : Block 36 := .seq (.action (.copy 0 33)) (.action (.copy 2 33))
def traceSectionLoaded (r : State) : State :=
  r.withRegisters {r.registers with input := r.trace, remaining := r.trace}
theorem loadTraceSection_exec (r : State) :
    Exec loadTraceSection r.store 2 (traceSectionLoaded r).store := by
  dsimp only [loadTraceSection, traceSectionLoaded, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact Exec.seq (.action _ _) (.action _ _)
def loadMatching : Block 36 := .seq (.action (.copy 0 31)) (.action (.copy 2 31))
def matchingLoaded (r : State) : State :=
  r.withRegisters {r.registers with input := r.core.table, remaining := r.core.table}
theorem loadMatching_exec (r : State) : Exec loadMatching r.store 2 (matchingLoaded r).store := by
  dsimp only [loadMatching, matchingLoaded, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact Exec.seq (.action _ _) (.action _ _)

private theorem seed_cost (n : Nat) : 3 * n + 6 = 2 + (3 * n + 4) := by omega
private theorem section_cost (n : Nat) : 11 * n + 13 = 2 + ((8 * n + 7) + (3 * n + 4)) := by omega
def packVariables : Block 36 := .seq seedVariables countPrefix
def variablesPacked (r : State) : State := countPrefixed (variablesSeeded r)
theorem packVariables_exec (r : State) :
    Exec packVariables r.store (3 * r.variables.length + 6) (variablesPacked r).store := by
  rw [seed_cost]
  exact Exec.seq (seedVariables_exec r) (countPrefix_exec (variablesSeeded r))
def prependClauses : Block 36 := .seq loadClauses (.seq bitsPrefix countPrefix)
def clausesPrefixed (r : State) : State := countPrefixed (bitsPrefixed (clausesLoaded r))
theorem prependClauses_exec (r : State) :
    Exec prependClauses r.store (11 * r.clauses.length + 13) (clausesPrefixed r).store := by
  rw [section_cost]
  exact Exec.seq (loadClauses_exec r) <|
    Exec.seq (bitsPrefix_exec (clausesLoaded r)) (countPrefix_exec (bitsPrefixed (clausesLoaded r)))
def prependTrace : Block 36 := .seq loadTraceSection (.seq bitsPrefix countPrefix)
def tracePrefixed (r : State) : State := countPrefixed (bitsPrefixed (traceSectionLoaded r))
theorem prependTrace_exec (r : State) :
    Exec prependTrace r.store (11 * r.trace.length + 13) (tracePrefixed r).store := by
  rw [section_cost]
  exact Exec.seq (loadTraceSection_exec r) <|
    Exec.seq (bitsPrefix_exec (traceSectionLoaded r)) (countPrefix_exec (bitsPrefixed (traceSectionLoaded r)))
def prependMatching : Block 36 := .seq loadMatching (.seq bitsPrefix countPrefix)
def matchingPrefixed (r : State) : State := countPrefixed (bitsPrefixed (matchingLoaded r))
theorem prependMatching_exec (r : State) :
    Exec prependMatching r.store (11 * r.core.table.length + 13) (matchingPrefixed r).store := by
  rw [section_cost]
  exact Exec.seq (loadMatching_exec r) <|
    Exec.seq (bitsPrefix_exec (matchingLoaded r)) (countPrefix_exec (bitsPrefixed (matchingLoaded r)))

def packet (matching trace clauses variables : BitString) : BitString :=
  TableInit.encodeCount matching.length (matching ++
    TableInit.encodeCount trace.length (trace ++
      TableInit.encodeCount clauses.length (clauses ++ TableInit.encodeCount variables.length variables)))
def pack : Block 36 := .seq packVariables (.seq prependClauses (.seq prependTrace prependMatching))
def packed (r : State) : State := matchingPrefixed (tracePrefixed (clausesPrefixed (variablesPacked r)))
def packFuel (r : State) : Nat :=
  3 * r.variables.length + 11 * r.clauses.length + 11 * r.trace.length + 11 * r.core.table.length + 45
private theorem pack_cost (v c t m : Nat) :
    3 * v + 11 * c + 11 * t + 11 * m + 45 =
      (3 * v + 6) + ((11 * c + 13) + ((11 * t + 13) + (11 * m + 13))) := by omega
theorem pack_exec (r : State) : Exec pack r.store (packFuel r) (packed r).store := by
  unfold packFuel
  rw [pack_cost]
  exact Exec.seq (packVariables_exec r) <|
    Exec.seq (prependClauses_exec (variablesPacked r)) <|
      Exec.seq (prependTrace_exec (clausesPrefixed (variablesPacked r)))
        (prependMatching_exec (tracePrefixed (clausesPrefixed (variablesPacked r))))
theorem packed_output (r : State) :
    (packed r).registers.output = packet r.core.table r.trace r.clauses r.variables := rfl
theorem packed_frame (r : State) :
    (packed r).core.width = r.core.width ∧ (packed r).core.formula = r.core.formula ∧
    (packed r).core.table = r.core.table ∧ (packed r).trace = r.trace ∧
    (packed r).clauses = r.clauses ∧ (packed r).variables = r.variables :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem State.get_matching (r : State) : r.store.get (31 : Fin 36) = r.core.table := by
  dsimp only [State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join, Store.get, Store.indexCases]
theorem State.get_trace (r : State) : r.store.get (33 : Fin 36) = r.trace := by
  dsimp only [State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join, Store.get, Store.indexCases]
theorem State.get_clauses (r : State) : r.store.get (34 : Fin 36) = r.clauses := by
  dsimp only [State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join, Store.get, Store.indexCases]
theorem State.get_variables (r : State) : r.store.get (35 : Fin 36) = r.variables := by
  dsimp only [State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Occurrence.Registers.store, Frame.join, Store.get, Store.indexCases]
attribute [local irreducible] State.store
theorem packFuel_bound (r : State) (bound : Nat) (h : r.store.Bounded bound) :
    packFuel r ≤ 36 * bound + 45 := by
  have m := Store.get_length_le r.store (31 : Fin 36) (bound := bound) h
  have t := Store.get_length_le r.store (33 : Fin 36) (bound := bound) h
  have c := Store.get_length_le r.store (34 : Fin 36) (bound := bound) h
  have v := Store.get_length_le r.store (35 : Fin 36) (bound := bound) h
  rw [State.get_matching] at m
  rw [State.get_trace] at t
  rw [State.get_clauses] at c
  rw [State.get_variables] at v
  unfold packFuel
  omega

end PNP.Concrete.NormalizerBlocks.CutDriver
