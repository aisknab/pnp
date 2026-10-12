/-
Copyright (c) 2026 PNP Labs.

Internally generated search trace and seen-variable table. The full input
is protected during exploration; the seen converter consumes a work copy
of the resulting trace while the original trace remains available.
-/
import PNP.Concrete.NormalizerSearchState

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister

def initial (input : BitString) : State := ⟨Exploration.initial input, []⟩
def saveOriginal : Block 29 := .action (.copy (Frame.frameIndex 28 (0 : Fin 1)) (Frame.index 1 (0 : Fin 28)))
def originalSaved (r : State) : State := {r with original := r.registers.input}
theorem saveOriginal_exec (r : State) : Exec saveOriginal r.store 1 (originalSaved r).store := by
  have input : r.core.store.get (0 : Fin 28) = r.registers.input := rfl
  have checked := Exec.action (.copy (Frame.frameIndex 28 (0 : Fin 1)) (Frame.index 1 (0 : Fin 28))) r.store
  simpa only [saveOriginal, Action.update, Action.instruction, Instruction.update, State.store,
    Frame.get_core, Frame.set_frame, input, State.frame, originalSaved, Store.set, Store.indexCases] using checked

def explore : Block 29 := .seq saveOriginal (liftExploration Exploration.block)
def explored (input : BitString) : State := ⟨Exploration.result input, input⟩
def exploreFuel (input : BitString) : Nat := 1 + Exploration.sourceSteps input
theorem explore_exec (input : BitString) : Exec explore (initial input).store (exploreFuel input) (explored input).store :=
  Exec.seq (saveOriginal_exec (initial input))
    (liftExploration_exec _ (originalSaved (initial input)) _ _ (Exploration.block_exec input))
theorem exploreFuel_bound (input : BitString) : exploreFuel input ≤ Exploration.sourceFuel.eval input.length := by
  have checked := Exploration.sourceSteps_bound input
  unfold exploreFuel
  omega

def traceValue (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : List TraceData.Row :=
  Exploration.value clauses entries (clauses.length + variables) (SearchVertices.vertices clauses.length variables) []

theorem explored_trace (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    (explored (Exploration.encode variables clauses entries)).core.core.trace =
      TraceData.encode (traceValue variables clauses entries) := by
  have checked := Exploration.polynomial_canonical variables clauses entries
  rw [Exploration.polynomial_output] at checked
  exact checked

theorem explored_matching_raw (input : BitString) :
    (explored input).parent.graph.core.matching = Exploration.sourceMatching input := by
  have preserved := Exploration.scan_preserves ((Exploration.initialized input).remaining.length + 1) (Exploration.initialized input)
  exact preserved.2.trans (Exploration.initialized_fields input).2.1

theorem explored_matching (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    (explored (Exploration.encode variables clauses entries)).parent.graph.core.matching = MatchingTable.encode entries := by
  rw [explored_matching_raw]
  exact (Exploration.source_canonical variables clauses entries).2.2.1

def copyTrace : Block 29 := .action (.copy 16 24)
def traceCopied (r : State) : State := r.withParent {r.parent with pending := r.core.core.trace}
theorem copyTrace_exec (r : State) : Exec copyTrace r.store 1 (traceCopied r).store := .action _ _

def buildSeen : Block 29 := liftPath SeenTrace.phase
def seenBuilt (r : State) : State := r.withPath (SeenTrace.phaseResult r.path)
def seenFuel (r : State) : Nat := SeenTrace.phaseFuel r.path
theorem buildSeen_exec (r : State) : Exec buildSeen r.store (seenFuel r) (seenBuilt r).store :=
  liftPath_exec _ r _ _ (SeenTrace.phase_exec r.path)

def deriveSeen : Block 29 := .seq copyTrace buildSeen
def seenDerived (r : State) : State := seenBuilt (traceCopied r)
def deriveSeenFuel (r : State) : Nat := 1 + seenFuel (traceCopied r)
theorem deriveSeen_exec (r : State) : Exec deriveSeen r.store (deriveSeenFuel r) (seenDerived r).store :=
  Exec.seq (copyTrace_exec r) (buildSeen_exec (traceCopied r))

theorem seenDerived_frame (r : State) :
    (seenDerived r).core.core.trace = r.core.core.trace ∧
      (seenDerived r).original = r.original ∧
        (seenDerived r).parent.graph.core.matching = r.parent.graph.core.matching :=
  ⟨rfl, rfl, (SeenTrace.phase_preserves (traceCopied r).path).2⟩

theorem seenDerived_canonical (r : State) (trace : List TraceData.Row)
    (read : r.core.core.trace = TraceData.encode trace) :
    (seenDerived r).registers.output = MatchingTable.encode (SeenTrace.value trace) :=
  SeenTrace.phase_canonical (traceCopied r).path trace read

end PNP.Concrete.NormalizerBlocks.Search
