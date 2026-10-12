/-
Copyright (c) 2026 PNP Labs.

One protected state joins terminal matching/trace generation with both range
selections. The selector reuses scratch registers only. Original width,
formula, matching, terminal trace and the two selected lists remain outside
that scratch region; no second matching computation is introduced.
-/
import PNP.Concrete.NormalizerCutSelectionCall

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister Occurrence

structure State where
  core : MatchingDriver.State
  trace : BitString
  clauses : BitString
  variables : BitString

def State.frame (r : State) : Store 3 :=
  .cons r.trace (.cons r.clauses (.cons r.variables .nil))
def State.store (r : State) : Store 36 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : MatchingDriver.State) : State := {r with core := core}
def State.withRegisters (r : State) (registers : Registers) : State :=
  r.withCore (r.core.withRegisters registers)

def liftMatching (body : Block 33) : Block 36 := Frame.block 3 body
theorem liftMatching_exec (body : Block 33) (r : State) (fuel : Nat) (after : MatchingDriver.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftMatching body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame
def liftCore (body : Block 9) : Block 36 := liftMatching (MatchingDriver.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftMatching_exec _ r _ _ (MatchingDriver.liftCore_exec body r.core fuel after checked)

def State.selection (r : State) : CutSelection.State :=
  ⟨r.core.core.parent, r.core.core.core.core.core.trace,
    r.core.core.core.core.pending, r.core.core.core.core.skipped⟩
def State.selectionFrame (r : State) : Store 12 :=
  .cons r.core.core.core.core.trace
    (.cons r.core.core.core.core.active
      (.cons r.core.core.core.core.output
        (.cons r.core.core.core.remaining
          (.cons r.core.core.original
            (.cons r.core.width
              (.cons r.core.formula
                (.cons r.core.table
                  (.cons r.core.remaining
                    (.cons r.trace (.cons r.clauses (.cons r.variables .nil)))))))))))
def State.withSelection (r : State) (after : CutSelection.State) : State :=
  {r with core := {r.core with core := {r.core.core with core :=
    {r.core.core.core with core := {r.core.core.core.core with
      core := ⟨after.core,after.trace⟩, pending := after.remaining, skipped := after.buffer}}}}}
theorem State.selection_store (r : State) :
    r.store = Frame.join r.selection.store r.selectionFrame := by
  dsimp only [State.selection, State.selectionFrame, CutSelection.State.store, CutSelection.State.frame, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
theorem State.withSelection_store (r : State) (after : CutSelection.State) :
    (r.withSelection after).store = Frame.join after.store r.selectionFrame := by
  dsimp only [State.withSelection, State.selectionFrame, CutSelection.State.store, CutSelection.State.frame, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
theorem State.selection_registers (r : State) : r.selection.registers = r.registers := rfl
theorem State.withSelection_registers (r : State) (after : CutSelection.State) :
    (r.withSelection after).registers = after.registers := rfl

def liftSelection (body : Block 24) : Block 36 := Frame.block 12 body
theorem liftSelection_exec (body : Block 24) (r : State) (fuel : Nat) (after : CutSelection.State)
    (checked : Exec body r.selection.store fuel after.store) :
    Exec (liftSelection body) r.store fuel (r.withSelection after).store := by
  rw [State.selection_store, State.withSelection_store]
  exact Frame.execution checked r.selectionFrame
theorem selection_bounded (r : State) (bound : Nat) (h : r.store.Bounded bound) :
    r.selection.store.Bounded bound := by
  rw [State.selection_store] at h
  exact Frame.core_bounded _ _ h
theorem withSelection_frame (r : State) (after : CutSelection.State) :
    (r.withSelection after).core.width = r.core.width ∧
    (r.withSelection after).core.formula = r.core.formula ∧
    (r.withSelection after).core.table = r.core.table ∧
    (r.withSelection after).trace = r.trace ∧
    (r.withSelection after).clauses = r.clauses ∧
    (r.withSelection after).variables = r.variables := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def initial (input : BitString) : State := ⟨MatchingDriver.initial input,[],[],[]⟩
def traceBlock : Block 36 := liftMatching CutTrace.block
def traced (input : BitString) : State := ⟨CutTrace.result input,[],[],[]⟩
theorem trace_exec (input : BitString) :
    Exec traceBlock (initial input).store (CutTrace.sourceSteps input) (traced input).store :=
  liftMatching_exec _ (initial input) _ _ (CutTrace.block_exec input)

def saveTrace : Block 36 := .action (.copy 33 8)
def traceSaved (r : State) : State := {r with trace := r.registers.output}
theorem saveTrace_exec (r : State) : Exec saveTrace r.store 1 (traceSaved r).store := by
  dsimp only [saveTrace, traceSaved, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
  exact .action _ _
def initializeBlock : Block 36 := .seq traceBlock saveTrace
def initialized (input : BitString) : State := traceSaved (traced input)
def initializeSteps (input : BitString) : Nat := CutTrace.sourceSteps input + 1
theorem initialize_exec (input : BitString) :
    Exec initializeBlock (initial input).store (initializeSteps input) (initialized input).store :=
  Exec.seq (trace_exec input) (saveTrace_exec (traced input))
theorem initialized_fields (input : BitString) :
    (initialized input).core = CutTrace.result input ∧
      (initialized input).trace = (CutTrace.result input).registers.output := by
  dsimp only [initialized, traceSaved, traced, State.registers]
  exact ⟨rfl,rfl⟩

end PNP.Concrete.NormalizerBlocks.CutDriver
