/-
Copyright (c) 2026 PNP Labs.

Protected finite-register views for complete search. Exploration owns the
first twenty-eight registers; a final register preserves the original
input. Candidate and path phases reuse shorter prefixes while the full
trace and original input remain protected.
-/
import PNP.Concrete.NormalizerSeenPhase

namespace PNP.Concrete.NormalizerBlocks.Frame
open BitRegister
theorem core_bounded {extra count bound : Nat} (core : Store count) (frame : Store extra)
    (checked : (join core frame).Bounded bound) : core.Bounded bound := by
  induction core with
  | nil => trivial
  | cons first rest ih => exact ⟨checked.1, ih checked.2⟩
end PNP.Concrete.NormalizerBlocks.Frame

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister Occurrence

structure State where
  core : Exploration.State
  original : BitString
def State.frame (r : State) : Store 1 := .cons r.original .nil
def State.store (r : State) : Store 29 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.parent (r : State) : ParentQuery.State := r.core.core.parent
def State.withCore (r : State) (core : Exploration.State) : State := {r with core := core}
def State.withRegisters (r : State) (registers : Registers) : State := r.withCore (r.core.withRegisters registers)
def State.withParent (r : State) (parent : ParentQuery.State) : State := r.withCore (r.core.withCore (r.core.core.withParent parent))

def liftExploration (body : Block 28) : Block 29 := Frame.block 1 body
theorem liftExploration_exec (body : Block 28) (r : State) (fuel : Nat) (after : Exploration.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (liftExploration body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame
def liftCore (body : Block 9) : Block 29 := liftExploration (Exploration.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  liftExploration_exec _ r _ _ (Exploration.liftCore_exec body r.core fuel after checked)

def State.path (r : State) : TracePath.State := ⟨r.parent, r.core.core.core.trace, r.core.core.pending⟩
def State.pathFrame (r : State) : Store 6 :=
  .cons r.core.core.skipped (.cons r.core.core.trace (.cons r.core.core.active (.cons r.core.core.output (.cons r.core.remaining (.cons r.original .nil)))))
def State.withPath (r : State) (path : TracePath.State) : State :=
  r.withCore (r.core.withCore {r.core.core with core := ⟨path.core, path.buffer⟩, pending := path.parentBytes})
theorem State.path_store (r : State) : r.store = Frame.join r.path.store r.pathFrame := by
  simp only [State.store, State.frame, State.path, State.pathFrame, State.parent, TracePath.State.store, TracePath.State.frame, Exploration.State.store, Exploration.State.frame, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]
theorem State.withPath_store (r : State) (after : TracePath.State) :
    (r.withPath after).store = Frame.join after.store r.pathFrame := by
  simp only [State.withPath, State.withCore, Exploration.State.withCore, State.store, State.frame, State.pathFrame, TracePath.State.store, TracePath.State.frame, Exploration.State.store, Exploration.State.frame, Extraction.State.store, Extraction.State.frame, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join]

def liftPath (body : Block 23) : Block 29 := Frame.block 6 body
theorem liftPath_exec (body : Block 23) (r : State) (fuel : Nat) (after : TracePath.State)
    (checked : Exec body r.path.store fuel after.store) :
    Exec (liftPath body) r.store fuel (r.withPath after).store :=
by
  rw [State.path_store, State.withPath_store]
  exact Frame.execution checked r.pathFrame
theorem path_bounded (r : State) (bound : Nat) (checked : r.store.Bounded bound) : r.path.store.Bounded bound :=
by
  rw [State.path_store] at checked
  exact Frame.core_bounded r.path.store r.pathFrame checked

def State.candidate (r : State) : Candidate.State :=
  ⟨r.registers, r.parent.graph.core.target, r.parent.graph.core.index, r.parent.graph.core.formula, r.parent.graph.core.matching⟩
def State.candidateFrame (r : State) : Store 16 :=
  .cons r.parent.graph.core.mark
    (Frame.join r.parent.graph.frame
      (Frame.join r.parent.frame (Frame.join r.core.core.core.frame
        (Frame.join r.core.core.frame (Frame.join r.core.frame r.frame)))))
def State.withCandidate (r : State) (candidate : Candidate.State) : State :=
  r.withParent {r.parent with graph := {r.parent.graph with core := {r.parent.graph.core with core := candidate.core, target := candidate.matching, index := candidate.seen, formula := candidate.remaining, matching := candidate.output}}}
theorem State.candidate_store (r : State) : r.store = Frame.join r.candidate.store r.candidateFrame := rfl
theorem State.withCandidate_store (r : State) (after : Candidate.State) :
    (r.withCandidate after).store = Frame.join after.store r.candidateFrame := rfl

def liftCandidate (body : Block 13) : Block 29 := Frame.block 16 body
theorem liftCandidate_exec (body : Block 13) (r : State) (fuel : Nat) (after : Candidate.State)
    (checked : Exec body r.candidate.store fuel after.store) :
    Exec (liftCandidate body) r.store fuel (r.withCandidate after).store :=
by
  rw [State.candidate_store, State.withCandidate_store]
  exact Frame.execution checked r.candidateFrame
theorem candidate_bounded (r : State) (bound : Nat) (checked : r.store.Bounded bound) :
    r.candidate.store.Bounded bound :=
by
  rw [State.candidate_store] at checked
  exact Frame.core_bounded r.candidate.store r.candidateFrame checked

theorem path_frame (r : State) (after : TracePath.State) :
    (r.withPath after).core.core.trace = r.core.core.trace ∧
      (r.withPath after).original = r.original := ⟨rfl, rfl⟩
theorem candidate_frame (r : State) (after : Candidate.State) :
    (r.withCandidate after).core.core.trace = r.core.core.trace ∧
      (r.withCandidate after).original = r.original := ⟨rfl, rfl⟩

end PNP.Concrete.NormalizerBlocks.Search
