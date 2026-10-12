/-
Copyright (c) 2026 PNP Labs.

Path reconstruction for the internally selected search candidate. The
target is taken from the actual selected answer and the path phase reads a
work copy of the complete generated trace. The selected index is preserved.
-/
import PNP.Concrete.NormalizerSearchCandidate

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister

def pathTarget : Block 23 :=
  .seq (.action (.copy 17 12)) (.seq (.action (.pop 17)) (.seq (.action (.clear 18)) (.action (.push 18 false))))
def pathTargeted (r : TracePath.State) : TracePath.State :=
  r.withCore {r.core with targetIndex := r.core.graph.core.matching.tail, targetTag := [false]}
theorem pathTarget_exec (r : TracePath.State) : Exec pathTarget r.store 4 (pathTargeted r).store :=
by
  let copied := r.withCore {r.core with targetIndex := r.core.graph.core.matching}
  let popped := r.withCore {r.core with targetIndex := r.core.graph.core.matching.tail}
  let cleared := r.withCore {r.core with targetIndex := r.core.graph.core.matching.tail, targetTag := []}
  have first : Exec (.action (.copy 17 12)) r.store 1 copied.store := .action _ _
  have second : Exec (.action (.pop 17)) copied.store 1 popped.store := .action _ _
  have third : Exec (.action (.clear 18)) popped.store 1 cleared.store := .action _ _
  have fourth : Exec (.action (.push 18 false)) cleared.store 1 (pathTargeted r).store := .action _ _
  exact Exec.seq first (Exec.seq second (Exec.seq third fourth))

def preparePath : Block 29 := .seq copyTrace (liftPath pathTarget)
def pathPrepared (r : State) : State := (traceCopied r).withPath (pathTargeted (traceCopied r).path)
theorem preparePath_exec (r : State) : Exec preparePath r.store 5 (pathPrepared r).store :=
  Exec.seq (copyTrace_exec r) (liftPath_exec _ (traceCopied r) _ _ (pathTarget_exec (traceCopied r).path))

def findPath : Block 29 := liftPath TracePath.phase
def pathFound (r : State) : State := r.withPath (TracePath.phaseResult r.path)
def findPathFuel (r : State) : Nat := TracePath.phaseFuel r.path
theorem findPath_exec (r : State) : Exec findPath r.store (findPathFuel r) (pathFound r).store :=
  liftPath_exec _ r _ _ (TracePath.phase_exec r.path)

def reconstruct : Block 29 := .seq preparePath findPath
def reconstructed (r : State) : State := pathFound (pathPrepared r)
def reconstructFuel (r : State) : Nat := 5 + findPathFuel (pathPrepared r)
theorem reconstruct_exec (r : State) : Exec reconstruct r.store (reconstructFuel r) (reconstructed r).store :=
  Exec.seq (preparePath_exec r) (findPath_exec (pathPrepared r))

theorem reconstructed_frame (r : State) :
    (reconstructed r).core.core.trace = r.core.core.trace ∧
      (reconstructed r).original = r.original ∧
        (reconstructed r).parent.graph.core.matching = r.parent.graph.core.matching :=
  ⟨rfl, rfl, (TracePath.phase_preserves (pathPrepared r).path).2⟩

theorem reconstructed_canonical (r : State) (index : Nat) (trace : List TraceData.Row)
    (chosen : r.parent.graph.core.matching = TableOwner.answer (some index))
    (read : r.core.core.trace = TraceData.encode trace) :
    (reconstructed r).registers.output = PathData.answer (TracePath.value trace ⟨false, index⟩) := by
  have target : (pathPrepared r).path.core.targetIndex = List.replicate index true := by
    change r.parent.graph.core.matching.tail = _
    rw [chosen]
    rfl
  exact TracePath.phase_canonical (pathPrepared r).path ⟨false, index⟩ trace target rfl read

end PNP.Concrete.NormalizerBlocks.Search
