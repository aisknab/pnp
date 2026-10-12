/-
Copyright (c) 2026 PNP Labs.

Finite emission of one decoded augmentation update. The reverse buffer
preserves pair order for final serialization and has no supplied output.
-/
import PNP.Concrete.NormalizerPairReader

namespace PNP.Concrete.NormalizerBlocks.PathPairs
open BitRegister

def startEmission : Block 12 := .seq (.action (.copy 2 1)) (.action (.copy 0 11))
def emissionStarted (r : State) : State := r.withCore {r.core with remaining := r.core.target, input := r.buffer}
theorem startEmission_exec (r : State) : Exec startEmission r.store 2 (emissionStarted r).store :=
  Exec.seq (.action _ _) (.action _ _)

def prepend : Block 12 := liftCore ParentQuery.prependLoop
def prepended (r : State) : State := r.withCore (ParentQuery.prepended r.core.remaining r.core)
theorem prepend_exec (r : State) :
    Exec prepend r.store (3 * r.core.remaining.length + 1) (prepended r).store :=
  liftCore_exec _ r _ _ (ParentQuery.prepend_exec r.core.remaining r.core)

def startValue : Block 12 := .seq (.action (.push 0 false)) (.action (.copy 2 10))
def valueStarted (r : State) : State := r.withCore {r.core with input := false :: r.core.input, remaining := r.firstIndex}
theorem startValue_exec (r : State) : Exec startValue r.store 2 (valueStarted r).store :=
  Exec.seq (.action _ _) (.action _ _)

def saveEmission : Block 12 := .seq (.action (.push 0 false)) (.action (.copy 11 0))
def emissionSaved (r : State) : State := {r.withCore {r.core with input := false :: r.core.input} with buffer := false :: r.core.input}
theorem saveEmission_exec (r : State) : Exec saveEmission r.store 2 (emissionSaved r).store :=
  Exec.seq (.action _ _) (.action _ _)

def emit : Block 12 := .seq startEmission (.seq prepend (.seq startValue (.seq prepend saveEmission)))
def emitted (r : State) : State := emissionSaved (prepended (valueStarted (prepended (emissionStarted r))))
def emitFuel (r : State) : Nat := 3 * r.core.target.length + 3 * r.firstIndex.length + 8
theorem emit_exec (r : State) : Exec emit r.store (emitFuel r) (emitted r).store := by
  have checked := Exec.seq (startEmission_exec r) (Exec.seq (prepend_exec (emissionStarted r))
    (Exec.seq (startValue_exec (prepended (emissionStarted r)))
      (Exec.seq (prepend_exec (valueStarted (prepended (emissionStarted r))))
        (saveEmission_exec (prepended (valueStarted (prepended (emissionStarted r))))))))
  change Exec emit r.store (2 + ((3 * r.core.target.length + 1) + (2 + ((3 * r.firstIndex.length + 1) + 2)))) (emitted r).store at checked
  have cost : 2 + ((3 * r.core.target.length + 1) + (2 + ((3 * r.firstIndex.length + 1) + 2))) = emitFuel r := by unfold emitFuel; omega
  rw [cost] at checked
  exact checked

theorem emitted_buffer (r : State) :
    (emitted r).buffer =
      false :: (List.replicate r.firstIndex.length true ++ (false :: (List.replicate r.core.target.length true ++ r.buffer))) := rfl
theorem emitted_pending (r : State) : (emitted r).pending = r.pending := rfl

theorem emitted_canonical (r : State) (index value : Nat)
    (indexRead : r.core.target = List.replicate index true)
    (valueRead : r.firstIndex = List.replicate value true) :
    (emitted r).buffer = (TableBatch.encodePair index value []).reverse ++ r.buffer := by
  rw [emitted_buffer, indexRead, valueRead, List.length_replicate, List.length_replicate, pair_reverse]

def processPair : Block 12 := .seq readSecond emit
def pairProcessed (r : State) : State := emitted (secondRead r)
def processFuel (r : State) : Nat := secondFuel r + emitFuel (secondRead r)
theorem processPair_exec (r : State) : Exec processPair r.store (processFuel r) (pairProcessed r).store :=
  Exec.seq (readSecond_exec r) (emit_exec (secondRead r))

theorem pairProcessed_canonical (r : State) (index value : Nat) (suffix : BitString)
    (input : r.core.input = TraceData.vertex ⟨true, index⟩ suffix)
    (first : r.firstIndex = List.replicate value true) :
    (pairProcessed r).pending = suffix ∧
      (pairProcessed r).buffer = (TableBatch.encodePair index value []).reverse ++ r.buffer := by
  have read := secondRead_canonical r ⟨true, index⟩ suffix input
  exact ⟨read.1, (emitted_canonical (secondRead r) index value read.2.1 (read.2.2.1.trans first)).trans
    (congrArg (fun b => (TableBatch.encodePair index value []).reverse ++ b) read.2.2.2)⟩

end PNP.Concrete.NormalizerBlocks.PathPairs
