/-
Copyright (c) 2026 PNP Labs.

Finite exploration state with a protected outer countdown. Each iteration
clears only disposable extraction flags and the skipped buffer, then runs
the already verified actual first-eligible extractor on the current trace.
The countdown is outside all extraction scratch registers.
-/

import PNP.Concrete.NormalizerExtractView

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister Occurrence

structure State where
  core : Extraction.State
  remaining : BitString
def State.frame (r : State) : Store 1 := .cons r.remaining .nil
def State.store (r : State) : Store 28 := Frame.join r.core.store r.frame
def State.registers (r : State) : Registers := r.core.registers
def State.withCore (r : State) (core : Extraction.State) : State := {r with core := core}
def State.withRegisters (r : State) (registers : Registers) : State := r.withCore (r.core.withRegisters registers)

def lift (body : Block 27) : Block 28 := Frame.block 1 body
theorem lift_exec (body : Block 27) (r : State) (fuel : Nat) (after : Extraction.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame

def liftCore (body : Block 9) : Block 28 := lift (Extraction.liftCore body)
theorem liftCore_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftCore body) r.store fuel (r.withRegisters after).store :=
  lift_exec _ r _ _ (Extraction.liftCore_exec body r.core fuel after checked)

def clearCore : Block 27 := .seq (.action (.clear 23)) (.action (.clear 25))
def coreCleared (r : Extraction.State) : Extraction.State := {r with skipped := [], active := []}
theorem clearCore_exec (r : Extraction.State) : Exec clearCore r.store 2 (coreCleared r).store :=
  Exec.seq (.action _ _) (.action _ _)

def prepareCore : Block 27 := .seq clearCore (.seq Extraction.activate Extraction.defaultAnswer)
def corePrepared (r : Extraction.State) : Extraction.State :=
  Extraction.defaulted (Extraction.activated (coreCleared r))
theorem prepareCore_exec (r : Extraction.State) : Exec prepareCore r.store 5 (corePrepared r).store :=
  Exec.seq (clearCore_exec r) (Exec.seq (Extraction.activate_exec (coreCleared r))
    (Extraction.defaultAnswer_exec (Extraction.activated (coreCleared r))))

def prepare : Block 28 := lift prepareCore
def prepared (r : State) : State := r.withCore (corePrepared r.core)
theorem prepare_exec (r : State) : Exec prepare r.store 5 (prepared r).store :=
  lift_exec _ r _ _ (prepareCore_exec r.core)

def extract : Block 28 := lift Extraction.loop
def extracted (r : State) : State := r.withCore (Extraction.whole r.core).state
theorem extract_exec (r : State) :
    Exec extract r.store (Extraction.whole r.core).fuel (extracted r).store :=
  lift_exec _ r _ _ (Extraction.whole_exec r.core)

def begin : Block 28 := .seq prepare extract
def begun (r : State) : State := extracted (prepared r)
def beginFuel (r : State) : Nat := 5 + (Extraction.whole (prepared r).core).fuel
theorem begin_exec (r : State) : Exec begin r.store (beginFuel r) (begun r).store :=
  Exec.seq (prepare_exec r) (extract_exec (prepared r))

theorem begun_fields (r : State) :
    (begun r).core.parent.graph.core.formula = r.core.parent.graph.core.formula ∧
      (begun r).core.parent.graph.core.matching = r.core.parent.graph.core.matching ∧
        (begun r).core.trace = r.core.trace ∧ (begun r).remaining = r.remaining := by
  have stable := Extraction.scan_preserves ((prepared r).core.pending.length + 1) (prepared r).core
  exact ⟨stable.1, stable.2.1, stable.2.2, rfl⟩

theorem begun_range (r : State) (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace) :
    Extraction.SelectionFrom unseen trace (begun r).core := by
  have layout : Extraction.Layout (prepared r).core unseen [] trace :=
    ⟨pendingRead, rfl, traceRead, rfl, rfl⟩
  exact Extraction.whole_range (prepared r).core unseen trace layout

theorem begun_outcome (r : State) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (formulaRead : r.core.parent.graph.core.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.core.parent.graph.core.matching = MatchingTable.encode entries)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace) :
    Extraction.OutputMatches (begun r).core (Extraction.value clauses entries trace unseen) := by
  have data : Extraction.Canonical (prepared r).core clauses entries trace unseen [] :=
    ⟨formulaRead, matchingRead, traceRead, pendingRead, rfl, rfl, rfl⟩
  exact Extraction.whole_outcome (prepared r).core clauses entries trace unseen data

theorem beginFuel_bound (r : State) :
    beginFuel r ≤ (Extraction.stepBound r.core + 1) * (r.core.pending.length + 1) + 6 := by
  have bound := Extraction.whole_fuel_bound (prepared r).core
  have same : Extraction.stepBound (prepared r).core = Extraction.stepBound r.core := rfl
  rw [same] at bound
  change (Extraction.whole (prepared r).core).fuel ≤
    (Extraction.stepBound r.core + 1) * (r.core.pending.length + 1) + 1 at bound
  unfold beginFuel
  omega

end PNP.Concrete.NormalizerBlocks.Exploration
