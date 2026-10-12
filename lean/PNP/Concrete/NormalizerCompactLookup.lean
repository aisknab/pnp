/-
Copyright (c) 2026 PNP Labs.

Call the existing first-owner machine on the protected selected-variable
encoding. The actual literal index is read from the core register; no dense
position is supplied. All cursor, polarity and output-buffer data survive.
-/
import PNP.Concrete.NormalizerCompactRead

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

def resetOwnerLeft : Block 9 :=
  .seq (.action (.clear 2)) (.seq (.action (.clear 3)) (.action (.clear 4)))
def ownerLeftCleared (r : Registers) : Registers :=
  {r with remaining := [], excess := [], sign := []}
theorem resetOwnerLeft_exec (r : Registers) :
    Exec resetOwnerLeft r.store 3 (ownerLeftCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def resetOwner : Block 9 :=
  .seq resetOwnerLeft <| .seq CandidatePacket.clearRight <|
    .seq (.action (.push 6 true)) (.action (.push 8 false))
theorem resetOwner_exec (r : Registers) :
    Exec resetOwner r.store 9 (TableOwner.prepared r.target r.input).store :=
  Exec.seq (resetOwnerLeft_exec r)
    (Exec.seq (CandidatePacket.clearRight_exec (ownerLeftCleared r))
      (Exec.seq (.action _ _) (.action _ _)))

def loadVariables : Block 13 := .action (.copy 0 10)
def variablesLoaded (r : State) : State := r.withCore {r.core with input := r.variables}
theorem loadVariables_exec (r : State) :
    Exec loadVariables r.store 1 (variablesLoaded r).store := .action _ _

def prepareOwner : Block 13 := .seq loadVariables (liftCore resetOwner)
def ownerPrepared (r : State) : State := r.withCore (TableOwner.prepared r.core.target r.variables)
theorem prepareOwner_exec (r : State) :
    Exec prepareOwner r.store 10 (ownerPrepared r).store :=
  Exec.seq (loadVariables_exec r)
    (liftCore_exec _ (variablesLoaded r) _ _ (resetOwner_exec (variablesLoaded r).core))

def lookup : Block 13 := .seq prepareOwner (liftCore TableOwner.loop)
def looked (r : State) : State :=
  r.withCore (TableOwner.queryResult (TableOwner.prepared r.core.target r.variables)).state
def lookupFuel (r : State) : Nat :=
  10 + (TableOwner.queryResult (TableOwner.prepared r.core.target r.variables)).fuel

theorem lookup_exec (r : State) : Exec lookup r.store (lookupFuel r) (looked r).store :=
  Exec.seq (prepareOwner_exec r)
    (liftCore_exec _ (ownerPrepared r) _ _ (TableOwner.query_exec (ownerPrepared r).core))

theorem lookupFuel_bound (r : State) : lookupFuel r ≤ 12 * r.variables.length + 23 := by
  have bound := TableOwner.query_fuel_bound (TableOwner.prepared r.core.target r.variables)
  change (TableOwner.queryResult (TableOwner.prepared r.core.target r.variables)).fuel ≤
    12 * (r.variables.length + 1) + 1 at bound
  unfold lookupFuel
  omega

theorem lookup_fields (r : State) :
    (looked r).pending = r.pending ∧
    (looked r).variables = r.variables ∧
    (looked r).buffer = r.buffer ∧
    (looked r).positive = r.positive := ⟨rfl,rfl,rfl,rfl⟩

theorem lookup_canonical (r : State) (target : Nat) (vertices : List CNFLiteral)
    (indexRead : r.core.target = List.replicate target true)
    (variablesRead : r.variables = SearchVertices.encodeVertices vertices) :
    (looked r).core.output = TableOwner.answer (TableOwner.vertexOwner vertices target) := by
  change (TableOwner.queryResult (TableOwner.prepared r.core.target r.variables)).state.output = _
  rw [indexRead, variablesRead]
  exact TableOwner.prepared_vertices target vertices

theorem preparedOwner_bounded (target variables : BitString) :
    (TableOwner.prepared target variables).store.Bounded
      (target.length + variables.length + 1) := by
  dsimp only [TableOwner.prepared, Registers.store, Store.Bounded]
  simp only [List.length_nil, List.length_cons]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,by omega,True.intro⟩

theorem lookup_output_bound (r : State) :
    (looked r).core.output.length ≤ r.core.target.length + 13 * r.variables.length + 14 := by
  let prepared := TableOwner.prepared r.core.target r.variables
  have bounded := (TableOwner.query_exec prepared).bounded
    (r.core.target.length + r.variables.length + 1)
    (preparedOwner_bounded r.core.target r.variables)
  have output := Store.get_length_le (TableOwner.queryResult prepared).state.store (8 : Fin 9) bounded
  change (looked r).core.output.length ≤
    r.core.target.length + r.variables.length + 1 + (TableOwner.queryResult prepared).fuel at output
  have fuel := TableOwner.query_fuel_bound prepared
  change (TableOwner.queryResult prepared).fuel ≤ 12 * (r.variables.length + 1) + 1 at fuel
  omega

end PNP.Concrete.NormalizerBlocks.CompactClause
