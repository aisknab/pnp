/-
Copyright (c) 2026 PNP Labs.

Recovery queries protect the original formula, original matching, selected
variables and dense candidate outside the scratch prefix. Both membership
and source ownership are computed by the existing closed first-owner scan.
-/
import PNP.Concrete.NormalizerCompactLookup
import PNP.Concrete.NormalizerBitLookup
import PNP.Concrete.NormalizerGraphQuery

namespace PNP.Concrete.NormalizerBlocks.Recovery
open BitRegister Occurrence

structure State where
  core : Registers
  formula : BitString
  matching : BitString
  variables : BitString
  assignment : BitString
  remaining : BitString
  counter : BitString
  buffer : BitString
def State.frame (r : State) : Store 7 :=
  .cons r.formula (.cons r.matching (.cons r.variables (.cons r.assignment
    (.cons r.remaining (.cons r.counter (.cons r.buffer .nil))))))
def State.store (r : State) : Store 16 := Frame.join r.core.store r.frame
def State.withCore (r : State) (core : Registers) : State := {r with core := core}
def lift (body : Block 9) : Block 16 := Frame.block 7 body
theorem lift_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lift body) r.store fuel (r.withCore after).store :=
  Frame.execution checked r.frame

structure Data where
  formula : BitString
  matching : BitString
  variables : BitString
  assignment : BitString
def State.data (r : State) : Data := ⟨r.formula,r.matching,r.variables,r.assignment⟩

inductive OwnerKind where
  | matching | selected
def ownerWord : OwnerKind → State → BitString
  | .matching,r => r.matching
  | .selected,r => r.variables
def ownerRegister : OwnerKind → Fin 16
  | .matching => 10
  | .selected => 11
def loadOwner (kind : OwnerKind) : Block 16 :=
  .seq (.action (.copy 0 (ownerRegister kind))) (.action (.copy 1 14))
def ownerLoaded (kind : OwnerKind) (r : State) : State :=
  r.withCore {r.core with input := ownerWord kind r,target := r.counter}
theorem loadOwner_exec (kind : OwnerKind) (r : State) :
    Exec (loadOwner kind) r.store 2 (ownerLoaded kind r).store := by
  cases kind <;> exact Exec.seq (.action _ _) (.action _ _)
def prepareOwner (kind : OwnerKind) : Block 16 := .seq (loadOwner kind) (lift CompactClause.resetOwner)
def ownerPrepared (kind : OwnerKind) (r : State) : State :=
  r.withCore (TableOwner.prepared r.counter (ownerWord kind r))
theorem prepareOwner_exec (kind : OwnerKind) (r : State) :
    Exec (prepareOwner kind) r.store 11 (ownerPrepared kind r).store :=
  Exec.seq (loadOwner_exec kind r)
    (lift_exec _ (ownerLoaded kind r) _ _ (CompactClause.resetOwner_exec _))
def owner (kind : OwnerKind) : Block 16 := .seq (prepareOwner kind) (lift TableOwner.loop)
def owned (kind : OwnerKind) (r : State) : State :=
  r.withCore (TableOwner.queryResult (TableOwner.prepared r.counter (ownerWord kind r))).state
def ownerFuel (kind : OwnerKind) (r : State) : Nat :=
  11+(TableOwner.queryResult (TableOwner.prepared r.counter (ownerWord kind r))).fuel
theorem owner_exec (kind : OwnerKind) (r : State) :
    Exec (owner kind) r.store (ownerFuel kind r) (owned kind r).store :=
  Exec.seq (prepareOwner_exec kind r)
    (lift_exec _ (ownerPrepared kind r) _ _ (TableOwner.query_exec _))
theorem owned_data (kind : OwnerKind) (r : State) : (owned kind r).data = r.data := rfl
theorem owned_frame (kind : OwnerKind) (r : State) :
    (owned kind r).remaining = r.remaining ∧ (owned kind r).counter = r.counter ∧
      (owned kind r).buffer = r.buffer := ⟨rfl,rfl,rfl⟩
theorem ownerFuel_bound (kind : OwnerKind) (r : State) :
    ownerFuel kind r ≤ 12*(ownerWord kind r).length+24 := by
  have checked := TableOwner.query_fuel_bound (TableOwner.prepared r.counter (ownerWord kind r))
  change (TableOwner.queryResult (TableOwner.prepared r.counter (ownerWord kind r))).fuel ≤
    12*((ownerWord kind r).length+1)+1 at checked
  unfold ownerFuel
  omega
theorem owned_output_bound (kind : OwnerKind) (r : State) :
    (owned kind r).core.output.length ≤ r.counter.length+13*(ownerWord kind r).length+14 := by
  have execution := (TableOwner.query_exec (TableOwner.prepared r.counter (ownerWord kind r))).bounded
    (r.counter.length+(ownerWord kind r).length+1)
    (CompactClause.preparedOwner_bounded r.counter (ownerWord kind r))
  have output := Store.get_length_le
    (TableOwner.queryResult (TableOwner.prepared r.counter (ownerWord kind r))).state.store
    (8 : Fin 9) execution
  change (owned kind r).core.output.length ≤ r.counter.length+(ownerWord kind r).length+1+
    (TableOwner.queryResult (TableOwner.prepared r.counter (ownerWord kind r))).fuel at output
  have cost := ownerFuel_bound kind r
  unfold ownerFuel at cost
  omega
theorem owned_matching (r : State) (target : Nat) (table : MatchingTable.Entries)
    (index : r.counter = List.replicate target true) (matching : r.matching = MatchingTable.encode table) :
    (owned .matching r).core.output = TableOwner.answer (TableOwner.owner table target) := by
  change (TableOwner.queryResult (TableOwner.prepared r.counter r.matching)).state.output = _
  rw [index,matching]
  exact TableOwner.prepared_canonical target table
theorem owned_selected (r : State) (target : Nat) (vertices : List CNFLiteral)
    (index : r.counter = List.replicate target true)
    (selected : r.variables = SearchVertices.encodeVertices vertices) :
    (owned .selected r).core.output = TableOwner.answer (TableOwner.vertexOwner vertices target) := by
  change (TableOwner.queryResult (TableOwner.prepared r.counter r.variables)).state.output = _
  rw [index,selected]
  exact TableOwner.prepared_vertices target vertices

end PNP.Concrete.NormalizerBlocks.Recovery
