/-
Copyright (c) 2026 PNP Labs.

Restore a discarded variable from the original matching and the first actual
occurrence in its owner clause. Missing owners or occurrences return false.
No literal sign is supplied to the finite program.
-/
import PNP.Concrete.NormalizerRecoveryOwner

namespace PNP.Concrete.NormalizerBlocks.Recovery
open BitRegister Occurrence

def loadOccurrence : Block 16 :=
  .seq (.action (.copy 1 8)) <| .seq (.action (.pop 1)) <|
  .seq (.action (.copy 2 1)) <| .seq (.action (.copy 0 9)) <|
  .seq (.action (.copy 3 14)) (.action (.push 3 false))
def occurrenceLoaded (r : State) : State :=
  r.withCore {r.core with
    target := r.core.output.tail,remaining := r.core.output.tail,
    input := r.formula,excess := false::r.counter}
theorem loadOccurrence_exec (r : State) :
    Exec loadOccurrence r.store 6 (occurrenceLoaded r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
def clearOccurrence : Block 16 :=
  .seq (.action (.clear 4)) <| .seq (.action (.clear 5)) <|
  .seq (.action (.clear 6)) <| .seq (.action (.clear 7)) (.action (.clear 8))
def occurrenceCleared (r : State) : State :=
  r.withCore {r.core with sign := [],mode := [],active := [],reserved := [],output := []}
theorem clearOccurrence_exec (r : State) :
    Exec clearOccurrence r.store 5 (occurrenceCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
    (Exec.seq (.action _ _) (.action _ _))))
def activateOccurrence : Block 16 := .seq (.action (.push 6 true)) (.action (.copy 7 14))
def occurrenceActivated (r : State) : State :=
  r.withCore {r.core with active := true::r.core.active,reserved := r.counter}
theorem activateOccurrence_exec (r : State) :
    Exec activateOccurrence r.store 2 (occurrenceActivated r).store :=
  Exec.seq (.action _ _) (.action _ _)
def prepareOccurrence : Block 16 := .seq loadOccurrence (.seq clearOccurrence activateOccurrence)
def occurrencePrepared (r : State) : State :=
  r.withCore (GraphQuery.prepared r.counter r.core.output.tail r.formula)
theorem prepareOccurrence_exec (r : State) :
    Exec prepareOccurrence r.store 13 (occurrencePrepared r).store :=
  Exec.seq (loadOccurrence_exec r)
    (Exec.seq (clearOccurrence_exec (occurrenceLoaded r))
      (activateOccurrence_exec (occurrenceCleared (occurrenceLoaded r))))
def occurrence : Block 16 := .seq prepareOccurrence (lift GraphQuery.block)
def occurrenceResult (r : State) : State :=
  r.withCore (GraphQuery.result (GraphQuery.prepared r.counter r.core.output.tail r.formula))
def occurrenceFuel (r : State) : Nat :=
  13+GraphQuery.fuel (GraphQuery.prepared r.counter r.core.output.tail r.formula)
theorem occurrence_exec (r : State) :
    Exec occurrence r.store (occurrenceFuel r) (occurrenceResult r).store :=
  Exec.seq (prepareOccurrence_exec r)
    (lift_exec _ (occurrencePrepared r) _ _ (GraphQuery.block_exec _))

def emit (bit : Bool) : Block 16 := lift (TraceCount.emit bit)
def emitted (bit : Bool) (r : State) : State := r.withCore (TraceCount.emitted bit r.core)
theorem emit_exec (bit : Bool) (r : State) :
    Exec (emit bit) r.store 2 (emitted bit r).store := lift_exec _ r _ _ (TraceCount.emit_exec _ _)
def signHead : Block 16 := .branch 8 (emit false) (emit false) (emit true)
theorem signHead_exec (r : State) :
    Exec signHead r.store 3 (emitted (r.core.output.headD false) r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 16) r.store
    (emit false) (emit true) 2 2 (emitted false r).store (emitted true r).store
    (emit_exec false r) (emit_exec true r)
  change Exec signHead r.store (1+if r.core.output.headD false then 2 else 2)
    (if r.core.output.headD false then (emitted true r).store else (emitted false r).store) at checked
  cases h : r.core.output.headD false <;>
    simpa only [h,Bool.false_eq_true,ite_false,ite_true] using checked
def sign : Block 16 := .seq (.action (.pop 8)) signHead
def signed (r : State) : State := emitted (r.core.output.tail.headD false) r
theorem sign_exec (r : State) : Exec sign r.store 4 (signed r).store := by
  have pop : Exec (.action (.pop (8 : Fin 16))) r.store 1
      (r.withCore {r.core with output := r.core.output.tail}).store := .action _ _
  exact Exec.seq pop (signHead_exec (r.withCore {r.core with output := r.core.output.tail}))
def literal : Block 16 := .seq occurrence sign
def literalResult (r : State) : State := signed (occurrenceResult r)
def literalFuel (r : State) : Nat := occurrenceFuel r+4
theorem literal_exec (r : State) :
    Exec literal r.store (literalFuel r) (literalResult r).store :=
  Exec.seq (occurrence_exec r) (sign_exec (occurrenceResult r))
theorem literalFuel_bound (r : State) :
    literalFuel r ≤ 188*r.formula.length+20*r.counter.length+20*r.core.output.length+300 := by
  have cost := GraphQuery.prepared_fuel_bound r.counter r.core.output.tail r.formula
  have tail := ParentQuery.input_tail_bound r.core.output
  unfold literalFuel occurrenceFuel
  omega
def literalValue (formula : List (List CNFLiteral)) (target row : Nat) : Bool :=
  (((formula[row]?.getD []).find? (fun lit => lit.variableIndex == target)).map CNFLiteral.positive).getD false
theorem literal_canonical (r : State) (formula : List (List CNFLiteral)) (target row : Nat)
    (data : r.formula = GraphQuery.clauseData formula)
    (index : r.counter = List.replicate target true)
    (owner : r.core.output = TableOwner.answer (some row)) :
    (literalResult r).core.output = [literalValue formula target row] := by
  change [(GraphQuery.result (GraphQuery.prepared r.counter r.core.output.tail r.formula)).output.tail.headD false] = _
  rw [data,index,owner]
  change [(GraphQuery.result (GraphQuery.prepared (List.replicate target true)
    (List.replicate row true) (GraphQuery.clauseData formula))).output.tail.headD false] = _
  rw [GraphQuery.result_canonical]
  unfold literalValue
  cases (formula[row]?.getD []).find? (fun lit => lit.variableIndex == target) <;> rfl

def choosePreferred : Block 16 := .branch 8 (emit false) (emit false) literal
def preferredChosen (r : State) : State :=
  if r.core.output.headD false then literalResult r else emitted false r
def choosePreferredFuel (r : State) : Nat :=
  1+if r.core.output.headD false then literalFuel r else 2
theorem choosePreferred_exec (r : State) :
    Exec choosePreferred r.store (choosePreferredFuel r) (preferredChosen r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 16) r.store
    (emit false) literal 2 (literalFuel r) (emitted false r).store (literalResult r).store
    (emit_exec false r) (literal_exec r)
  change Exec choosePreferred r.store (choosePreferredFuel r)
    (if r.core.output.headD false then (literalResult r).store else (emitted false r).store) at checked
  cases h : r.core.output.headD false <;>
    simpa only [preferredChosen,h,Bool.false_eq_true,ite_false,ite_true] using checked
def preferred : Block 16 := .seq (owner .matching) choosePreferred
def preferredResult (r : State) : State := preferredChosen (owned .matching r)
def preferredFuel (r : State) : Nat := ownerFuel .matching r+choosePreferredFuel (owned .matching r)
theorem preferred_exec (r : State) :
    Exec preferred r.store (preferredFuel r) (preferredResult r).store :=
  Exec.seq (owner_exec .matching r) (choosePreferred_exec (owned .matching r))
theorem preferred_frame (r : State) :
    (preferredResult r).frame = r.frame := by
  unfold preferredResult preferredChosen
  split <;> rfl
theorem preferredFuel_bound (r : State) (n : Nat)
    (formula : r.formula.length ≤ n) (matching : r.matching.length ≤ n)
    (index : r.counter.length ≤ n) : preferredFuel r ≤ 500*n+605 := by
  have first := ownerFuel_bound .matching r
  have output := owned_output_bound .matching r
  have last := literalFuel_bound (owned .matching r)
  change ownerFuel .matching r ≤ 12*r.matching.length+24 at first
  change (owned .matching r).core.output.length ≤ r.counter.length+13*r.matching.length+14 at output
  change literalFuel (owned .matching r) ≤
    188*r.formula.length+20*r.counter.length+20*(owned .matching r).core.output.length+300 at last
  unfold preferredFuel choosePreferredFuel
  split <;> omega
def preferredValue (formula : List (List CNFLiteral)) (table : MatchingTable.Entries) (target : Nat) : Bool :=
  match TableOwner.owner table target with
  | none => false
  | some row => literalValue formula target row
theorem preferred_canonical (r : State) (formula : List (List CNFLiteral)) (table : MatchingTable.Entries)
    (target : Nat) (data : r.formula = GraphQuery.clauseData formula)
    (matching : r.matching = MatchingTable.encode table) (index : r.counter = List.replicate target true) :
    (preferredResult r).core.output = [preferredValue formula table target] := by
  have found := owned_matching r target table index matching
  cases h : TableOwner.owner table target with
  | none =>
      rw [h] at found
      simp only [preferredResult,preferredChosen,found,TableOwner.answer,List.headD_cons,
        Bool.false_eq_true,ite_false,preferredValue,h]
      rfl
  | some row =>
      rw [h] at found
      simp only [preferredResult,preferredChosen,found,TableOwner.answer,List.headD_cons,
        ite_true,preferredValue,h]
      exact literal_canonical (owned .matching r) formula target row data index found

end PNP.Concrete.NormalizerBlocks.Recovery
