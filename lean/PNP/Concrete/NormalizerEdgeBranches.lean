/-
Copyright (c) 2026 PNP Labs.

Finite branch bodies for the complete directed graph query. Reversing
the endpoint roles swaps the stored indices by actual copy instructions;
a reverse edge reads the matching table, not a supplied relation answer.
-/

import PNP.Concrete.NormalizerForwardPolynomial

namespace PNP.Concrete.NormalizerBlocks.EdgeKinds

open BitRegister ForwardEdge

def swap : Block 14 :=
  .seq (.action (.copy 1 9)) (.seq (.action (.copy 9 10)) (.action (.copy 10 1)))
def swapped (r : ForwardEdge.State) : ForwardEdge.State :=
  {r with core := {r.core with target := r.target}, target := r.index, index := r.target}
theorem swap_exec (r : ForwardEdge.State) : Exec swap r.store 3 (swapped r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def normalize : Block 14 := .branch 8 (emit false) (emit false) (emit true)
def normalized (r : ForwardEdge.State) : ForwardEdge.State := emitted (present r.core.output) r

theorem normalize_exec (r : ForwardEdge.State) : Exec normalize r.store 3 (normalized r).store := by
  cases answer : r.core.output with
  | nil =>
      simpa only [normalize, normalized, present, answer, List.headD] using
        (Exec.empty (source := (8 : Fin 14)) (before := r.store) answer (emit_exec false r))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [normalize, normalized, present, answer, List.headD] using
            (Exec.zero (source := (8 : Fin 14)) (before := r.store) answer (emit_exec false r))
      | true =>
          simpa only [normalize, normalized, present, answer, List.headD] using
            (Exec.one (source := (8 : Fin 14)) (before := r.store) answer (emit_exec true r))

def reverse : Block 14 := .seq (prepare false) (.seq query normalize)
def reverseResult (r : ForwardEdge.State) : ForwardEdge.State := normalized (queried (ready false r))
def reverseFuel (r : ForwardEdge.State) : Nat := 15 + (GraphQuery.fuel (ready false r).core + 3)
theorem reverse_exec (r : ForwardEdge.State) :
    Exec reverse r.store (reverseFuel r) (reverseResult r).store :=
  Exec.seq (prepare_exec false r) (Exec.seq (query_exec (ready false r)) (normalize_exec (queried (ready false r))))

def forward : Block 14 := .seq swap phase
def forwardResult (r : ForwardEdge.State) : ForwardEdge.State := phaseResult (swapped r)
def forwardFuel (r : ForwardEdge.State) : Nat := 3 + phaseFuel (swapped r)
theorem forward_exec (r : ForwardEdge.State) :
    Exec forward r.store (forwardFuel r) (forwardResult r).store :=
  Exec.seq (swap_exec r) (phase_exec (swapped r))

def branchBound (r : ForwardEdge.State) : Nat :=
  188 * r.formula.length + 188 * r.matching.length + 40 * r.target.length + 40 * r.index.length + 604

theorem reverseFuel_bound (r : ForwardEdge.State) : reverseFuel r ≤ branchBound r := by
  have bound := GraphQuery.prepared_fuel_bound r.target r.index r.matching
  change 15 + (GraphQuery.fuel (GraphQuery.prepared r.target r.index r.matching) + 3) ≤
    188 * r.formula.length + 188 * r.matching.length + 40 * r.target.length + 40 * r.index.length + 604
  omega

theorem forwardFuel_bound (r : ForwardEdge.State) : forwardFuel r ≤ branchBound r := by
  have bound := phaseFuel_bound (swapped r)
  change phaseFuel (swapped r) + 1 ≤
    188 * r.formula.length + 188 * r.matching.length + 40 * r.index.length + 40 * r.target.length + 602 at bound
  change 3 + phaseFuel (swapped r) ≤
    188 * r.formula.length + 188 * r.matching.length + 40 * r.target.length + 40 * r.index.length + 604
  omega

theorem branchBound_pos (r : ForwardEdge.State) : 2 ≤ branchBound r := by
  unfold branchBound
  omega

theorem reverse_output (r : ForwardEdge.State) :
    (reverseResult r).core.output =
      [present (GraphQuery.result (GraphQuery.prepared r.target r.index r.matching)).output] := rfl

theorem forward_output (r : ForwardEdge.State) :
    (forwardResult r).core.output =
      [present (GraphQuery.result (GraphQuery.prepared r.index r.target r.formula)).output &&
        !present (GraphQuery.result (GraphQuery.prepared r.index r.target r.matching)).output] := rfl

theorem reverse_canonical (r : ForwardEdge.State) (variableIndex clause : Nat) (entries : MatchingTable.Entries)
    (targetRead : r.target = List.replicate variableIndex true)
    (indexRead : r.index = List.replicate clause true)
    (matchingRead : r.matching = MatchingTable.encode entries) :
    (reverseResult r).core.output = [MatchingTable.read entries clause == some variableIndex] := by
  rw [reverse_output, targetRead, indexRead, matchingRead]
  change [present (GraphQuery.result (GraphQuery.prepared _ _ (GraphQuery.clauseData (MatchingTable.clauses entries)))).output] = _
  rw [GraphQuery.result_canonical, present_answer, MatchingTable.clauses_read, MatchingRelation.entry_matches]

theorem forward_canonical (r : ForwardEdge.State) (clause variableIndex : Nat)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (targetRead : r.target = List.replicate clause true)
    (indexRead : r.index = List.replicate variableIndex true)
    (formulaRead : r.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.matching = MatchingTable.encode entries) :
    (forwardResult r).core.output = [ForwardEdge.value variableIndex clause clauses entries] := by
  rw [forward_output, targetRead, indexRead, formulaRead, matchingRead]
  change [present (GraphQuery.result (GraphQuery.prepared _ _ (GraphQuery.clauseData clauses))).output &&
    !present (GraphQuery.result (GraphQuery.prepared _ _ (GraphQuery.clauseData (MatchingTable.clauses entries)))).output] = _
  rw [GraphQuery.result_canonical, GraphQuery.result_canonical, present_answer, present_answer,
    MatchingTable.clauses_read, MatchingRelation.entry_matches]
  rfl

end PNP.Concrete.NormalizerBlocks.EdgeKinds
