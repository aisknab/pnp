/-
Copyright (c) 2026 PNP Labs.

Computed zero/unary descent distinguishes proper R7 gains from whole-span
residual descents. All computational fields remain actual source observations.
No supplied support family, replacement, rank or compiler result is an input.

This is a computational route component, not complete manuscript
normalization, global minimality, ZeroSlack or polynomial-time PCCMin.
-/

import PNP.NANDWireUnarySupportSearch

namespace PNP.DirectWire.WireZeroUnaryClosure

open WireUnaryArbitrarySupport

variable {inputs outputs fields : Nat}

/-- The whole support is derived from every original physical gate. -/
def wholeRecords (carrier : WireCarrier inputs outputs fields) :
    List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount
      (outputs + fields) 0) :=
  WireUnarySupportSearch.gateRecords (fun _ => true)

theorem whole_selected (carrier : WireCarrier inputs outputs fields) :
    terminalGateSelected (wholeRecords carrier) = (fun _ => true) :=
  WireUnarySupportSearch.gateRecords_selected _

/-- Whole-span replacement has no retained exterior, unlike a proper local gain. -/
theorem whole_exterior (carrier : WireCarrier inputs outputs fields) :
    exteriorCharge carrier (wholeRecords carrier) = 0 := by
  by_cases positive : 0 < exteriorCharge carrier (wholeRecords carrier)
  · have asLength : 0 < (ArbitrarySupportSplice.exterior (wholeRecords carrier)).length :=
      positive
    obtain ⟨gate, member⟩ := List.length_pos_iff_exists_mem.mp asLength
    have absent := (ArbitrarySupportSplice.mem_exterior_iff (wholeRecords carrier) gate).1 member
    have present := congrFun (whole_selected carrier) gate
    rw [present] at absent
    cases absent
  · omega

theorem whole_gateCount (carrier : WireCarrier inputs outputs fields) :
    (pulled carrier (wholeRecords carrier)).gateCount = carrier.implementation.gateCount := by
  have accounting := original_charge carrier (wholeRecords carrier)
  rw [whole_exterior, Nat.add_zero] at accounting
  exact accounting.symm

/-- A whole-span branch cannot be advertised as a proper-support VerifyDW gain. -/
theorem whole_not_proper (carrier : WireCarrier inputs outputs fields) :
    ¬ (pulled carrier (wholeRecords carrier)).gateCount < carrier.implementation.gateCount := by
  rw [whole_gateCount]
  exact Nat.lt_irrefl _

/-- Zero actual exterior forces every original gate into the physical support. -/
theorem all_gates_of_zero_exterior (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount
      (outputs + fields) 0))
    (empty : exteriorCharge carrier records = 0) :
    terminalGateSelected records = (fun _ => true) := by
  funext gate
  cases selectedAt : terminalGateSelected records gate with
  | true => rfl
  | false =>
      have member := (ArbitrarySupportSplice.mem_exterior_iff records gate).2 selectedAt
      have positive : 0 < exteriorCharge carrier records :=
        List.length_pos_iff_exists_mem.mpr ⟨gate, member⟩
      rw [empty] at positive
      exact False.elim (Nat.lt_irrefl 0 positive)

/-- A checked strict whole-span word, not a proper-support local certificate. -/
structure WholeGain (carrier : WireCarrier inputs outputs fields) : Type where
  small : (pulled carrier (wholeRecords carrier)).boundary.length ≤ 1
  smaller : (replacement carrier (wholeRecords carrier) small).gateCount <
    (pulled carrier (wholeRecords carrier)).gateCount

/-- The actual compiled whole-span replacement with every full field restored. -/
def WholeGain.expanded {carrier : WireCarrier inputs outputs fields}
    (gain : WholeGain carrier) : WireCarrier inputs outputs fields :=
  WireUnaryArbitrarySupport.expanded carrier (wholeRecords carrier) gain.small

def WholeGain.strictGain {carrier : WireCarrier inputs outputs fields}
    (gain : WholeGain carrier) :
    StrictEquivalentGain carrier.implementation gain.expanded.implementation where
  smaller := (expanded_gain_iff carrier (wholeRecords carrier) gain.small).2 gain.smaller
  equivalent := expanded_equivalent carrier (wholeRecords carrier) gain.small

theorem WholeGain.checked {carrier : WireCarrier inputs outputs fields}
    (gain : WholeGain carrier) :
    exteriorCharge carrier (wholeRecords carrier) = 0 ∧
      StrictEquivalentGain carrier.implementation gain.expanded.implementation ∧
      (∀ valuation field, gain.expanded.fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      gain.expanded.implementation.gateCount =
        (replacement carrier (wholeRecords carrier) gain.small).gateCount := by
  refine ⟨whole_exterior carrier, gain.strictGain,
    expanded_field carrier (wholeRecords carrier) gain.small, ?_⟩
  exact (expanded_charge carrier (wholeRecords carrier) gain.small).trans
    (by rw [whole_exterior, Nat.add_zero])

/-- Compute the actual whole support and local minimum, then require strict saving. -/
def wholeGain (carrier : WireCarrier inputs outputs fields) : Option (WholeGain carrier) :=
  if small : (pulled carrier (wholeRecords carrier)).boundary.length ≤ 1 then
    if smaller : (replacement carrier (wholeRecords carrier) small).gateCount <
        (pulled carrier (wholeRecords carrier)).gateCount then
      some ⟨small, smaller⟩
    else none
  else none

theorem wholeGain_isSome_iff (carrier : WireCarrier inputs outputs fields) :
    (wholeGain carrier).isSome = true ↔
      ∃ small : (pulled carrier (wholeRecords carrier)).boundary.length ≤ 1,
        (replacement carrier (wholeRecords carrier) small).gateCount <
          (pulled carrier (wholeRecords carrier)).gateCount := by
  unfold wholeGain
  split
  next small =>
    split
    next smaller => exact ⟨fun _ => ⟨small, smaller⟩, fun _ => rfl⟩
    next notSmaller =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨otherSmall, smaller⟩
        exact False.elim (notSmaller smaller)
  next notSmall =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨small, _⟩
      exact False.elim (notSmall small)

/-- Every cheaper complete zero/unary whole-support word triggers actual descent.
The comparison word and semantic equality are not executable search inputs. -/
theorem wholeGain_complete (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount
      (outputs + fields) 0))
    (small : (pulled carrier records).boundary.length ≤ 1)
    (empty : exteriorCharge carrier records = 0)
    (other : Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics)
    (smaller : other.gateCount < (pulled carrier records).gateCount) :
    (wholeGain carrier).isSome = true := by
  let property (support : TerminalExtractedSupport (profileWidth := 0)
      carrier.exposed.candidate) : Prop :=
    ∃ small : support.boundary.length ≤ 1,
      (WireUnaryFrontier.localWord support.extractedCandidate.toImplementation small).gateCount <
        support.gateCount
  have originalProperty : property (pulled carrier records) :=
    ⟨small, Nat.lt_of_le_of_lt (replacement_minimal carrier records small other sameOpen) smaller⟩
  have selection : terminalGateSelected records = terminalGateSelected (wholeRecords carrier) :=
    (all_gates_of_zero_exterior carrier records empty).trans (whole_selected carrier).symm
  have equal := extractTerminalSupport_eq_of_gateSelected_eq
    carrier.exposed.candidate records (wholeRecords carrier) selection
  have wholeProperty : property (pulled carrier (wholeRecords carrier)) := by
    change property (extractTerminalSupport carrier.exposed.candidate (wholeRecords carrier))
    rw [← equal]
    exact originalProperty
  exact (wholeGain_isSome_iff carrier).2 wholeProperty

/-- Proper local R7 gain and whole-span residual descent are distinct data. -/
inductive Gain (carrier : WireCarrier inputs outputs fields) : Type where
  | proper (result : WireUnarySupportSearch.GainResult carrier)
  | wholeSpan (result : WholeGain carrier)

/-- Each branch returns its actual complete compiled replacement. -/
def Gain.expanded {carrier : WireCarrier inputs outputs fields} :
    Gain carrier → WireCarrier inputs outputs fields
  | .proper result => result.expanded
  | .wholeSpan result => result.expanded

def Gain.strictGain {carrier : WireCarrier inputs outputs fields} :
    (gain : Gain carrier) →
      StrictEquivalentGain carrier.implementation gain.expanded.implementation
  | .proper result => result.gain.strictGain
  | .wholeSpan result => result.strictGain

/-- Complete field equality accompanies both kinds of actual strict descent. -/
theorem Gain.full_field {carrier : WireCarrier inputs outputs fields}
    (gain : Gain carrier) (valuation : Valuation inputs) (field : Fin fields) :
    gain.expanded.fieldValue valuation field = carrier.fieldValue valuation field := by
  cases gain with
  | proper result => exact result.checked.2.2.2.1 valuation field
  | wholeSpan result => exact result.checked.2.2.1 valuation field

/-- The returned branch records the correct physical proper/whole distinction. -/
theorem Gain.branch_boundary {carrier : WireCarrier inputs outputs fields}
    (gain : Gain carrier) :
    match gain with
    | .proper result => 0 < exteriorCharge carrier result.records
    | .wholeSpan _ => exteriorCharge carrier (wholeRecords carrier) = 0 := by
  cases gain with
  | proper result => exact result.gain.proper
  | wholeSpan _ => exact whole_exterior carrier

def Gain.savedGates {carrier : WireCarrier inputs outputs fields}
    (gain : Gain carrier) : Nat :=
  carrier.implementation.gateCount - gain.expanded.implementation.gateCount

theorem Gain.exact_accounting {carrier : WireCarrier inputs outputs fields}
    (gain : Gain carrier) :
    gain.expanded.implementation.gateCount + gain.savedGates =
        carrier.implementation.gateCount ∧
      0 < gain.savedGates := by
  have smaller := gain.strictGain.smaller
  unfold Gain.savedGates
  constructor <;> omega

/-- Proper supports retain priority; the whole-span fallback is separately typed. -/
def nextGain (carrier : WireCarrier inputs outputs fields) : Option (Gain carrier) :=
  match WireUnarySupportSearch.findGain carrier with
  | some result => some (.proper result)
  | none => (wholeGain carrier).map Gain.wholeSpan

/-- The combined recognizer succeeds exactly when one actual branch succeeds. -/
theorem nextGain_isSome_iff (carrier : WireCarrier inputs outputs fields) :
    (nextGain carrier).isSome = true ↔
      (WireUnarySupportSearch.findGain carrier).isSome = true ∨
        (wholeGain carrier).isSome = true := by
  unfold nextGain
  cases properAt : WireUnarySupportSearch.findGain carrier with
  | some result =>
      exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | none =>
      cases wholeAt : wholeGain carrier with
      | some result => exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
      | none =>
          constructor
          · intro impossible
            cases impossible
          · intro impossible
            rcases impossible with impossible | impossible <;> cases impossible

/-- A negative result excludes both branches on this same actual carrier. -/
theorem nextGain_none_iff (carrier : WireCarrier inputs outputs fields) :
    nextGain carrier = none ↔
      WireUnarySupportSearch.findGain carrier = none ∧ wholeGain carrier = none := by
  unfold nextGain
  cases properAt : WireUnarySupportSearch.findGain carrier with
  | some result =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨impossible, _⟩
        cases impossible
  | none =>
      cases wholeAt : wholeGain carrier with
      | some result =>
          constructor
          · intro impossible
            cases impossible
          · rintro ⟨_, impossible⟩
            cases impossible
      | none => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- Every cheaper complete zero/unary local word triggers an actual descent,
without requiring a supplied support, family or properness premise in the search. -/
theorem nextGain_complete (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount
      (outputs + fields) 0))
    (small : (pulled carrier records).boundary.length ≤ 1)
    (other : Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics)
    (smaller : other.gateCount < (pulled carrier records).gateCount) :
    (nextGain carrier).isSome = true := by
  apply (nextGain_isSome_iff carrier).2
  by_cases proper : 0 < exteriorCharge carrier records
  · exact Or.inl (WireUnarySupportSearch.findGain_complete
      carrier records small proper other sameOpen smaller)
  · have empty : exteriorCharge carrier records = 0 := by omega
    exact Or.inr (wholeGain_complete carrier records small empty other sameOpen smaller)

/-- Absence excludes all zero/unary support savings, including whole-span ones.
It does not rule out wider-boundary improvements or establish global minimality. -/
theorem nextGain_none_excludes (carrier : WireCarrier inputs outputs fields)
    (notFound : nextGain carrier = none)
    (records : List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount
      (outputs + fields) 0))
    (small : (pulled carrier records).boundary.length ≤ 1)
    (other : Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) :
    (pulled carrier records).gateCount ≤ other.gateCount := by
  by_cases smaller : other.gateCount < (pulled carrier records).gateCount
  · have accepted := nextGain_complete carrier records small other sameOpen smaller
    rw [notFound] at accepted
    cases accepted
  · omega

/-- Actual physical savings from the all-fields-visible normalization stage. -/
def normalizationSaved (carrier : WireCarrier inputs outputs fields) : Nat :=
  (runPhysicalNormalization carrier.exposed).trace.savedGates

def normalizationIterations (carrier : WireCarrier inputs outputs fields) : Nat :=
  (runPhysicalNormalization carrier.exposed).trace.gainIterations

theorem normalization_accounting (carrier : WireCarrier inputs outputs fields) :
    carrier.normalize.implementation.gateCount + normalizationSaved carrier =
      carrier.implementation.gateCount :=
  carrier.normalize_exact_accounting

theorem normalization_iterations (carrier : WireCarrier inputs outputs fields) :
    normalizationIterations carrier ≤ normalizationSaved carrier :=
  (runPhysicalNormalization_checked carrier.exposed).2.2.2

/-- Every trace edge re-normalizes the complete carrier and records the actual
search result. Its endpoint stops only after the same normalized carrier has no gain. -/
inductive Trace : WireCarrier inputs outputs fields →
    WireCarrier inputs outputs fields → Type where
  | done (current : WireCarrier inputs outputs fields)
      (stopped : nextGain current.normalize = none) :
      Trace current current.normalize
  | step (current : WireCarrier inputs outputs fields)
      (gain : Gain current.normalize)
      (found : nextGain current.normalize = some gain)
      {final : WireCarrier inputs outputs fields}
      (tail : Trace gain.expanded final) :
      Trace current final

def Trace.savedGates {current final : WireCarrier inputs outputs fields} :
    Trace current final → Nat
  | .done current _ => normalizationSaved current
  | .step current gain _ tail =>
      normalizationSaved current + gain.savedGates + tail.savedGates

/-- Count actual physical-normalization gains and actual support descents. -/
def Trace.gainIterations {current final : WireCarrier inputs outputs fields} :
    Trace current final → Nat
  | .done current _ => normalizationIterations current
  | .step current _ _ tail => normalizationIterations current + 1 + tail.gainIterations

/-- Count combined support-search calls, including the final negative call. -/
def Trace.searchCalls {current final : WireCarrier inputs outputs fields} :
    Trace current final → Nat
  | .done _ _ => 1
  | .step _ _ _ tail => tail.searchCalls + 1

theorem Trace.checked {current final : WireCarrier inputs outputs fields}
    (trace : Trace current final) :
    Equivalent final.implementation.candidate.program final.implementation.candidate.directWireWord
        current.implementation.candidate.program current.implementation.candidate.directWireWord ∧
      (∀ valuation field, final.fieldValue valuation field = current.fieldValue valuation field) ∧
      PhysicalNormalizationQuiescent final.exposed ∧
      nextGain final = none ∧
      final.implementation.gateCount + trace.savedGates = current.implementation.gateCount ∧
      trace.gainIterations ≤ trace.savedGates := by
  induction trace with
  | done current stopped =>
      exact ⟨WireCarrier.normalize_output current, WireCarrier.normalize_field current,
        current.normalize_quiescent, stopped, normalization_accounting current,
        normalization_iterations current⟩
  | step current gain found tail ih =>
      obtain ⟨equivalent, full, quiet, notFound, accounting, iterations⟩ := ih
      have normalAccounting := normalization_accounting current
      have normalIterations := normalization_iterations current
      have gainAccounting := gain.exact_accounting.1
      have gainPositive := gain.exact_accounting.2
      refine ⟨Equivalent.trans equivalent
          (Equivalent.trans gain.strictGain.equivalent (WireCarrier.normalize_output current)),
        ?_, quiet, notFound, ?_, ?_⟩
      · intro valuation field
        exact (full valuation field).trans
          ((gain.full_field valuation field).trans (current.normalize_field valuation field))
      · change _ + (normalizationSaved current + gain.savedGates + tail.savedGates) = _
        omega
      · change normalizationIterations current + 1 + tail.gainIterations ≤
          normalizationSaved current + gain.savedGates + tail.savedGates
        omega

theorem Trace.searchCalls_le {current final : WireCarrier inputs outputs fields}
    (trace : Trace current final) :
    trace.searchCalls ≤ trace.gainIterations + 1 := by
  induction trace with
  | done current stopped =>
      change 1 ≤ normalizationIterations current + 1
      omega
  | step current gain found tail ih =>
      change tail.searchCalls + 1 ≤ normalizationIterations current + 1 + tail.gainIterations + 1
      omega

/-- The result and its complete trace are computed, not supplied by the caller. -/
structure Execution (current : WireCarrier inputs outputs fields) where
  result : WireCarrier inputs outputs fields
  trace : Trace current result

/-- Normalize all fields, find the next typed descent, and repeat after every gain.
A negative search is a scoped stopping condition, never a ZeroSlack certificate. -/
def run (current : WireCarrier inputs outputs fields) : Execution current :=
  match found : nextGain current.normalize with
  | none =>
      { result := current.normalize
        trace := .done current found }
  | some gain =>
      let tail := run gain.expanded
      { result := tail.result
        trace := .step current gain found tail.trace }
termination_by current.implementation.gateCount
decreasing_by
  have normalBound : current.normalize.implementation.gateCount ≤ current.implementation.gateCount :=
    Nat.le.intro (normalization_accounting current)
  exact Nat.lt_of_lt_of_le gain.strictGain.smaller normalBound

/-- General end-to-end full fields, common stopping, exact charge and iteration bound. -/
theorem run_checked (carrier : WireCarrier inputs outputs fields) :
    let execution := run carrier
    Equivalent execution.result.implementation.candidate.program
        execution.result.implementation.candidate.directWireWord
        carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord ∧
      (∀ valuation field, execution.result.fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      PhysicalNormalizationQuiescent execution.result.exposed ∧
      nextGain execution.result = none ∧
      execution.result.implementation.gateCount + execution.trace.savedGates =
        carrier.implementation.gateCount ∧
      execution.trace.gainIterations ≤ execution.trace.savedGates :=
  (run carrier).trace.checked

/-- A common fixed point is returned unchanged, not merely with equal semantics. -/
theorem run_of_stopped (carrier : WireCarrier inputs outputs fields)
    (quiet : PhysicalNormalizationQuiescent carrier.exposed)
    (absent : nextGain carrier = none) :
    (run carrier).result = carrier := by
  have normalized : carrier.normalize = carrier := by
    unfold WireCarrier.normalize
    rw [runPhysicalNormalization_of_quiescent carrier.exposed quiet]
    exact WireCarrier.unpack_exposed carrier
  have stopped : nextGain carrier.normalize = none := by
    rw [normalized]
    exact absent
  rw [run]
  split
  · exact normalized
  · rename_i gain found
    have impossible : (none : Option (Gain carrier.normalize)) = some gain :=
      stopped.symm.trans found
    cases impossible

/-- Re-executing the complete computed closure cannot restart a missed branch. -/
theorem run_idempotent (carrier : WireCarrier inputs outputs fields) :
    (run (run carrier).result).result = (run carrier).result :=
  run_of_stopped _ (run_checked carrier).2.2.1 (run_checked carrier).2.2.2.1

/-- The final carrier has no cheaper complete zero/unary open support word.
This ranges over every physical support; it is not global minimality. -/
theorem run_no_smaller_zeroUnary (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      (run carrier).result.implementation.gateCount (outputs + fields) 0))
    (small : (pulled (run carrier).result records).boundary.length ≤ 1)
    (other : Implementation (pulled (run carrier).result records).boundary.length
      (pulled (run carrier).result records).interface.length)
    (sameOpen : other.candidate.semantics =
      (pulled (run carrier).result records).extractedCandidate.semantics) :
    (pulled (run carrier).result records).gateCount ≤ other.gateCount :=
  nextGain_none_excludes _ (run_checked carrier).2.2.2.1 records small other sameOpen

/-- Reference minima appear in the specification only, never in execution. -/
theorem run_referenceMinimum (carrier : WireCarrier inputs outputs fields) :
    referenceMinimum (run carrier).result.implementation =
      referenceMinimum carrier.implementation :=
  referenceMinimum_invariant _ _ (run_checked carrier).1

/-- The actual computed trace removes exactly its physical saving from slack. -/
theorem run_residualSlack (carrier : WireCarrier inputs outputs fields) :
    residualSlack carrier.implementation =
      residualSlack (run carrier).result.implementation + (run carrier).trace.savedGates := by
  have accounting := (run_checked carrier).2.2.2.2.1
  have bounded := referenceMinimum_le_target (run carrier).result.implementation
  have sameMinimum := run_referenceMinimum carrier
  unfold residualSlack
  rw [sameMinimum] at bounded ⊢
  omega

/-- This bounds strict gain iterations, not the runtime of the complete search. -/
theorem run_gainIterations_le_residualSlack (carrier : WireCarrier inputs outputs fields) :
    (run carrier).trace.gainIterations ≤ residualSlack carrier.implementation := by
  have iterations := (run_checked carrier).2.2.2.2.2
  have slack := run_residualSlack carrier
  omega

/-- One final negative search follows the successful descents. The bound does not
establish encoded-size polynomial time for normalization or support construction. -/
theorem run_searchCalls_le_residualSlack (carrier : WireCarrier inputs outputs fields) :
    (run carrier).trace.searchCalls ≤ residualSlack carrier.implementation + 1 :=
  Nat.le_trans (run carrier).trace.searchCalls_le
    (Nat.add_le_add_right (run_gainIterations_le_residualSlack carrier) 1)

end PNP.DirectWire.WireZeroUnaryClosure
