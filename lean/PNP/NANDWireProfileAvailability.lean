import PNP.NANDWireProfileExposure
import PNP.ResidualTerminalProjectionMinimum

/-!
Research construction: target-relative availability of existing computational
sources. Availability is computed, not supplied as a correctness certificate.
It is not a value encoding of arbitrary field bindings and is not the complete
manuscript profile grammar. Truth-table enumeration is not polynomial time.
-/

namespace PNP.DirectWire.WireProfileAvailability

variable {inputs outputs fields : Nat}

def sourceMatches (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields)
    (source : Source inputs offered.gateCount) : Bool :=
  allTrue (allBoolTuples inputs) fun tuple =>
    boolEqual
      (source.eval tuple.toValuation
        (offered.candidate.program.eval tuple.toValuation))
      (target.fieldValue tuple.toValuation field)

theorem sourceMatches_iff (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields)
    (source : Source inputs offered.gateCount) :
    sourceMatches target offered field source = true ↔
      ∀ valuation, source.eval valuation (offered.candidate.program.eval valuation) =
        target.fieldValue valuation field := by
  constructor
  · intro checked valuation
    have atTuple := allTrue_sound checked (mem_allBoolTuples (BoolTuple.ofFn valuation))
    have valuationEqual : (BoolTuple.ofFn valuation).toValuation = valuation :=
      funext (BoolTuple.toValuation_ofFn valuation)
    have same := (boolEqual_eq_true_iff _ _).mp atTuple
    rw [valuationEqual] at same
    exact same
  · intro same
    apply allTrue_complete
    intro tuple _member
    exact (boolEqual_eq_true_iff _ _).mpr (same tuple.toValuation)

def findSource (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields) :
    Option (Source inputs offered.gateCount) :=
  (allSources inputs offered.gateCount).find? (sourceMatches target offered field)

def available (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields) : Bool :=
  (findSource target offered field).isSome

theorem findSource_sound (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields)
    (source : Source inputs offered.gateCount)
    (found : findSource target offered field = some source) :
    ∀ valuation, source.eval valuation (offered.candidate.program.eval valuation) =
      target.fieldValue valuation field :=
  (sourceMatches_iff target offered field source).mp (List.find?_some found)

theorem available_of_source (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields)
    (source : Source inputs offered.gateCount)
    (same : ∀ valuation,
      source.eval valuation (offered.candidate.program.eval valuation) =
        target.fieldValue valuation field) :
    available target offered field = true :=
  (List.find?_isSome).mpr
    ⟨source, mem_allSources source, (sourceMatches_iff target offered field source).mpr same⟩

theorem current_available (target : WireCarrier inputs outputs fields)
    (field : Fin fields) :
    available target target.implementation field = true :=
  available_of_source target target.implementation field (target.source field)
    (fun _ => rfl)

def bind (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) : WireCarrier inputs outputs fields :=
  { implementation := offered
    source := fun field => (findSource target offered field).getD (.constant false) }

theorem bind_implementation (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) :
    (bind target offered).implementation = offered := rfl

theorem bind_gateCount (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) :
    (bind target offered).implementation.gateCount = offered.gateCount := rfl

theorem bind_fieldValue (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (field : Fin fields)
    (present : available target offered field = true) (valuation : Valuation inputs) :
    (bind target offered).fieldValue valuation field = target.fieldValue valuation field := by
  cases found : findSource target offered field with
  | none =>
      unfold available at present
      rw [found] at present
      cases present
  | some source =>
      change ((findSource target offered field).getD (.constant false)).eval
        valuation (offered.candidate.program.eval valuation) = _
      rw [found]
      exact findSource_sound target offered field source found valuation

def system (target : WireCarrier inputs outputs fields) :
    TerminalProfileSystem inputs outputs fields :=
  { role := fun _ => .carrier
    observe := available target }

def fullComparison (target offered : WireCarrier inputs outputs fields)
    (same : WireProfile.FullEquivalent target offered) :
    TerminalFullCarrierRealization (system target) target.implementation :=
  { realization :=
      { implementation := offered.implementation
        equivalent := ((WireProfile.full_iff target offered).mp same).1 }
    profileEqual := by
      intro field
      exact (available_of_source target offered.implementation field (offered.source field)
        (fun valuation => ((WireProfile.full_iff target offered).mp same).2 valuation field)).trans
          (current_available target field).symm }

def quotientComparison (target offered : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (same : WireProfile.QuotientEquivalent keep target offered) :
    TerminalQuotientComparison (system target) ⟨keep⟩ target.implementation :=
  { realization :=
      { implementation := offered.implementation
        equivalent := ((WireProfile.quotient_iff keep target offered).mp same).1 }
    keptProfileEqual := by
      intro field kept
      exact (available_of_source target offered.implementation field (offered.source field)
        (fun valuation =>
          ((WireProfile.quotient_iff keep target offered).mp same).2 valuation field kept)).trans
          (current_available target field).symm }

theorem bind_full (target : WireCarrier inputs outputs fields)
    (full : TerminalFullCarrierRealization (system target) target.implementation) :
    WireProfile.FullEquivalent target (bind target full.realization.implementation) := by
  apply (WireProfile.full_iff target (bind target full.realization.implementation)).mpr
  refine ⟨full.realization.equivalent, ?_⟩
  intro valuation field
  exact bind_fieldValue target full.realization.implementation field
    ((full.profileEqual field).trans (current_available target field)) valuation

theorem bind_quotient (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (comparison : TerminalQuotientComparison (system target) ⟨keep⟩ target.implementation) :
    WireProfile.QuotientEquivalent keep target
      (bind target comparison.realization.implementation) := by
  apply (WireProfile.quotient_iff keep target
    (bind target comparison.realization.implementation)).mpr
  refine ⟨comparison.realization.equivalent, ?_⟩
  intro valuation field kept
  exact bind_fieldValue target comparison.realization.implementation field
    ((comparison.keptProfileEqual field kept).trans (current_available target field)) valuation

theorem full_minimum (target : WireCarrier inputs outputs fields) :
    terminalFullProfileMinimum (system target) target.implementation =
      WireProfile.fullMinimum target := by
  apply Nat.le_antisymm
  · have lower := terminalFullProfileMinimum_le
      (fullComparison target (WireProfile.fullWitness target)
        (WireProfile.fullWitness_matches target))
    change terminalFullProfileMinimum (system target) target.implementation ≤
      (WireProfile.fullWitness target).implementation.gateCount at lower
    rw [WireProfile.fullWitness_gateCount] at lower
    exact lower
  · have lower := WireProfile.full_candidate_lower_bound target
      (bind target
        (terminalFullProfileMinimumRealization (system target) target.implementation).realization.implementation)
      (bind_full target
        (terminalFullProfileMinimumRealization (system target) target.implementation))
    rw [bind_gateCount, terminalFullProfileMinimumRealization_gateCount] at lower
    exact lower

theorem quotient_minimum (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    terminalQuotientProfileMinimum (system target) ⟨keep⟩ target.implementation =
      WireProfile.quotientMinimum target keep := by
  apply Nat.le_antisymm
  · have lower := terminalQuotientProfileMinimum_le
      (quotientComparison target (WireProfile.quotientWitness target keep) keep
        (WireProfile.quotientWitness_matches target keep))
    change terminalQuotientProfileMinimum (system target) ⟨keep⟩ target.implementation ≤
      (WireProfile.quotientWitness target keep).implementation.gateCount at lower
    rw [WireProfile.quotientWitness_gateCount] at lower
    exact lower
  · have lower := WireProfile.quotient_candidate_lower_bound target
      (bind target
        (terminalQuotientProfileMinimumComparison
          (system target) ⟨keep⟩ target.implementation).realization.implementation)
      keep (bind_quotient target keep
        (terminalQuotientProfileMinimumComparison (system target) ⟨keep⟩ target.implementation))
    rw [bind_gateCount, terminalQuotientProfileMinimumComparison_gateCount] at lower
    exact lower

theorem full_match_iff (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) :
    terminalFullProfileMatchBool (system target) target.implementation offered = true ↔
      WireProfile.FullEquivalent target (bind target offered) := by
  constructor
  · intro accepted
    exact bind_full target (terminalFullProfileMatchBool_sound accepted)
  · intro same
    exact terminalFullProfileMatchBool_complete (fullComparison target (bind target offered) same)

theorem quotient_match_iff (target : WireCarrier inputs outputs fields)
    (offered : Implementation inputs outputs) (keep : Fin fields → Bool) :
    terminalQuotientProfileMatchBool (system target) ⟨keep⟩ target.implementation offered = true ↔
      WireProfile.QuotientEquivalent keep target (bind target offered) := by
  constructor
  · intro accepted
    exact bind_quotient target keep (terminalQuotientProfileMatchBool_sound accepted)
  · intro same
    exact terminalQuotientProfileMatchBool_complete
      (quotientComparison target (bind target offered) keep same)

theorem sourceMatches_congr (left right : WireCarrier inputs outputs fields)
    (same : ∀ valuation field, left.fieldValue valuation field = right.fieldValue valuation field)
    (offered : Implementation inputs outputs) (field : Fin fields)
    (source : Source inputs offered.gateCount) :
    sourceMatches left offered field source = sourceMatches right offered field source := by
  unfold sourceMatches
  apply congrArg (allTrue (allBoolTuples inputs))
  funext tuple
  rw [same tuple.toValuation field]

theorem findSource_congr (left right : WireCarrier inputs outputs fields)
    (same : ∀ valuation field, left.fieldValue valuation field = right.fieldValue valuation field)
    (offered : Implementation inputs outputs) (field : Fin fields) :
    findSource left offered field = findSource right offered field := by
  unfold findSource
  apply congrArg (fun predicate => (allSources inputs offered.gateCount).find? predicate)
  funext source
  exact sourceMatches_congr left right same offered field source

theorem system_congr (left right : WireCarrier inputs outputs fields)
    (same : ∀ valuation field, left.fieldValue valuation field = right.fieldValue valuation field) :
    system left = system right := by
  have observers : available left = available right := by
    funext offered field
    exact congrArg Option.isSome (findSource_congr left right same offered field)
  exact congrArg (fun observe =>
    ({ role := fun _ => .carrier, observe := observe } :
      TerminalProfileSystem inputs outputs fields)) observers

theorem system_fullEquivalent (left right : WireCarrier inputs outputs fields)
    (same : WireProfile.FullEquivalent left right) :
    system left = system right :=
  system_congr left right
    (fun valuation field => (((WireProfile.full_iff left right).mp same).2 valuation field).symm)





end PNP.DirectWire.WireProfileAvailability
