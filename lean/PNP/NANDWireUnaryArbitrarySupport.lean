/-
Copyright (c) 2026 PNP Labs.

Derive a minimum constant/unary full frontier word for any completed terminal
support and prove that its literal replacement cannot introduce a cycle,
including when the sole incoming port is an external original gate.

This computational R7 component is not complete Package E, unrestricted
minimization, unconditional ZeroSlack or polynomial-time PCCMin.
-/

import PNP.NANDWireUnaryFrontier

namespace PNP.DirectWire.WireUnaryArbitrarySupport

variable {inputs outputs fields width : Nat}

private theorem unpack_source (combined : Implementation inputs (outputs + fields))
    (output : Fin outputs) :
    (WireCarrier.unpack (outputs := outputs) (fields := fields) combined).implementation.candidate.directWireWord.source output =
      combined.candidate.directWireWord.source (Fin.castAdd fields output) := by
  unfold WireCarrier.unpack
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]

/-- The zero-input constructor uses a literal constant at every frontier port. -/
theorem constantWord_source (original : Implementation 0 width) (output : Fin width) :
    ∃ value, (WireUnaryFrontier.constantWord original).candidate.directWireWord.source
      output = .constant value := by
  refine ⟨original.candidate.semantics Fin.elim0 output, ?_⟩
  unfold WireUnaryFrontier.constantWord
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]

/-- An actually constant unary observation becomes a literal constant source.
    Semantic equality alone would not justify discarding a wiring dependency. -/
theorem unaryWord_source_of_constant (original : Implementation 1 width)
    (output : Fin width)
    (constant : ∀ left right : Valuation 1,
      original.candidate.semantics left output = original.candidate.semantics right output) :
    ∃ value, (WireUnaryFrontier.unaryWord original).candidate.directWireWord.source
      output = .constant value := by
  let carrier := WireUnaryFrontier.unaryCarrier original
  have equal : WireUnaryRealization.bit carrier false (Fin.castAdd 0 output) =
      WireUnaryRealization.bit carrier true (Fin.castAdd 0 output) := by
    unfold WireUnaryRealization.bit carrier WireUnaryFrontier.unaryCarrier
    rw [WireCarrier.exposed_unpack]
    exact constant (fun _ => false) (fun _ => true)
  let literal (word : Implementation 1 (width + 0)) : Prop :=
    ∃ value, word.candidate.directWireWord.source (Fin.castAdd 0 output) = .constant value
  have actual : literal (WireUnaryRealization.implementation carrier) := by
    unfold WireUnaryRealization.implementation
    split
    · change literal (WireUnaryRealization.oneImplementation carrier)
      unfold literal
      dsimp only [WireUnaryRealization.oneImplementation, Candidate.toImplementation]
      rw [Candidate.ofDirectWireWord_pointwise]
      dsimp only
      rw [equal]
      cases WireUnaryRealization.bit carrier true (Fin.castAdd 0 output)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    · change literal (WireUnaryRealization.zeroImplementation carrier)
      unfold literal
      dsimp only [WireUnaryRealization.zeroImplementation, Candidate.toImplementation]
      rw [Candidate.ofDirectWireWord_pointwise]
      dsimp only
      rw [equal]
      cases WireUnaryRealization.bit carrier true (Fin.castAdd 0 output)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  obtain ⟨value, literalAt⟩ := actual
  refine ⟨value, ?_⟩
  exact (unpack_source (WireUnaryRealization.implementation carrier) output).trans literalAt

/-- Constant open observations produce no dependency-bearing input or gate wire. -/
theorem localWord_source_of_constant (original : Implementation inputs width)
    (small : inputs ≤ 1) (output : Fin width)
    (constant : ∀ left right : Valuation inputs,
      original.candidate.semantics left output = original.candidate.semantics right output) :
    ∃ value, (WireUnaryFrontier.localWord original small).candidate.directWireWord.source
      output = .constant value := by
  cases inputs with
  | zero => exact constantWord_source original output
  | succ inputs =>
    cases inputs with
    | zero => exact unaryWord_source_of_constant original output constant
    | succ inputs => omega


private theorem shortList {alpha : Type} (items : List alpha) (small : items.length ≤ 1) :
    items = [] ∨ ∃ item, items = [item] := by
  cases items with
  | nil => exact Or.inl rfl
  | cons head tail =>
      right
      refine ⟨head, ?_⟩
      cases tail with
      | nil => rfl
      | cons next rest =>
          exact False.elim (Nat.not_succ_le_self 1 (Nat.le_trans
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))) small))

variable (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))

/-- Complete an arbitrary input support against all actual computational fields. -/
def pulled : TerminalExtractedSupport (profileWidth := 0) carrier.exposed.candidate :=
  extractTerminalSupport carrier.exposed.candidate records

/-- Count the actual exterior once, independently of local replacement size. -/
def exteriorCharge : Nat := (ArbitrarySupportSplice.exterior records).length

/-- The minimum zero/unary frontier word is derived from the original open function. -/
def replacement (small : (pulled carrier records).boundary.length ≤ 1) :
    Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length :=
  WireUnaryFrontier.localWord (pulled carrier records).extractedCandidate.toImplementation small

theorem replacement_agreement (small : (pulled carrier records).boundary.length ≤ 1) :
    (replacement carrier records small).candidate.semantics =
      (pulled carrier records).extractedCandidate.semantics := by
  funext valuation output
  exact WireUnaryFrontier.localWord_value _ small valuation output

theorem replacement_gate_bound (small : (pulled carrier records).boundary.length ≤ 1) :
    (replacement carrier records small).gateCount ≤ 1 :=
  WireUnaryFrontier.localWord_gate_bound _ small

theorem replacement_minimal (small : (pulled carrier records).boundary.length ≤ 1)
    (other : Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics =
      (pulled carrier records).extractedCandidate.semantics) :
    (replacement carrier records small).gateCount ≤ other.gateCount :=
  WireUnaryFrontier.localWord_minimal _ other small
    (fun valuation output => congrFun (congrFun sameOpen valuation) output)

theorem replacement_nonincrease (small : (pulled carrier records).boundary.length ≤ 1) :
    (replacement carrier records small).gateCount ≤ (pulled carrier records).gateCount :=
  WireUnaryFrontier.localWord_nonincrease _ small

/-- Prefix causality forces the literal constructor to omit every backwards edge. -/
theorem replacement_early_constant
    (small : (pulled carrier records).boundary.length ≤ 1)
    (boundaryGate : Fin carrier.implementation.gateCount)
    (single : terminalBoundaryPorts carrier.exposed.candidate.program records =
      [.gate boundaryGate])
    (port : Fin (pulled carrier records).interface.length)
    (before : ((pulled carrier records).interface.get port).val < boundaryGate.val) :
    ∃ value, (replacement carrier records small).candidate.directWireWord.source port =
      .constant value := by
  apply localWord_source_of_constant _ small port
  intro left right
  change (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics
      left port =
    (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics
      right port
  exact (extractTerminalSupport_semantics carrier.exposed.candidate records left port).trans
    ((terminalOpenGateEvaluation_single_gate_prefix carrier.exposed.candidate records
      boundaryGate single left right _ before).trans
        (extractTerminalSupport_semantics carrier.exposed.candidate records right port).symm)

/-- Every computed zero/unary replacement is acyclic, including an external gate input. -/
theorem graph_wellFounded (small : (pulled carrier records).boundary.length ≤ 1) :
    WellFounded (ArbitrarySupportSplice.graph carrier.exposed.candidate records
      (replacement carrier records small).candidate).Depends := by
  rcases shortList (terminalBoundaryPorts carrier.exposed.candidate.program records) small
    with empty | ⟨wire, single⟩
  · apply ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary
      carrier.exposed.candidate records (replacement carrier records small).candidate
    intro wire member
    rw [empty] at member
    cases member
  · cases wire with
    | input index =>
        apply ArbitrarySupportSplice.graph_wellFounded_of_primaryBoundary
          carrier.exposed.candidate records (replacement carrier records small).candidate
        intro wire member
        refine ⟨index, ?_⟩
        apply List.mem_singleton.mp
        rw [← single]
        exact member
    | gate boundaryGate =>
        exact ArbitrarySupportSplice.graph_wellFounded_of_singleGateBoundary
          carrier.exposed.candidate records (replacement carrier records small).candidate
          boundaryGate single (replacement_gate_bound carrier records small)
          (replacement_early_constant carrier records small boundaryGate single)

/-- The actual compiler succeeds from the boundary-size test alone.
    No order, agreement, acyclicity or successful compiler result is an input. -/
theorem compile_isSome (small : (pulled carrier records).boundary.length ≤ 1) :
    (ArbitrarySupportSplice.compile carrier.exposed.candidate records
      (replacement carrier records small).candidate).isSome = true := by
  obtain ⟨compiled, compiledAt⟩ := (ArbitrarySupportSplice.compile_success_iff
    carrier.exposed.candidate records (replacement carrier records small).candidate).2
      (graph_wellFounded carrier records small)
  rw [compiledAt]
  rfl

/-- Obtain the actual compiled program from the total recognized construction. -/
def compiled (small : (pulled carrier records).boundary.length ≤ 1) :
    CompiledRawNandGraph (ArbitrarySupportSplice.graph carrier.exposed.candidate records
      (replacement carrier records small).candidate) :=
  (ArbitrarySupportSplice.compile carrier.exposed.candidate records
    (replacement carrier records small).candidate).get (compile_isSome carrier records small)

/-- Reconnect the original exterior and recover every ordinary output and field. -/
def expanded (small : (pulled carrier records).boundary.length ≤ 1) :
    WireCarrier inputs outputs fields :=
  carrier.spliceResult records (replacement carrier records small).candidate
    (compiled carrier records small)


theorem original_charge :
    carrier.implementation.gateCount =
      (pulled carrier records).gateCount + exteriorCharge carrier records :=
  (ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate records).symm

theorem expanded_output (small : (pulled carrier records).boundary.length ≤ 1)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (expanded carrier records small).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  carrier.splice_output records _ (replacement_agreement carrier records small)
    (compiled carrier records small) valuation output

theorem expanded_field (small : (pulled carrier records).boundary.length ≤ 1)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier records small).fieldValue valuation field = carrier.fieldValue valuation field :=
  carrier.splice_field records _ (replacement_agreement carrier records small)
    (compiled carrier records small) valuation field

theorem expanded_equivalent (small : (pulled carrier records).boundary.length ≤ 1) :
    Equivalent (expanded carrier records small).implementation.candidate.program
      (expanded carrier records small).implementation.candidate.directWireWord
      carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord :=
  expanded_output carrier records small

/-- Exactly one copy of the original physical exterior is retained. -/
theorem expanded_charge (small : (pulled carrier records).boundary.length ≤ 1) :
    (expanded carrier records small).implementation.gateCount =
      (replacement carrier records small).gateCount + exteriorCharge carrier records := by
  have accounting := ArbitrarySupportSplice.result_gateCount carrier.exposed.candidate records
    (replacement carrier records small).candidate (compiled carrier records small)
  change (expanded carrier records small).implementation.gateCount =
    exteriorCharge carrier records + (replacement carrier records small).gateCount at accounting
  exact accounting.trans (Nat.add_comm _ _)

theorem expanded_nonincrease (small : (pulled carrier records).boundary.length ≤ 1) :
    (expanded carrier records small).implementation.gateCount ≤ carrier.implementation.gateCount := by
  rw [expanded_charge carrier records small, original_charge carrier records]
  exact Nat.add_le_add_right (replacement_nonincrease carrier records small) _

theorem expanded_gain_iff (small : (pulled carrier records).boundary.length ≤ 1) :
    (expanded carrier records small).implementation.gateCount < carrier.implementation.gateCount ↔
      (replacement carrier records small).gateCount < (pulled carrier records).gateCount := by
  rw [expanded_charge carrier records small, original_charge carrier records]
  constructor <;> intro inequality <;> omega

theorem proper_iff_exterior_positive :
    (pulled carrier records).gateCount < carrier.implementation.gateCount ↔
      0 < exteriorCharge carrier records := by
  rw [original_charge carrier records]
  constructor
  · intro smaller
    apply Nat.lt_of_add_lt_add_left
    simpa only [Nat.add_zero] using smaller
  · intro positive
    simpa only [Nat.add_zero] using
      Nat.add_lt_add_left positive (pulled carrier records).gateCount

/-- Recognize the actual completed boundary, not a supplied successful compiler result. -/
def attempt : Option (WireCarrier inputs outputs fields) :=
  if small : (pulled carrier records).boundary.length ≤ 1 then
    some (expanded carrier records small)
  else none

theorem attempt_isSome_iff :
    (attempt carrier records).isSome = true ↔ (pulled carrier records).boundary.length ≤ 1 := by
  unfold attempt
  split
  next small => exact ⟨fun _accepted => small, fun _small => rfl⟩
  next notSmall =>
    constructor
    · intro impossible
      cases impossible
    · intro small
      exact (notSmall small).elim

private theorem attempt_result (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier records = some result) :
    ∃ small, result = expanded carrier records small := by
  unfold attempt at accepted
  split at accepted
  next small => exact ⟨small, (Option.some.inj accepted).symm⟩
  next notSmall => cases accepted

theorem attempt_output (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier records = some result)
    (valuation : Valuation inputs) (output : Fin outputs) :
    result.implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output := by
  obtain ⟨small, rfl⟩ := attempt_result carrier records result accepted
  exact expanded_output carrier records small valuation output

theorem attempt_field (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier records = some result)
    (valuation : Valuation inputs) (field : Fin fields) :
    result.fieldValue valuation field = carrier.fieldValue valuation field := by
  obtain ⟨small, rfl⟩ := attempt_result carrier records result accepted
  exact expanded_field carrier records small valuation field

theorem attempt_nonincrease (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier records = some result) :
    result.implementation.gateCount ≤ carrier.implementation.gateCount := by
  obtain ⟨small, rfl⟩ := attempt_result carrier records result accepted
  exact expanded_nonincrease carrier records small

theorem attempt_charge (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier records = some result) :
    ∃ small, result.implementation.gateCount =
      (replacement carrier records small).gateCount + exteriorCharge carrier records := by
  obtain ⟨small, rfl⟩ := attempt_result carrier records result accepted
  exact ⟨small, expanded_charge carrier records small⟩

/-- A lost R5 identity is tied to the actual expanded source and its full value. -/
structure ExpandedDischarge (small : (pulled carrier records).boundary.length ≤ 1)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) where
  actualSource : Source inputs (expanded carrier records small).implementation.gateCount
  sourceExact : actualSource = (expanded carrier records small).source creation.coordinate
  fullWitness : ∀ valuation,
    actualSource.eval valuation
        ((expanded carrier records small).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

/-- No padding or caller-supplied full-agreement certificate discharges this R7 witness. -/
def dischargeR7 (small : (pulled carrier records).boundary.length ≤ 1)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    ExpandedDischarge carrier records small keep creation :=
  { actualSource := (expanded carrier records small).source creation.coordinate
    sourceExact := rfl
    fullWitness := by
      intro valuation
      rw [creation.sourceExact]
      exact expanded_field carrier records small valuation creation.coordinate }

theorem dischargeR7_source_exact (small : (pulled carrier records).boundary.length ≤ 1)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (dischargeR7 carrier records small keep creation).actualSource =
      (expanded carrier records small).source creation.coordinate := rfl

theorem dischargeR7_full_value (small : (pulled carrier records).boundary.length ≤ 1)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (dischargeR7 carrier records small keep creation).actualSource.eval valuation
        ((expanded carrier records small).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  expanded_field carrier records small valuation creation.coordinate

/-- Physical properness and strict local saving are independently checked. -/
structure ProperGain : Type where
  small : (pulled carrier records).boundary.length ≤ 1
  proper : 0 < exteriorCharge carrier records
  smaller : (replacement carrier records small).gateCount < (pulled carrier records).gateCount

def checkedProperGain : Option (ProperGain carrier records) :=
  if small : (pulled carrier records).boundary.length ≤ 1 then
    if proper : 0 < exteriorCharge carrier records then
      if smaller : (replacement carrier records small).gateCount <
          (pulled carrier records).gateCount then
        some ⟨small, proper, smaller⟩
      else none
    else none
  else none

theorem checkedProperGain_isSome_iff :
    (checkedProperGain carrier records).isSome = true ↔
      ∃ small, 0 < exteriorCharge carrier records ∧
        (replacement carrier records small).gateCount < (pulled carrier records).gateCount := by
  unfold checkedProperGain
  split
  next small =>
    split
    next proper =>
      split
      next smaller => exact ⟨fun _accepted => ⟨small, proper, smaller⟩, fun _valid => rfl⟩
      next notSmaller =>
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_small, _proper, smaller⟩
          exact (notSmaller smaller).elim
    next notProper =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨_small, proper, _smaller⟩
        exact (notProper proper).elim
  next notSmall =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨small, _proper, _smaller⟩
      exact (notSmall small).elim

/-- Any smaller complete local word implies acceptance on a proper recognized support.
    No global minimum over alternative exterior implementations is claimed. -/
theorem checkedProperGain_complete
    (small : (pulled carrier records).boundary.length ≤ 1)
    (proper : 0 < exteriorCharge carrier records)
    (other : Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics)
    (smaller : other.gateCount < (pulled carrier records).gateCount) :
    (checkedProperGain carrier records).isSome = true :=
  (checkedProperGain_isSome_iff carrier records).2
    ⟨small, proper,
      Nat.lt_of_le_of_lt (replacement_minimal carrier records small other sameOpen) smaller⟩

def ProperGain.strictGain {carrier : WireCarrier inputs outputs fields}
    {records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)}
    (gain : ProperGain carrier records) :
    StrictEquivalentGain carrier.implementation
      (expanded carrier records gain.small).implementation where
  smaller := (expanded_gain_iff carrier records gain.small).2 gain.smaller
  equivalent := expanded_equivalent carrier records gain.small

theorem ProperGain.checked {carrier : WireCarrier inputs outputs fields}
    {records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)}
    (gain : ProperGain carrier records) :
    (pulled carrier records).gateCount < carrier.implementation.gateCount ∧
      StrictEquivalentGain carrier.implementation (expanded carrier records gain.small).implementation ∧
      (∀ valuation field, (expanded carrier records gain.small).fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      (expanded carrier records gain.small).implementation.gateCount =
        (replacement carrier records gain.small).gateCount + exteriorCharge carrier records :=
  ⟨(proper_iff_exterior_positive carrier records).2 gain.proper,
    gain.strictGain, expanded_field carrier records gain.small,
    expanded_charge carrier records gain.small⟩

end PNP.DirectWire.WireUnaryArbitrarySupport
