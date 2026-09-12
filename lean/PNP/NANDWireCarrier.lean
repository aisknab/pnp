/-
Copyright (c) 2026 PNP Labs.

Literal wire-backed computational carrier fields. Every field is an actual
input, constant or gate source, not a supplied observer or a proof-only record.
Expose all such sources during physical normalization and arbitrary-support
replacement, then recover the ordinary outputs and rebound field wires.

This value-transport component does not derive the full manuscript carrier,
record histories, obligation creation/discharge, global routes or polynomial
bounds. It does not turn logical records into free Boolean sources.
-/

import PNP.PCCMinPhysicalNormalizationClosure
import PNP.NANDArbitrarySupportSplice

namespace PNP.DirectWire

/-- An actual implementation with ordered, literal computational field wires. -/
structure WireCarrier (inputs outputs fields : Nat) where
  implementation : Implementation inputs outputs
  source : Fin fields → Source inputs implementation.gateCount

namespace WireCarrier

variable {inputs outputs fields : Nat}

/-- Evaluate an actual source in the actual implementation. -/
def fieldValue (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (field : Fin fields) : Bool :=
  (carrier.source field).eval valuation
    (carrier.implementation.candidate.program.eval valuation)

/-- Ordinary outputs followed by every field wire; no gates are appended. -/
def exposed (carrier : WireCarrier inputs outputs fields) :
    Implementation inputs (outputs + fields) :=
  (Candidate.ofDirectWireWord carrier.implementation.candidate.program
    ⟨splitFin carrier.implementation.candidate.directWireWord.source
      carrier.source⟩).toImplementation

/-- Recover the ordinary outputs and field wires from a transformed full word. -/
def unpack (combined : Implementation inputs (outputs + fields)) :
    WireCarrier inputs outputs fields :=
  { implementation :=
      (Candidate.ofDirectWireWord combined.candidate.program
        ⟨fun output => combined.candidate.directWireWord.source
          (Fin.castAdd fields output)⟩).toImplementation
    source := fun field => combined.candidate.directWireWord.source
      (Fin.natAdd outputs field) }

theorem exposed_gateCount (carrier : WireCarrier inputs outputs fields) :
    carrier.exposed.gateCount = carrier.implementation.gateCount := rfl

theorem unpack_gateCount (combined : Implementation inputs (outputs + fields)) :
    (unpack (outputs := outputs) (fields := fields) combined).implementation.gateCount =
      combined.gateCount := rfl

theorem exposed_output_source (carrier : WireCarrier inputs outputs fields)
    (output : Fin outputs) :
    carrier.exposed.candidate.directWireWord.source (Fin.castAdd fields output) =
      carrier.implementation.candidate.directWireWord.source output := by
  unfold exposed
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  exact splitFin_left _ _ output

theorem exposed_field_source (carrier : WireCarrier inputs outputs fields)
    (field : Fin fields) :
    carrier.exposed.candidate.directWireWord.source (Fin.natAdd outputs field) =
      carrier.source field := by
  unfold exposed
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_pointwise]
  exact splitFin_right _ _ field

theorem exposed_output (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    carrier.exposed.candidate.semantics valuation (Fin.castAdd fields output) =
      carrier.implementation.candidate.semantics valuation output := by
  change (carrier.exposed.candidate.directWireWord.source
      (Fin.castAdd fields output)).eval valuation
      (carrier.implementation.candidate.program.eval valuation) = _
  rw [exposed_output_source]
  rfl

theorem exposed_field (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (field : Fin fields) :
    carrier.exposed.candidate.semantics valuation (Fin.natAdd outputs field) =
      carrier.fieldValue valuation field := by
  change (carrier.exposed.candidate.directWireWord.source
      (Fin.natAdd outputs field)).eval valuation
      (carrier.implementation.candidate.program.eval valuation) = _
  rw [exposed_field_source]
  rfl

theorem unpack_output (combined : Implementation inputs (outputs + fields))
    (valuation : Valuation inputs) (output : Fin outputs) :
    (unpack (outputs := outputs) (fields := fields) combined).implementation.candidate.semantics
        valuation output =
      combined.candidate.semantics valuation (Fin.castAdd fields output) := by
  unfold unpack Candidate.toImplementation
  change ((Candidate.ofDirectWireWord combined.candidate.program
      ⟨fun index => combined.candidate.directWireWord.source
        (Fin.castAdd fields index)⟩).directWireWord.source output).eval
      valuation (combined.candidate.program.eval valuation) = _
  rw [Candidate.ofDirectWireWord_pointwise]
  rfl

theorem unpack_field (combined : Implementation inputs (outputs + fields))
    (valuation : Valuation inputs) (field : Fin fields) :
    (unpack (outputs := outputs) (fields := fields) combined).fieldValue valuation field =
      combined.candidate.semantics valuation (Fin.natAdd outputs field) := rfl

private theorem word_ofFn_get {gates width : Nat}
    (word : OutputWord inputs gates width) :
    OutputWord.ofFn word.get = word := by
  induction word with
  | nil => rfl
  | cons head tail ih =>
      change OutputWord.cons head (OutputWord.ofFn tail.get) = _
      rw [ih]

private theorem word_ext {gates width : Nat}
    (left right : OutputWord inputs gates width)
    (same : ∀ index, left.get index = right.get index) : left = right :=
  (word_ofFn_get left).symm.trans
    ((congrArg OutputWord.ofFn (funext same)).trans (word_ofFn_get right))

private theorem split_rejoin {left right : Nat} {alpha : Type}
    (source : Fin (left + right) → alpha) (index : Fin (left + right)) :
    splitFin (fun output => source (Fin.castAdd right output))
      (fun field => source (Fin.natAdd left field)) index = source index := by
  rcases finSum_decompose index with ⟨output, rfl⟩ | ⟨field, rfl⟩
  · exact splitFin_left _ _ output
  · exact splitFin_right _ _ field

/-- Repacking retains the exact program and every ordered source, not only size. -/
theorem exposed_unpack (combined : Implementation inputs (outputs + fields)) :
    (unpack (outputs := outputs) (fields := fields) combined).exposed = combined := by
  cases combined with
  | mk gates candidate =>
    cases candidate with
    | mk program word =>
      apply congrArg (Implementation.mk gates)
      apply congrArg (Candidate.mk program)
      apply word_ext
      intro index
      change (OutputWord.ofFn (splitFin
        (OutputWord.ofFn (fun output => word.get (Fin.castAdd fields output))).get
        (fun field => word.get (Fin.natAdd outputs field)))).get index = word.get index
      rw [OutputWord.get_ofFn]
      have leftEq : (OutputWord.ofFn
          (fun output => word.get (Fin.castAdd fields output))).get =
          (fun output => word.get (Fin.castAdd fields output)) :=
        funext (OutputWord.get_ofFn _)
      rw [leftEq]
      exact split_rejoin word.get index

/-- Splitting a carrier's complete word recovers the exact carrier. -/
theorem unpack_exposed (carrier : WireCarrier inputs outputs fields) :
    unpack carrier.exposed = carrier := by
  cases carrier with
  | mk implementation source =>
    cases implementation with
    | mk gates candidate =>
      cases candidate with
      | mk program word =>
        have originalWord :
            OutputWord.ofFn (fun output : Fin outputs =>
              (OutputWord.ofFn (splitFin word.get source)).get
                (Fin.castAdd fields output)) = word := by
          apply word_ext
          intro output
          rw [OutputWord.get_ofFn, OutputWord.get_ofFn, splitFin_left]
        have originalFields :
            (fun field : Fin fields =>
              (OutputWord.ofFn (splitFin word.get source)).get
                (Fin.natAdd outputs field)) = source := by
          funext field
          rw [OutputWord.get_ofFn, splitFin_right]
        change WireCarrier.mk
          (Implementation.mk gates (Candidate.mk program
            (OutputWord.ofFn (fun output : Fin outputs =>
              (OutputWord.ofFn (splitFin word.get source)).get
                (Fin.castAdd fields output)))))
          (fun field : Fin fields =>
            (OutputWord.ofFn (splitFin word.get source)).get
              (Fin.natAdd outputs field)) = _
        rw [originalWord, originalFields]

/-- Run the actual three-pass physical closure with every field visible. -/
def normalize (carrier : WireCarrier inputs outputs fields) :
    WireCarrier inputs outputs fields :=
  unpack (runPhysicalNormalization carrier.exposed).result

theorem normalize_output (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    carrier.normalize.implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  (unpack_output _ valuation output).trans
    (((runPhysicalNormalization_checked carrier.exposed).1 valuation
      (Fin.castAdd fields output)).trans (carrier.exposed_output valuation output))

theorem normalize_field (carrier : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (field : Fin fields) :
    carrier.normalize.fieldValue valuation field = carrier.fieldValue valuation field :=
  (unpack_field _ valuation field).trans
    (((runPhysicalNormalization_checked carrier.exposed).1 valuation
      (Fin.natAdd outputs field)).trans (carrier.exposed_field valuation field))

theorem normalize_exact_accounting (carrier : WireCarrier inputs outputs fields) :
    carrier.normalize.implementation.gateCount +
      (runPhysicalNormalization carrier.exposed).trace.savedGates =
        carrier.implementation.gateCount :=
  (runPhysicalNormalization_checked carrier.exposed).2.2.1

theorem normalize_quiescent (carrier : WireCarrier inputs outputs fields) :
    PhysicalNormalizationQuiescent carrier.normalize.exposed := by
  unfold normalize
  rw [exposed_unpack]
  exact (runPhysicalNormalization_checked carrier.exposed).2.1

theorem normalize_idempotent (carrier : WireCarrier inputs outputs fields) :
    carrier.normalize.normalize = carrier.normalize := by
  unfold normalize
  rw [exposed_unpack, runPhysicalNormalization_idempotent]

/-- Selected field producers are physical interface ports even when ordinary
outputs never refer to them. -/
theorem field_producer_visible (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (field : Fin fields) (producer : Fin carrier.implementation.gateCount)
    (sourceAt : carrier.source field = .gate producer)
    (selected : terminalGateSelected records producer = true) :
    producer ∈ (extractTerminalSupport carrier.exposed.candidate records).interface := by
  apply (mem_terminalInterfacePorts_iff carrier.exposed.candidate records producer).2
  apply (terminalInterfaceGate_eq_true_iff carrier.exposed.candidate records producer).2
  refine ⟨selected, Or.inr ?_⟩
  apply (terminalGateIsGlobalOutput_eq_true_iff
    carrier.exposed.candidate.directWireWord producer).2
  exact ⟨Fin.natAdd outputs field, (carrier.exposed_field_source field).trans sourceAt⟩

variable (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    {replacementGates : Nat}
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate records).boundary.length
      replacementGates
      (extractTerminalSupport carrier.exposed.candidate records).interface.length)

/-- Recover the carrier from the literal compiler's complete rebound word. -/
def spliceResult
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) :
    WireCarrier inputs outputs fields :=
  unpack (ArbitrarySupportSplice.result carrier.exposed.candidate records
    replacement compiled).toImplementation

/-- Run the actual compiler; no map, order or successful result is supplied. -/
def splice : Option (WireCarrier inputs outputs fields) :=
  (ArbitrarySupportSplice.compile carrier.exposed.candidate records replacement).map
    (carrier.spliceResult records replacement)

theorem splice_output
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement))
    (valuation : Valuation inputs) (output : Fin outputs) :
    (carrier.spliceResult records replacement compiled).implementation.candidate.semantics
        valuation output = carrier.implementation.candidate.semantics valuation output :=
  (unpack_output _ valuation output).trans
    ((ArbitrarySupportSplice.result_semantics carrier.exposed.candidate records replacement
      sameOpen compiled valuation (Fin.castAdd fields output)).trans
        (carrier.exposed_output valuation output))

theorem splice_field
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement))
    (valuation : Valuation inputs) (field : Fin fields) :
    (carrier.spliceResult records replacement compiled).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  (unpack_field _ valuation field).trans
    ((ArbitrarySupportSplice.result_semantics carrier.exposed.candidate records replacement
      sameOpen compiled valuation (Fin.natAdd outputs field)).trans
        (carrier.exposed_field valuation field))

theorem splice_exact_accounting
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) :
    (carrier.spliceResult records replacement compiled).implementation.gateCount +
      (extractTerminalSupport carrier.exposed.candidate records).gateCount =
        carrier.implementation.gateCount + replacementGates :=
  ArbitrarySupportSplice.result_exact_accounting
    carrier.exposed.candidate records replacement compiled

theorem splice_strict_gain
    (smaller : replacementGates <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph carrier.exposed.candidate records replacement)) :
    (carrier.spliceResult records replacement compiled).implementation.gateCount <
      carrier.implementation.gateCount :=
  ArbitrarySupportSplice.result_strict_gain
    carrier.exposed.candidate records replacement smaller compiled

/-- A successful execution preserves both observation classes and exact size. -/
theorem splice_checked
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)
    (result : WireCarrier inputs outputs fields)
    (accepted : carrier.splice records replacement = some result) :
    (∀ valuation output, result.implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output) ∧
    (∀ valuation field, result.fieldValue valuation field =
      carrier.fieldValue valuation field) ∧
    result.implementation.gateCount +
      (extractTerminalSupport carrier.exposed.candidate records).gateCount =
        carrier.implementation.gateCount + replacementGates := by
  unfold splice at accepted
  cases compiledAt : ArbitrarySupportSplice.compile
      carrier.exposed.candidate records replacement with
  | none =>
      rw [compiledAt] at accepted
      cases accepted
  | some compiled =>
      rw [compiledAt] at accepted
      cases accepted
      exact ⟨carrier.splice_output records replacement sameOpen compiled,
        carrier.splice_field records replacement sameOpen compiled,
        carrier.splice_exact_accounting records replacement compiled⟩

/-- Literal cycles still fail; carrier exposure does not supply an order proof. -/
theorem splice_failure_iff :
    carrier.splice records replacement = none ↔
      ¬WellFounded (ArbitrarySupportSplice.graph
        carrier.exposed.candidate records replacement).Depends := by
  have rawFailure := ArbitrarySupportSplice.compile_failure_iff
    carrier.exposed.candidate records replacement
  constructor
  · intro failure
    apply rawFailure.1
    cases compiledAt : ArbitrarySupportSplice.compile
        carrier.exposed.candidate records replacement with
    | none => rfl
    | some compiled =>
        unfold splice at failure
        rw [compiledAt] at failure
        cases failure
  · intro cyclic
    unfold splice
    rw [rawFailure.2 cyclic]
    rfl

/-- These computational fields are already in the physical output word.
There are no additional abstract profile coordinates at this specialization;
this does not assert that the full manuscript profile is empty. -/
def productionModel :
    TerminalCandidateSaturationModel (profileWidth := 0) carrier.exposed.candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

/-- Derive physical predecessor closure from the actual combined program. -/
def productionRecords
    (seed : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)) :
    List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0) :=
  terminalSaturateRecords
    (terminalCandidateSaturationSystem carrier.exposed.candidate carrier.productionModel) seed

/-- Production saturation makes every incoming support wire a primary input. -/
theorem production_boundary_isInput
    (seed : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (wire : TerminalSupportWire inputs carrier.implementation.gateCount)
    (member : wire ∈ (extractTerminalSupport carrier.exposed.candidate
      (carrier.productionRecords seed)).boundary) :
    ∃ index : Fin inputs, wire = TerminalSupportWire.input index :=
  terminalCandidateSaturate_boundary_isInput
    carrier.exposed.candidate carrier.productionModel seed wire member

/-- The actual production splice runs successfully without a supplied observer,
wire map, acyclicity proof or compiled result. -/
theorem production_compiles
    (seed : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate
        (carrier.productionRecords seed)).boundary.length replacementGates
      (extractTerminalSupport carrier.exposed.candidate
        (carrier.productionRecords seed)).interface.length) :
    ∃ result, carrier.splice (carrier.productionRecords seed) replacement = some result := by
  obtain ⟨compiled, compiledAt⟩ := ArbitrarySupportSplice.production_compiles
    carrier.exposed.candidate carrier.productionModel seed replacement
  refine ⟨carrier.spliceResult (carrier.productionRecords seed) replacement compiled, ?_⟩
  exact congrArg (Option.map (carrier.spliceResult
    (carrier.productionRecords seed) replacement)) compiledAt

end WireCarrier
end PNP.DirectWire
