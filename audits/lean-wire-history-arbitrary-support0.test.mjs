import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import {REQUIRED_MILESTONE_THEOREMS0} from '../formal-publication0.mjs';

const SPECS = [
  {
    "path": "lean/PNP/NANDCausalBounds.lean",
    "heads": [
      "index_cases",
      "source",
      "levels",
      "levels_snoc_castSucc",
      "levels_snoc_last",
      "source_mono",
      "levels_mono",
      "source_noninterference",
      "program_noninterference",
      "source_sound",
      "source_congr",
      "source_rename_inputs",
      "levels_rename_inputs",
      "source_weaken",
      "source_shift",
      "source_substitute",
      "levels_append_prefix",
      "levels_append_suffix",
      "substituted_source_level",
      "Bounds",
      "bounds_levels",
      "bounds_index",
      "levels_le_of_bounds",
      "outputLevel",
      "outputLevel_renameInputs"
    ],
    "imports": [
      "PNP.NANDComposition"
    ],
    "context": [
      "namespace PNP.DirectWire.CausalBound",
      "end PNP.DirectWire.CausalBound"
    ],
    "signatures": {},
    "guards": []
  },
  {
    "path": "lean/PNP/ResidualTerminalSupportExtraction.lean",
    "heads": [
      "terminalSelectedGateIndices",
      "terminalSelectedGates",
      "mem_terminalSelectedGateIndices_iff",
      "mem_terminalSelectedGates_iff",
      "terminalSelectedGateIndices_nodup",
      "terminalSelectedGates_nodup",
      "TerminalExtractedSupport",
      "extractTerminalSupport",
      "extractTerminalSupport_records",
      "extractTerminalSupport_boundary",
      "extractTerminalSupport_selectedGates",
      "extractTerminalSupport_interface",
      "extractTerminalSupport_gateCount",
      "terminalExtractionGateIndex",
      "terminalExtractionOrigin",
      "terminalExtractionOrigin_selected",
      "terminalExtractionGateIndex_origin",
      "terminalExtractionOrigin_gateIndex",
      "terminalExtractionOrigin_injective",
      "terminalOpenGateEvaluation",
      "terminalOpenSupportSemantics",
      "TerminalSupportWire.candidateValue",
      "TerminalSupportWire.causalLevel",
      "terminalBoundaryCausalLabels",
      "terminalExtractedInterfaceCausalLevel",
      "extractTerminalSupport_causal_levels",
      "extractTerminalSupport_causal_index",
      "terminalInducedBoundaryValuation",
      "terminalOpenGateEvaluation_induced_selected",
      "terminalOpenSupportSemantics_induced",
      "extractTerminalSupport_semantics",
      "extractTerminalSupport_induced",
      "extractSaturatedTerminalSupport",
      "extractSaturatedTerminalSupport_records",
      "extractSaturatedTerminalSupport_gateCount",
      "extractSaturatedTerminalSupport_semantics",
      "extractSaturatedTerminalSupport_induced",
      "extractTerminalSupport_eq_of_gateSelected_eq",
      "terminalOpenGateEvaluation_prefix_congr",
      "terminalOpenGateEvaluation_single_gate_prefix",
      "terminalOpenWireValue",
      "terminalBoundaryPullback",
      "terminalOpenGateEvaluation_pullback",
      "terminalOpenSupportSemantics_pullback",
      "terminalBoundaryPullback_identity",
      "terminalBoundaryPullback_compose",
      "terminalOpenSourceValue",
      "terminalOpenGateEvaluation_sourceEquation",
      "terminalOpenWireValue_boundary_get",
      "terminalOpenWireValue_external_absent"
    ],
    "imports": [
      "PNP.ResidualTerminalPhysicalSupportCompletion",
      "PNP.NANDCausalBounds"
    ],
    "context": [
      "namespace PNP",
      "namespace DirectWire universe u",
      "end DirectWire",
      "end PNP"
    ],
    "signatures": {
      "extractTerminalSupport_causal_levels": "theorem extractTerminalSupport_causal_levels {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (labels : Fin inputs → Nat) (output : Fin (terminalInterfacePorts candidate records).length) : terminalExtractedInterfaceCausalLevel candidate records labels (CausalBound.levels candidate.program labels) output ≤ CausalBound.levels candidate.program labels ((terminalInterfacePorts candidate records).get output)",
      "extractTerminalSupport_causal_index": "theorem extractTerminalSupport_causal_index {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) (output : Fin (terminalInterfacePorts candidate records).length) : terminalExtractedInterfaceCausalLevel candidate records (fun _ => 0) (fun index => index.val + 1) output ≤ ((terminalInterfacePorts candidate records).get output).val + 1"
    },
    "guards": [
      [
        "causalBound := by",
        "constructed-extraction-bound"
      ]
    ]
  },
  {
    "path": "lean/PNP/PCCMinOutputConePruning.lean",
    "heads": [
      "outputConeSystem",
      "outputConeSeed",
      "outputConeRecords",
      "outputConeRecords_output",
      "outputConeRecords_closed",
      "outputConeRecords_least",
      "outputConeRecords_noExternalGate",
      "outputConeFrontierCandidate",
      "outputConeFrontierCandidate_semantics",
      "outputConeImplementation",
      "outputConeImplementation_equivalent",
      "outputConeImplementation_gateCount_le",
      "outputConeDeletedGateCount",
      "outputConeImplementation_exact_accounting",
      "outputConeImplementation_referenceMinimum",
      "outputConeImplementation_residualSlack",
      "outputConeImplementation_strictGain_iff",
      "outputConeNormalizer",
      "outputConeNormalizer_checked",
      "outputConeFrontierCandidate_causal_bound",
      "outputConeImplementation_causal_bound"
    ],
    "imports": [
      "PNP.PCCMinNormalizeOracleComposition",
      "PNP.ResidualTerminalSupportExtraction"
    ],
    "context": [
      "namespace PNP",
      "namespace DirectWire",
      "end DirectWire",
      "end PNP"
    ],
    "signatures": {},
    "guards": [
      [
        "extractTerminalSupport_causal_levels",
        "actual-extraction-pruning-bound"
      ]
    ]
  },
  {
    "path": "lean/PNP/NANDNormalizationCausalBounds.lean",
    "heads": [
      "source_weaken_snoc",
      "propagationRename_source_bound",
      "propagation_alias_bound",
      "constant_propagation_output_bound",
      "terminal_sources_level",
      "sharing_find_sources",
      "sharing_find_level",
      "sharingRename_source_bound",
      "sharing_alias_bound",
      "sharing_output_bound",
      "physical_pass_output_bound",
      "physical_trace_output_bound",
      "physical_normalization_output_bound"
    ],
    "imports": [
      "PNP.NANDCausalBounds",
      "PNP.PCCMinPhysicalNormalizationClosure"
    ],
    "context": [
      "namespace PNP.DirectWire.CausalBound",
      "end PNP.DirectWire.CausalBound"
    ],
    "signatures": {
      "physical_normalization_output_bound": "theorem physical_normalization_output_bound {inputs outputs : Nat} (current : Implementation inputs outputs) (labels : Fin inputs → Nat) (output : Fin outputs) : outputLevel (runPhysicalNormalization current).result.candidate labels output ≤ outputLevel current.candidate labels output"
    },
    "guards": [
      [
        "outputConeImplementation_causal_bound",
        "actual-pruning-bound"
      ],
      [
        "physical_trace_output_bound",
        "actual-normalization-trace"
      ]
    ]
  },
  {
    "path": "lean/PNP/NANDWireCausalBounds.lean",
    "heads": [
      "fieldLevel",
      "CausalBounds",
      "exposed_output_level",
      "exposed_field_level",
      "exposed_level",
      "causalBounds_exposed_le",
      "causalBounds_self",
      "normalize_exposed_level",
      "normalize_output_level",
      "normalize_field_level",
      "normalize_causalBounds",
      "masked_causalBounds",
      "hidden_causalBounds",
      "materializer_causalBounds",
      "join_output_level",
      "join_field_level",
      "join_causalBounds"
    ],
    "imports": [
      "PNP.NANDNormalizationCausalBounds",
      "PNP.NANDWireObligationRestoration"
    ],
    "context": [
      "namespace PNP.DirectWire",
      "namespace WireCarrier",
      "variable {inputs outputs fields : Nat}",
      "end WireCarrier",
      "namespace WireObligationRestoration",
      "variable {inputs outputs fields : Nat}",
      "end WireObligationRestoration",
      "end PNP.DirectWire"
    ],
    "signatures": {
      "normalize_causalBounds": "theorem normalize_causalBounds (carrier : WireCarrier inputs outputs fields) (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat) (fieldCaps : Fin fields → Nat) (bounded : carrier.CausalBounds labels outputCaps fieldCaps) : carrier.normalize.CausalBounds labels outputCaps fieldCaps",
      "join_causalBounds": "theorem join_causalBounds (visible : WireCarrier inputs outputs fields) (missing : WireCarrier inputs 0 fields) (keep : Fin fields → Bool) (labels : Fin inputs → Nat) (outputCaps : Fin outputs → Nat) (fieldCaps : Fin fields → Nat) (visibleBound : visible.CausalBounds labels outputCaps fieldCaps) (missingBound : missing.CausalBounds labels Fin.elim0 fieldCaps) : (join visible missing keep).CausalBounds labels outputCaps fieldCaps"
    },
    "guards": [
      [
        "missing.implementation.candidate.program",
        "actual-joined-materializer"
      ]
    ]
  },
  {
    "path": "lean/PNP/NANDWireHistoryCausalBounds.lean",
    "heads": [
      "SourceCausalBounds",
      "PendingCausalBounds",
      "State.CausalInvariant",
      "initial_causalInvariant",
      "create_causalInvariant",
      "normalize_causalInvariant",
      "restore_causalInvariant",
      "restoreR7_causalInvariant",
      "cancel_causalInvariant",
      "Transition.causalInvariant",
      "Execution.causalInvariant",
      "causalInvariant",
      "output_causal_bound",
      "field_causal_bound",
      "compileHistory_causal_bounds"
    ],
    "imports": [
      "PNP.NANDWireCausalBounds",
      "PNP.NANDWireObligationHistoryExecution"
    ],
    "context": [
      "namespace PNP.DirectWire.WireObligationHistory open WireObligationRestoration",
      "variable {inputs outputs fields : Nat}",
      "namespace State",
      "variable {source : WireCarrier inputs outputs fields}",
      "end State",
      "namespace ClosedHistory",
      "variable {source : WireCarrier inputs outputs fields} {raw : List (RawEvent fields)}",
      "end ClosedHistory",
      "end PNP.DirectWire.WireObligationHistory"
    ],
    "signatures": {
      "restoreR7_causalInvariant": "theorem restoreR7_causalInvariant (state : State source) (field : Fin fields) (snapshot : Snapshot source field) (found : state.pending field = some snapshot) (raw : List RawSupportRecord) (realization : R7Realization snapshot.carrier raw) (labels : Fin inputs → Nat) (bounded : state.CausalInvariant labels) : (state.restoreR7 field snapshot found raw realization).CausalInvariant labels",
      "Transition.causalInvariant": "theorem Transition.causalInvariant {source : WireCarrier inputs outputs fields} {before after : State source} {event : RawEvent fields} (step : Transition source before event after) (labels : Fin inputs → Nat) : before.CausalInvariant labels → after.CausalInvariant labels",
      "Execution.causalInvariant": "theorem Execution.causalInvariant {source : WireCarrier inputs outputs fields} {before after : State source} {events : List (RawEvent fields)} (trace : Execution source before events after) (labels : Fin inputs → Nat) : before.CausalInvariant labels → after.CausalInvariant labels",
      "causalInvariant": "theorem causalInvariant (history : ClosedHistory source raw) (labels : Fin inputs → Nat) : history.state.CausalInvariant labels",
      "field_causal_bound": "theorem field_causal_bound (history : ClosedHistory source raw) (labels : Fin inputs → Nat) (field : Fin fields) : history.state.current.fieldLevel labels field ≤ source.fieldLevel labels field",
      "compileHistory_causal_bounds": "theorem compileHistory_causal_bounds (source : WireCarrier inputs outputs fields) (raw : List (RawEvent fields)) (labels : Fin inputs → Nat) : match compileHistory source raw with | none => True | some history => SourceCausalBounds source history.state.current labels"
    },
    "guards": [
      [
        "bounded.2 field snapshot found",
        "actual-pending-snapshot-bound"
      ],
      [
        "rw [alias.sourceExact]",
        "literal-r6-source-identity"
      ],
      [
        "history.execution.causalInvariant labels (State.initial_causalInvariant source labels)",
        "source-initialized-history-invariant"
      ]
    ]
  },
  {
    "path": "lean/PNP/NANDArbitrarySupportSplice.lean",
    "heads": [
      "sources_eval",
      "sources_ordered",
      "exterior",
      "mem_exterior_iff",
      "boundarySource",
      "replacementSource",
      "Visible",
      "originalSource",
      "exteriorSource_visible",
      "output_visible",
      "exteriorGate",
      "replacementGate",
      "graph",
      "word",
      "compile",
      "result",
      "result_gateCount",
      "compile_success_iff",
      "compile_failure_iff",
      "values",
      "replacementSource_eval",
      "originalSource_eval",
      "values_solution",
      "result_semantics",
      "exterior_accounting",
      "result_exact_accounting",
      "result_strict_gain",
      "PrimaryBoundary",
      "rank",
      "graph_rank_decreases",
      "graph_wellFounded_of_primaryBoundary",
      "production_compiles",
      "production_agreement",
      "graph_wellFounded_of_singleGateBoundary",
      "causalBoundaryLabels",
      "CausalInterfaceBound",
      "causalRank",
      "graph_causal_rank_decreases",
      "graph_wellFounded_of_causalInterfaceBound",
      "compile_of_causalInterfaceBound",
      "dependencyBoundaryLabels",
      "dependencyCaps",
      "DependencyInterfaceBound",
      "graph_dependency_bounds",
      "result_output_dependency_bound",
      "boundarySource_input",
      "boundarySource_gate",
      "originalSource_exterior",
      "originalSource_interface"
    ],
    "imports": [
      "PNP.NANDTopologicalCompiler",
      "PNP.NANDTopologicalCausalBounds",
      "PNP.ResidualTerminalSaturatedSupportContext",
      "PNP.NANDNormalizationCausalBounds"
    ],
    "context": [
      "namespace PNP",
      "namespace DirectWire",
      "namespace ArbitrarySupportSplice",
      "variable {inputs gates outputs profileWidth replacementGates : Nat}",
      "variable (candidate : Candidate inputs gates outputs)",
      "variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))",
      "variable (replacement : Candidate (terminalBoundaryPorts candidate.program records).length replacementGates (terminalInterfacePorts candidate records).length)",
      "variable (labels : Fin inputs → Nat)",
      "end ArbitrarySupportSplice",
      "end DirectWire",
      "end PNP"
    ],
    "signatures": {
      "graph_causal_rank_decreases": "theorem graph_causal_rank_decreases (interfaceBound : CausalInterfaceBound candidate records replacement) (producer consumer : Fin ((exterior records).length + replacementGates)) (edge : (graph candidate records replacement).Depends producer consumer) : causalRank candidate records replacement producer < causalRank candidate records replacement consumer",
      "graph_wellFounded_of_causalInterfaceBound": "theorem graph_wellFounded_of_causalInterfaceBound (interfaceBound : CausalInterfaceBound candidate records replacement) : WellFounded (graph candidate records replacement).Depends",
      "compile_of_causalInterfaceBound": "theorem compile_of_causalInterfaceBound (interfaceBound : CausalInterfaceBound candidate records replacement) : ∃ compiled, compile candidate records replacement = some compiled"
    },
    "guards": [
      [
        "(fun index => (((exterior records).get index).val + 1) * (replacementGates + 1))",
        "original-exterior-rank"
      ],
      [
        "(graph_causal_rank_decreases candidate records replacement interfaceBound)",
        "derived-edge-order"
      ]
    ]
  },
  {
    "path": "lean/PNP/NANDWireHistoryArbitrarySupport.lean",
    "heads": [
      "fieldCandidate",
      "fieldCandidate_semantics",
      "fieldCandidate_outputLevel",
      "extractedCarrier",
      "extractedCarrier_gateCount",
      "extractedCarrier_fieldValue",
      "closedHistory_equivalent",
      "closedHistory_causalInterfaceBound",
      "closedHistory_compiles",
      "closedHistory_result_semantics",
      "closedHistory_result_exact_accounting",
      "closedHistory_result_strict_gain",
      "compile",
      "compile_complete",
      "compile_sound",
      "compile_none_iff"
    ],
    "imports": [
      "PNP.NANDWireHistoryCausalBounds"
    ],
    "context": [
      "namespace PNP.DirectWire.WireHistoryArbitrarySupport open WireObligationHistory",
      "variable {inputs gates outputs profileWidth : Nat}",
      "variable (candidate : Candidate inputs gates outputs)",
      "variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))",
      "variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}",
      "end PNP.DirectWire.WireHistoryArbitrarySupport"
    ],
    "signatures": {
      "extractedCarrier_gateCount": "theorem extractedCarrier_gateCount : (extractedCarrier candidate records).implementation.gateCount = (extractTerminalSupport candidate records).gateCount",
      "extractedCarrier_fieldValue": "theorem extractedCarrier_fieldValue (valuation : Valuation (terminalBoundaryPorts candidate.program records).length) (field : Fin (terminalInterfacePorts candidate records).length) : (extractedCarrier candidate records).fieldValue valuation field = (extractTerminalSupport candidate records).extractedCandidate.semantics valuation field",
      "closedHistory_equivalent": "theorem closedHistory_equivalent (history : ClosedHistory (extractedCarrier candidate records) raw) : (fieldCandidate history.state.current).semantics = (extractTerminalSupport candidate records).extractedCandidate.semantics",
      "closedHistory_causalInterfaceBound": "theorem closedHistory_causalInterfaceBound (history : ClosedHistory (extractedCarrier candidate records) raw) : ArbitrarySupportSplice.CausalInterfaceBound candidate records (fieldCandidate history.state.current)",
      "closedHistory_compiles": "theorem closedHistory_compiles (history : ClosedHistory (extractedCarrier candidate records) raw) : ∃ compiled, ArbitrarySupportSplice.compile candidate records (fieldCandidate history.state.current) = some compiled",
      "closedHistory_result_semantics": "theorem closedHistory_result_semantics (history : ClosedHistory (extractedCarrier candidate records) raw) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) (valuation : Valuation inputs) (output : Fin outputs) : (ArbitrarySupportSplice.result candidate records (fieldCandidate history.state.current) compiled).semantics valuation output = candidate.semantics valuation output",
      "closedHistory_result_exact_accounting": "theorem closedHistory_result_exact_accounting (history : ClosedHistory (extractedCarrier candidate records) raw) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) : (ArbitrarySupportSplice.result candidate records (fieldCandidate history.state.current) compiled).toImplementation.gateCount + history.execution.removed = gates + history.execution.charged",
      "closedHistory_result_strict_gain": "theorem closedHistory_result_strict_gain (history : ClosedHistory (extractedCarrier candidate records) raw) (gain : history.execution.charged < history.execution.removed) (compiled : CompiledRawNandGraph (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) : (ArbitrarySupportSplice.result candidate records (fieldCandidate history.state.current) compiled).toImplementation.gateCount < gates",
      "compile_complete": "theorem compile_complete (history : ClosedHistory (extractedCarrier candidate records) raw) (executed : compileHistory (extractedCarrier candidate records) raw = some history) : ∃ result, compile candidate records raw = some result",
      "compile_sound": "theorem compile_sound (result : Implementation inputs outputs) (accepted : compile candidate records raw = some result) : ∃ history : ClosedHistory (extractedCarrier candidate records) raw, compileHistory (extractedCarrier candidate records) raw = some history ∧ result.gateCount + history.execution.removed = gates + history.execution.charged ∧ (∀ valuation output, result.candidate.semantics valuation output = candidate.semantics valuation output)",
      "compile_none_iff": "theorem compile_none_iff : compile candidate records raw = none ↔ compileHistory (extractedCarrier candidate records) raw = none",
      "extractedCarrier": "def extractedCarrier : WireCarrier (terminalBoundaryPorts candidate.program records).length 0 (terminalInterfacePorts candidate records).length",
      "compile": "def compile (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) : Option (Implementation inputs outputs)"
    },
    "guards": [
      [
        "WireCarrier (terminalBoundaryPorts candidate.program records).length 0 (terminalInterfacePorts candidate records).length",
        "no-duplicate-ordinary-outputs"
      ],
      [
        "source := extracted.directWireWord.source",
        "actual-extracted-fields"
      ],
      [
        "history.field_causal_bound _ field",
        "history-derived-causality"
      ],
      [
        "extractTerminalSupport_causal_index candidate records field",
        "extraction-derived-causality"
      ],
      [
        "match compileHistory (extractedCarrier candidate records) raw with",
        "raw-history-constructor"
      ],
      [
        "(fieldCandidate history.state.current)).map",
        "actual-final-carrier"
      ],
      [
        "history.execution.removed = gates + history.execution.charged",
        "complete-physical-accounting"
      ]
    ]
  }
];
const REVIEWED = [
  [
    "PNP.DirectWire.extractTerminalSupport_causal_levels",
    "PNP.ResidualTerminalSupportExtraction",
    "extractTerminalSupport_causal_levels"
  ],
  [
    "PNP.DirectWire.extractTerminalSupport_causal_index",
    "PNP.ResidualTerminalSupportExtraction",
    "extractTerminalSupport_causal_index"
  ],
  [
    "PNP.DirectWire.CausalBound.physical_normalization_output_bound",
    "PNP.NANDNormalizationCausalBounds",
    "physical_normalization_output_bound"
  ],
  [
    "PNP.DirectWire.WireCarrier.normalize_causalBounds",
    "PNP.NANDWireCausalBounds",
    "normalize_causalBounds"
  ],
  [
    "PNP.DirectWire.WireObligationRestoration.join_causalBounds",
    "PNP.NANDWireCausalBounds",
    "join_causalBounds"
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Transition.causalInvariant",
    "PNP.NANDWireHistoryCausalBounds",
    "Transition.causalInvariant"
  ],
  [
    "PNP.DirectWire.WireObligationHistory.Execution.causalInvariant",
    "PNP.NANDWireHistoryCausalBounds",
    "Execution.causalInvariant"
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.causalInvariant",
    "PNP.NANDWireHistoryCausalBounds",
    "causalInvariant"
  ],
  [
    "PNP.DirectWire.WireObligationHistory.ClosedHistory.field_causal_bound",
    "PNP.NANDWireHistoryCausalBounds",
    "field_causal_bound"
  ],
  [
    "PNP.DirectWire.WireObligationHistory.compileHistory_causal_bounds",
    "PNP.NANDWireHistoryCausalBounds",
    "compileHistory_causal_bounds"
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.graph_causal_rank_decreases",
    "PNP.NANDArbitrarySupportSplice",
    "graph_causal_rank_decreases"
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.graph_wellFounded_of_causalInterfaceBound",
    "PNP.NANDArbitrarySupportSplice",
    "graph_wellFounded_of_causalInterfaceBound"
  ],
  [
    "PNP.DirectWire.ArbitrarySupportSplice.compile_of_causalInterfaceBound",
    "PNP.NANDArbitrarySupportSplice",
    "compile_of_causalInterfaceBound"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.extractedCarrier_gateCount",
    "PNP.NANDWireHistoryArbitrarySupport",
    "extractedCarrier_gateCount"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.extractedCarrier_fieldValue",
    "PNP.NANDWireHistoryArbitrarySupport",
    "extractedCarrier_fieldValue"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_equivalent",
    "PNP.NANDWireHistoryArbitrarySupport",
    "closedHistory_equivalent"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_causalInterfaceBound",
    "PNP.NANDWireHistoryArbitrarySupport",
    "closedHistory_causalInterfaceBound"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_compiles",
    "PNP.NANDWireHistoryArbitrarySupport",
    "closedHistory_compiles"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_semantics",
    "PNP.NANDWireHistoryArbitrarySupport",
    "closedHistory_result_semantics"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_exact_accounting",
    "PNP.NANDWireHistoryArbitrarySupport",
    "closedHistory_result_exact_accounting"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.closedHistory_result_strict_gain",
    "PNP.NANDWireHistoryArbitrarySupport",
    "closedHistory_result_strict_gain"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.compile_complete",
    "PNP.NANDWireHistoryArbitrarySupport",
    "compile_complete"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.compile_sound",
    "PNP.NANDWireHistoryArbitrarySupport",
    "compile_sound"
  ],
  [
    "PNP.DirectWire.WireHistoryArbitrarySupport.compile_none_iff",
    "PNP.NANDWireHistoryArbitrarySupport",
    "compile_none_iff"
  ]
];
const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
function boundaries0(source) {
  return [...stripLeanCommentsAndStrings0(source).matchAll(
    /^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|(variable|namespace|end)\b)/gmu)];
}
function block0(source, name) {
  const boundaries = boundaries0(source);
  const index = boundaries.findIndex(match => match[2] === name);
  return index < 0 ? '' : source.slice(boundaries[index].index,
    boundaries[index + 1]?.index ?? source.length);
}
function signature0(block) {
  const stripped = stripLeanCommentsAndStrings0(block);
  let depth = 0;
  for (let index = 0; index < stripped.length; index += 1) {
    const character = stripped[index];
    if ('([{'.includes(character)) depth += 1;
    else if (')]}'.includes(character)) depth -= 1;
    else if (depth === 0 && (stripped.startsWith(':=', index) ||
        /^where\b/u.test(stripped.slice(index)))) return compact0(stripped.slice(0,index));
  }
  return compact0(stripped);
}
function context0(source) {
  const boundaries = boundaries0(source);
  return boundaries.flatMap((match,index) => ['variable','namespace','end'].includes(match[3])
    ? [compact0(source.slice(match.index,boundaries[index+1]?.index ?? source.length))] : []);
}
function inspect0(source,spec) {
  const failures=[];
  const require0=(condition,category)=>{if(!condition)failures.push(category);};
  const clean=compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source),'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source),'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|implemented_by|csimp)\b|#(?:eval|reduce|guard|synth)\b/u.test(clean),'shortcut');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head=>head.name))===JSON.stringify(spec.heads),'closed-interface');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]))===JSON.stringify(spec.imports),'closed-imports');
  require0(JSON.stringify(context0(source))===JSON.stringify(spec.context),'closed-parameters-and-namespaces');
  for(const [name,signature] of Object.entries(spec.signatures))
    require0(signature0(block0(source,name))===signature,'signature:'+name);
  for(const [fragment,category] of spec.guards)
    require0(clean.includes(fragment),category);
  return failures;
}
const MAIN='lean/PNP/NANDWireHistoryArbitrarySupport.lean';
const HISTORY='lean/PNP/NANDWireHistoryCausalBounds.lean';
const SPLICE='lean/PNP/NANDArbitrarySupportSplice.lean';
const CARRIER='lean/PNP/NANDWireCausalBounds.lean';

test('M264 preserves closed general source interfaces and source-derived causal invariants',async()=>{
  for(const spec of SPECS)assert.deepEqual(inspect0(await text0(spec.path),spec),[],spec.path);
});
test('M264 rejects hidden assumptions, native authority and extra declarations',async()=>{
  for(const spec of SPECS){
    const source=await text0(spec.path);
    assert.ok(inspect0(source+'\naxiom hiddenProgress : False\n',spec).includes('assumption'));
    assert.ok(inspect0(source+'\nunsafe def unchecked : Nat := 0\n',spec).includes('shortcut'));
    assert.ok(inspect0(source+'\nexample : True := True.intro\n',spec).includes('unaudited-form'));
    assert.ok(inspect0(source+'\ntheorem unreviewed : True := True.intro\n',spec).includes('closed-interface'));
    assert.deepEqual(inspect0(source+'\n/- axiom, native_decide and caller data mentioned only in a comment -/\n',spec),[]);
  }
});
test('M264 freezes full theorem types across named arguments and extra caller premises',async()=>{
  const declaration='theorem checked (source : Carrier (fields := fields)) '+
    '(input : Input) : Result (source := source) input := by exact checkedBody';
  assert.equal(signature0(declaration),declaration.slice(0,declaration.lastIndexOf(' := ')));
  assert.notEqual(signature0(declaration.replace('(input :','(supplied : True) (input :')),
    signature0(declaration));
  const spec=SPECS.find(row=>row.path===MAIN),source=await text0(MAIN);
  const anchor='def compile (raw :';
  assert.ok(source.includes(anchor));
  assert.ok(inspect0(source.replace(anchor,'def compile (suppliedOrder : Nat) (raw :'),spec)
    .includes('signature:compile'));
  assert.ok(inspect0(source.replace('variable {inputs gates outputs profileWidth : Nat}',
    'variable {inputs gates outputs profileWidth : Nat}\nvariable (supplied : True)'),spec)
    .includes('closed-parameters-and-namespaces'));
});
test('M264 rejects duplicate protected outputs, supplied causality and substituted physical histories',async()=>{
  for(const [file,before,after,category] of [
    [MAIN,'records).length 0\n      (terminalInterfacePorts','records).length 1\n      (terminalInterfacePorts','no-duplicate-ordinary-outputs'],
    [MAIN,'source := extracted.directWireWord.source','source := suppliedFields','actual-extracted-fields'],
    [MAIN,'history.field_causal_bound _ field','suppliedCausalBound field','history-derived-causality'],
    [MAIN,'extractTerminalSupport_causal_index candidate records field','suppliedExtractionBound field','extraction-derived-causality'],
    [MAIN,'match compileHistory (extractedCarrier candidate records) raw with','match suppliedHistory with','raw-history-constructor'],
    [MAIN,'(fieldCandidate history.state.current)).map','(fieldCandidate (extractedCarrier candidate records))).map','actual-final-carrier'],
    [HISTORY,'bounded.2 field snapshot found','suppliedSnapshotBound','actual-pending-snapshot-bound'],
    [HISTORY,'rw [alias.sourceExact]','rw [suppliedSemanticEquality]','literal-r6-source-identity'],
    [HISTORY,'history.execution.causalInvariant labels (State.initial_causalInvariant source labels)',
      'suppliedHistoryInvariant','source-initialized-history-invariant'],
    [SPLICE,'(fun index => (((exterior records).get index).val + 1) * (replacementGates + 1))',
      '(fun _ => 0)','original-exterior-rank'],
    [SPLICE,'(graph_causal_rank_decreases candidate records replacement interfaceBound)',
      '(suppliedDecreasingRank)','derived-edge-order'],
    [CARRIER,'missing.implementation.candidate.program','suppliedMaterializerProgram','actual-joined-materializer'],
  ]){
    const spec=SPECS.find(row=>row.path===file),source=await text0(file);
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(inspect0(source.replaceAll(before,after),spec).includes(category),category);
  }
});
test('M264 root and exact reviewed theorem producers agree before inventory sealing',async()=>{
  const names=REVIEWED.map(row=>row[0]);
  assert.equal(new Set(names).size,names.length);
  const [root,inventory,audit]=await Promise.all([
    text0('lean/PNP.lean'),text0('lean-audit/PNPTheoremInventory.lean'),
    text0('lean-audit/PNPWireHistoryArbitrarySupportAxiomAudit.lean')]);
  assert.ok(root.includes('import PNP.NANDWireHistoryArbitrarySupport'));
  const printed=[...audit.matchAll(/^#print axioms (.+)$/gmu)].map(match=>match[1]);
  assert.deepEqual(printed,names);
  const publication=JSON.parse(await text0('publication/FORMAL_PUBLICATION_MAP.json'));
  assert.deepEqual(publication.milestones.find(row=>row.id==='wire-history-arbitrary-support')?.requiredTheorems,names);
  for(const name of names){
    assert.ok(Object.hasOwn(publication.earnedMilestoneTheoremKernelTypeSha256,name),name);
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value=>value===name).length,1,name);
    assert.equal(inventory.split(String.fromCharCode(96)+name+',').length-1,1,name);
  }
});
test('M264 regression retains general proofs, interleaved boundaries, paid restoration and hostile rejection',async()=>{
  const source=await text0('lean-regression/PNPWireHistoryArbitrarySupport.lean');
  for(const fragment of [
    'closedHistory_compiles candidate records history',
    'compile_sound candidate records result accepted',
    '[.input 0, .gate 1, .gate 3]',
    'checkRun chain interleaved restoreMiddle 5 1 1',
    'checkRun saving savingRecords [⟨10, [], .normalize⟩] 3 0 1',
    'checkRun zero zeroRecords [] 0 0 0',
    'checkRun unused unusedRecords [⟨10, [], .normalize⟩] 0 0 1',
    '¬ArbitrarySupportSplice.CausalInterfaceBound',
    'cyclicReplacement.semantics',
    'unclosed obligation was silently accepted',
    'missing creation reference was silently accepted',
    'Boolean equivalence bypassed literal-cycle rejection',
    'HISTORY_ARBITRARY_SUPPORT_RUNTIME_FIXTURES_GREEN',
  ])assert.ok(source.includes(fragment),fragment);
});
