import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from the reviewed general implementation and compiled closures.
// Tests never derive these expectations from the source being checked.
const SPECS = [
  {
    "part": "SupportSplice",
    "path": "lean/PNP/NANDWireOpenSupportSplice.lean",
    "sourceContractSha256": "817946d6f5422adcfa933710dc4c45ddd4cf200c94a49610aad1367332590cc3",
    "heads": [
      {
        "kind": "def",
        "name": "transfer"
      },
      {
        "kind": "theorem",
        "name": "transfer_pending"
      },
      {
        "kind": "theorem",
        "name": "transfer_keep"
      },
      {
        "kind": "theorem",
        "name": "transfer_snapshot"
      },
      {
        "kind": "theorem",
        "name": "transfer_charge"
      },
      {
        "kind": "theorem",
        "name": "transfer_removal"
      },
      {
        "kind": "theorem",
        "name": "transfer_output"
      },
      {
        "kind": "theorem",
        "name": "transfer_available"
      },
      {
        "kind": "theorem",
        "name": "transfer_balance"
      },
      {
        "kind": "theorem",
        "name": "replacement_dependency_bound"
      },
      {
        "kind": "theorem",
        "name": "result_exposed_dependency_bound"
      },
      {
        "kind": "theorem",
        "name": "result_causal_bounds"
      },
      {
        "kind": "theorem",
        "name": "transfer_causal_invariant"
      },
      {
        "kind": "structure",
        "name": "Receipt"
      },
      {
        "kind": "def",
        "name": "next"
      },
      {
        "kind": "theorem",
        "name": "pending"
      },
      {
        "kind": "theorem",
        "name": "records_source"
      },
      {
        "kind": "def",
        "name": "execute"
      },
      {
        "kind": "theorem",
        "name": "execute_of_compiled"
      },
      {
        "kind": "theorem",
        "name": "execute_exists_iff"
      }
    ]
  },
  {
    "part": "ProgramInput",
    "path": "lean/PNP/NANDWireOpenProgramInput.lean",
    "sourceContractSha256": "39c6252386d583adba8b51f1edc3d6fefe56fd36dfacc7a1da789e04ae03f2eb",
    "heads": [
      {
        "kind": "inductive",
        "name": "Action"
      },
      {
        "kind": "def",
        "name": "Action.creationDependencies"
      },
      {
        "kind": "structure",
        "name": "RawEvent"
      },
      {
        "kind": "def",
        "name": "RawEvent.dependencies"
      },
      {
        "kind": "def",
        "name": "UniqueIDs"
      },
      {
        "kind": "def",
        "name": "CompleteReferences"
      },
      {
        "kind": "def",
        "name": "uniqueIDs"
      },
      {
        "kind": "theorem",
        "name": "uniqueIDs_iff"
      },
      {
        "kind": "def",
        "name": "completeReferences"
      },
      {
        "kind": "theorem",
        "name": "completeReferences_iff"
      },
      {
        "kind": "def",
        "name": "eventGraph"
      },
      {
        "kind": "theorem",
        "name": "graph_dependency_iff"
      },
      {
        "kind": "structure",
        "name": "OrderedEvents"
      },
      {
        "kind": "def",
        "name": "OrderedEvents.order"
      },
      {
        "kind": "theorem",
        "name": "OrderedEvents.order_complete"
      },
      {
        "kind": "theorem",
        "name": "OrderedEvents.order_nodup"
      },
      {
        "kind": "theorem",
        "name": "OrderedEvents.order_length"
      },
      {
        "kind": "theorem",
        "name": "OrderedEvents.identities_nodup"
      },
      {
        "kind": "def",
        "name": "orderEvents"
      },
      {
        "kind": "theorem",
        "name": "orderEvents_success_iff"
      },
      {
        "kind": "theorem",
        "name": "orderEvents_failure_iff"
      }
    ]
  },
  {
    "part": "Program",
    "path": "lean/PNP/NANDWireOpenProgram.lean",
    "sourceContractSha256": "2742e9169efac1295fe3030eafe2eb0eeef7a4fe0674557e76769f06392748dd",
    "heads": [
      {
        "kind": "def",
        "name": "RawEvent.primitiveEvent"
      },
      {
        "kind": "inductive",
        "name": "Transition"
      },
      {
        "kind": "def",
        "name": "applyEvent"
      },
      {
        "kind": "def",
        "name": "charged"
      },
      {
        "kind": "def",
        "name": "removed"
      },
      {
        "kind": "theorem",
        "name": "charged_eq"
      },
      {
        "kind": "theorem",
        "name": "removed_eq"
      },
      {
        "kind": "def",
        "name": "created"
      },
      {
        "kind": "def",
        "name": "discharged"
      },
      {
        "kind": "def",
        "name": "dischargeRecord"
      },
      {
        "kind": "def",
        "name": "fullRead"
      },
      {
        "kind": "theorem",
        "name": "dischargeRecord_binding"
      },
      {
        "kind": "theorem",
        "name": "pending_persists_or_discharged"
      },
      {
        "kind": "theorem",
        "name": "created_pending"
      },
      {
        "kind": "theorem",
        "name": "causalInvariant"
      },
      {
        "kind": "def",
        "name": "record"
      },
      {
        "kind": "inductive",
        "name": "Execution"
      },
      {
        "kind": "def",
        "name": "execute"
      },
      {
        "kind": "theorem",
        "name": "execute_failed_tail"
      },
      {
        "kind": "def",
        "name": "charged"
      },
      {
        "kind": "def",
        "name": "removed"
      },
      {
        "kind": "def",
        "name": "records"
      },
      {
        "kind": "theorem",
        "name": "total_charge"
      },
      {
        "kind": "theorem",
        "name": "total_removed"
      },
      {
        "kind": "theorem",
        "name": "record_identities"
      },
      {
        "kind": "def",
        "name": "Discharged"
      },
      {
        "kind": "theorem",
        "name": "pending_persists_or_discharged"
      },
      {
        "kind": "def",
        "name": "CreationsClosed"
      },
      {
        "kind": "theorem",
        "name": "creationsClosed_of_finalClosed"
      },
      {
        "kind": "theorem",
        "name": "causalInvariant"
      },
      {
        "kind": "structure",
        "name": "CompiledProgram"
      },
      {
        "kind": "def",
        "name": "compile"
      },
      {
        "kind": "def",
        "name": "result"
      },
      {
        "kind": "theorem",
        "name": "closed"
      },
      {
        "kind": "theorem",
        "name": "full_output"
      },
      {
        "kind": "theorem",
        "name": "full_field"
      },
      {
        "kind": "theorem",
        "name": "gate_balance"
      },
      {
        "kind": "theorem",
        "name": "creation_lifecycle"
      },
      {
        "kind": "theorem",
        "name": "executed_count"
      },
      {
        "kind": "theorem",
        "name": "executed_identities_nodup"
      },
      {
        "kind": "theorem",
        "name": "dependency_before"
      },
      {
        "kind": "theorem",
        "name": "causalInvariant"
      },
      {
        "kind": "theorem",
        "name": "output_causal_bound"
      },
      {
        "kind": "theorem",
        "name": "field_causal_bound"
      },
      {
        "kind": "theorem",
        "name": "compile_exists_iff"
      },
      {
        "kind": "theorem",
        "name": "compile_none_iff"
      }
    ]
  },
  {
    "part": "SupportOwnership",
    "path": "lean/PNP/NANDWireOpenSupportOwnership.lean",
    "sourceContractSha256": "2e104aad50d64b1ecad1cf977cf7731fd1b6c9e1fa0402617cd670553e1209a5",
    "heads": [
      {
        "kind": "def",
        "name": "ownershipLift"
      },
      {
        "kind": "theorem",
        "name": "ownershipLift_original"
      },
      {
        "kind": "theorem",
        "name": "ownershipLift_allocated"
      },
      {
        "kind": "theorem",
        "name": "ownershipLift_injective"
      },
      {
        "kind": "def",
        "name": "ownershipRawNode"
      },
      {
        "kind": "theorem",
        "name": "ownershipRawNode_exterior"
      },
      {
        "kind": "theorem",
        "name": "ownershipRawNode_nested"
      },
      {
        "kind": "def",
        "name": "ownership"
      },
      {
        "kind": "theorem",
        "name": "ownership_compiled_position"
      },
      {
        "kind": "theorem",
        "name": "ownership_partition"
      },
      {
        "kind": "theorem",
        "name": "ownership_charged_origin"
      },
      {
        "kind": "theorem",
        "name": "ownership_distinct"
      },
      {
        "kind": "theorem",
        "name": "physical_ownership"
      },
      {
        "kind": "def",
        "name": "ownership"
      },
      {
        "kind": "theorem",
        "name": "physical_ownership"
      }
    ]
  },
  {
    "part": "PrimitiveOwnership",
    "path": "lean/PNP/NANDWireOpenPrimitiveOwnership.lean",
    "sourceContractSha256": "36225f8e377208445247872da886f17a81e69487ff9fa0a05201f5238c9700c9",
    "heads": [
      {
        "kind": "def",
        "name": "advance"
      },
      {
        "kind": "def",
        "name": "allocations"
      },
      {
        "kind": "theorem",
        "name": "allocations_nodup"
      },
      {
        "kind": "theorem",
        "name": "advance_charged"
      },
      {
        "kind": "theorem",
        "name": "advance_removed_length"
      },
      {
        "kind": "theorem",
        "name": "advance_conservation"
      },
      {
        "kind": "def",
        "name": "ledger"
      },
      {
        "kind": "theorem",
        "name": "ledger_charged"
      },
      {
        "kind": "theorem",
        "name": "ledger_removed_length"
      },
      {
        "kind": "theorem",
        "name": "ledger_partition"
      },
      {
        "kind": "theorem",
        "name": "physical_ownership"
      },
      {
        "kind": "def",
        "name": "lift"
      },
      {
        "kind": "theorem",
        "name": "lift_injective"
      },
      {
        "kind": "def",
        "name": "labelled"
      },
      {
        "kind": "theorem",
        "name": "labelled_live"
      },
      {
        "kind": "theorem",
        "name": "labelled_physical_ownership"
      },
      {
        "kind": "theorem",
        "name": "labelled_charged_origin"
      }
    ]
  },
  {
    "part": "ProgramOwnership",
    "path": "lean/PNP/NANDWireOpenProgramOwnership.lean",
    "sourceContractSha256": "95d499f4e1e11a1417c5c6a2246bdd336e3387d41757e598b5e1c069c95d1b82",
    "heads": [
      {
        "kind": "def",
        "name": "localLedger"
      },
      {
        "kind": "theorem",
        "name": "local_physical_ownership"
      },
      {
        "kind": "theorem",
        "name": "local_charged_origin"
      },
      {
        "kind": "inductive",
        "name": "ProgramOrigin"
      },
      {
        "kind": "def",
        "name": "programOriginals"
      },
      {
        "kind": "def",
        "name": "bornBefore"
      },
      {
        "kind": "theorem",
        "name": "bornBefore_mono"
      },
      {
        "kind": "structure",
        "name": "ProgramOwnership"
      },
      {
        "kind": "def",
        "name": "live"
      },
      {
        "kind": "def",
        "name": "initial"
      },
      {
        "kind": "structure",
        "name": "WellFormed"
      },
      {
        "kind": "theorem",
        "name": "initial_wellFormed"
      },
      {
        "kind": "theorem",
        "name": "accounted_before"
      },
      {
        "kind": "theorem",
        "name": "origin_before"
      },
      {
        "kind": "theorem",
        "name": "origin_injective"
      },
      {
        "kind": "def",
        "name": "liftOrigin"
      },
      {
        "kind": "theorem",
        "name": "liftOrigin_original"
      },
      {
        "kind": "theorem",
        "name": "liftOrigin_allocated"
      },
      {
        "kind": "theorem",
        "name": "liftOrigin_injective"
      },
      {
        "kind": "theorem",
        "name": "lift_originals"
      },
      {
        "kind": "def",
        "name": "advance"
      },
      {
        "kind": "theorem",
        "name": "advance_live"
      },
      {
        "kind": "theorem",
        "name": "advance_charged_length"
      },
      {
        "kind": "theorem",
        "name": "advance_removed_length"
      },
      {
        "kind": "theorem",
        "name": "advance_charge_origin"
      },
      {
        "kind": "theorem",
        "name": "advance_physical_position"
      },
      {
        "kind": "theorem",
        "name": "advance_support_compiled_position"
      },
      {
        "kind": "theorem",
        "name": "advance_partition"
      },
      {
        "kind": "theorem",
        "name": "advance_wellFormed"
      },
      {
        "kind": "def",
        "name": "carryOwnership"
      },
      {
        "kind": "theorem",
        "name": "carryOwnership_wellFormed"
      },
      {
        "kind": "theorem",
        "name": "carryOwnership_charged_length"
      },
      {
        "kind": "theorem",
        "name": "carryOwnership_removed_length"
      },
      {
        "kind": "theorem",
        "name": "carryOwnership_charge_survives"
      },
      {
        "kind": "def",
        "name": "ownership"
      },
      {
        "kind": "theorem",
        "name": "ownership_wellFormed"
      },
      {
        "kind": "theorem",
        "name": "physical_ownership"
      },
      {
        "kind": "theorem",
        "name": "ownership_origin_injective"
      },
      {
        "kind": "theorem",
        "name": "ownership_charge_origin"
      },
      {
        "kind": "theorem",
        "name": "allocation_namespaces_disjoint"
      }
    ]
  },
  {
    "part": "ProperSupport",
    "path": "lean/PNP/NANDWireOpenProperSupport.lean",
    "sourceContractSha256": "06e2c2033f229290d2ed653d6169a4942fd48365c6676c63bef1aa08fd384b6c",
    "heads": [
      {
        "kind": "def",
        "name": "localSource"
      },
      {
        "kind": "theorem",
        "name": "program_equivalent"
      },
      {
        "kind": "theorem",
        "name": "program_causalInterfaceBound"
      },
      {
        "kind": "theorem",
        "name": "program_compiles"
      },
      {
        "kind": "structure",
        "name": "SplicedProgram"
      },
      {
        "kind": "def",
        "name": "result"
      },
      {
        "kind": "theorem",
        "name": "output"
      },
      {
        "kind": "theorem",
        "name": "field"
      },
      {
        "kind": "theorem",
        "name": "gateCount"
      },
      {
        "kind": "theorem",
        "name": "charge_accounting"
      },
      {
        "kind": "theorem",
        "name": "gain_iff_local_gain"
      },
      {
        "kind": "theorem",
        "name": "gain_iff_net_charges"
      },
      {
        "kind": "theorem",
        "name": "strictGain"
      },
      {
        "kind": "theorem",
        "name": "strictResidualDescent"
      },
      {
        "kind": "def",
        "name": "compile"
      },
      {
        "kind": "theorem",
        "name": "compile_complete"
      },
      {
        "kind": "theorem",
        "name": "compile_exists_iff"
      },
      {
        "kind": "theorem",
        "name": "compile_none_iff"
      }
    ]
  },
  {
    "part": "ProperOwnership",
    "path": "lean/PNP/NANDWireOpenProperOwnership.lean",
    "sourceContractSha256": "ec2f83b453ac6a29d3f25a6e52e5d37dada90c71a31c56313d883cb8f0ac7f66",
    "heads": [
      {
        "kind": "def",
        "name": "ownershipLift"
      },
      {
        "kind": "theorem",
        "name": "ownershipLift_original"
      },
      {
        "kind": "theorem",
        "name": "ownershipLift_allocated"
      },
      {
        "kind": "theorem",
        "name": "ownershipLift_injective"
      },
      {
        "kind": "def",
        "name": "ownershipRawNode"
      },
      {
        "kind": "theorem",
        "name": "ownershipRawNode_exterior"
      },
      {
        "kind": "theorem",
        "name": "ownershipRawNode_program"
      },
      {
        "kind": "def",
        "name": "ownership"
      },
      {
        "kind": "theorem",
        "name": "ownership_compiled_position"
      },
      {
        "kind": "theorem",
        "name": "ownership_partition"
      },
      {
        "kind": "theorem",
        "name": "ownership_charged_origin"
      },
      {
        "kind": "theorem",
        "name": "ownership_distinct"
      },
      {
        "kind": "theorem",
        "name": "physical_ownership"
      }
    ]
  },
  {
    "part": "Certificate",
    "path": "lean/PNP/NANDWireOpenCertificate.lean",
    "sourceContractSha256": "a3b7b057902b2296b6b1afec1d4e84daed81a897702d152c8bee724002539aea",
    "heads": [
      {
        "kind": "structure",
        "name": "RawCertificate"
      },
      {
        "kind": "structure",
        "name": "CheckedCertificate"
      },
      {
        "kind": "def",
        "name": "result"
      },
      {
        "kind": "theorem",
        "name": "records_source"
      },
      {
        "kind": "theorem",
        "name": "proper_support"
      },
      {
        "kind": "theorem",
        "name": "output"
      },
      {
        "kind": "theorem",
        "name": "field"
      },
      {
        "kind": "theorem",
        "name": "gateCount"
      },
      {
        "kind": "theorem",
        "name": "charge_accounting"
      },
      {
        "kind": "theorem",
        "name": "strictGain"
      },
      {
        "kind": "theorem",
        "name": "strictResidualDescent"
      },
      {
        "kind": "def",
        "name": "ownership"
      },
      {
        "kind": "theorem",
        "name": "physical_ownership"
      },
      {
        "kind": "theorem",
        "name": "closed_ledger"
      },
      {
        "kind": "theorem",
        "name": "creation_lifecycle"
      },
      {
        "kind": "def",
        "name": "verify"
      },
      {
        "kind": "theorem",
        "name": "verify_complete"
      },
      {
        "kind": "theorem",
        "name": "verify_exists_iff"
      },
      {
        "kind": "theorem",
        "name": "verify_sound"
      },
      {
        "kind": "theorem",
        "name": "verify_decode_none"
      },
      {
        "kind": "theorem",
        "name": "verify_program_none"
      },
      {
        "kind": "theorem",
        "name": "verify_not_proper"
      },
      {
        "kind": "theorem",
        "name": "verify_no_gain"
      }
    ]
  }
];

const REGRESSIONS = [
  {
    "part": "SupportSplice",
    "path": "lean-regression/PNPWireOpenSupportSplice.lean",
    "printedNames": [
      "transfer_pending",
      "transfer_keep",
      "transfer_snapshot",
      "transfer_charge",
      "transfer_removal",
      "transfer_output",
      "transfer_available",
      "transfer_balance",
      "replacement_dependency_bound",
      "result_exposed_dependency_bound",
      "result_causal_bounds",
      "transfer_causal_invariant",
      "Receipt.pending",
      "Receipt.records_source",
      "execute_of_compiled",
      "execute_exists_iff"
    ],
    "names": [
      "PNP.DirectWire.WireOpenSupportSplice.transfer_pending",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_keep",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_snapshot",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_charge",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_removal",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_output",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_available",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_balance",
      "PNP.DirectWire.WireOpenSupportSplice.replacement_dependency_bound",
      "PNP.DirectWire.WireOpenSupportSplice.result_exposed_dependency_bound",
      "PNP.DirectWire.WireOpenSupportSplice.result_causal_bounds",
      "PNP.DirectWire.WireOpenSupportSplice.transfer_causal_invariant",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.pending",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.records_source",
      "PNP.DirectWire.WireOpenSupportSplice.execute_of_compiled",
      "PNP.DirectWire.WireOpenSupportSplice.execute_exists_iff"
    ]
  },
  {
    "part": "Program",
    "path": "lean-regression/PNPWireOpenProgram.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenProgram.uniqueIDs_iff",
      "PNP.DirectWire.WireOpenProgram.completeReferences_iff",
      "PNP.DirectWire.WireOpenProgram.graph_dependency_iff",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_complete",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_nodup",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_length",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.identities_nodup",
      "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
      "PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff",
      "PNP.DirectWire.WireOpenProgram.Transition.charged_eq",
      "PNP.DirectWire.WireOpenProgram.Transition.removed_eq",
      "PNP.DirectWire.WireOpenProgram.Transition.dischargeRecord_binding",
      "PNP.DirectWire.WireOpenProgram.Transition.pending_persists_or_discharged",
      "PNP.DirectWire.WireOpenProgram.Transition.created_pending",
      "PNP.DirectWire.WireOpenProgram.Transition.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
      "PNP.DirectWire.WireOpenProgram.Execution.total_charge",
      "PNP.DirectWire.WireOpenProgram.Execution.total_removed",
      "PNP.DirectWire.WireOpenProgram.Execution.record_identities",
      "PNP.DirectWire.WireOpenProgram.Execution.pending_persists_or_discharged",
      "PNP.DirectWire.WireOpenProgram.Execution.creationsClosed_of_finalClosed",
      "PNP.DirectWire.WireOpenProgram.Execution.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.closed",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.dependency_before",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.output_causal_bound",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.field_causal_bound",
      "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
      "PNP.DirectWire.WireOpenProgram.compile_none_iff"
    ],
    "names": [
      "PNP.DirectWire.WireOpenProgram.uniqueIDs_iff",
      "PNP.DirectWire.WireOpenProgram.completeReferences_iff",
      "PNP.DirectWire.WireOpenProgram.graph_dependency_iff",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_complete",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_nodup",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.order_length",
      "PNP.DirectWire.WireOpenProgram.OrderedEvents.identities_nodup",
      "PNP.DirectWire.WireOpenProgram.orderEvents_success_iff",
      "PNP.DirectWire.WireOpenProgram.orderEvents_failure_iff",
      "PNP.DirectWire.WireOpenProgram.Transition.charged_eq",
      "PNP.DirectWire.WireOpenProgram.Transition.removed_eq",
      "PNP.DirectWire.WireOpenProgram.Transition.dischargeRecord_binding",
      "PNP.DirectWire.WireOpenProgram.Transition.pending_persists_or_discharged",
      "PNP.DirectWire.WireOpenProgram.Transition.created_pending",
      "PNP.DirectWire.WireOpenProgram.Transition.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.execute_failed_tail",
      "PNP.DirectWire.WireOpenProgram.Execution.total_charge",
      "PNP.DirectWire.WireOpenProgram.Execution.total_removed",
      "PNP.DirectWire.WireOpenProgram.Execution.record_identities",
      "PNP.DirectWire.WireOpenProgram.Execution.pending_persists_or_discharged",
      "PNP.DirectWire.WireOpenProgram.Execution.creationsClosed_of_finalClosed",
      "PNP.DirectWire.WireOpenProgram.Execution.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.closed",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_output",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.full_field",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.gate_balance",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.creation_lifecycle",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_count",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.executed_identities_nodup",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.dependency_before",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.causalInvariant",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.output_causal_bound",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.field_causal_bound",
      "PNP.DirectWire.WireOpenProgram.compile_exists_iff",
      "PNP.DirectWire.WireOpenProgram.compile_none_iff"
    ]
  },
  {
    "part": "SupportOwnership",
    "path": "lean-regression/PNPWireOpenSupportOwnership.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_original",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_allocated",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_injective",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_exterior",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_nested",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_compiled_position",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_partition",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_charged_origin",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_distinct",
      "PNP.DirectWire.WireOpenSupportSplice.physical_ownership",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.physical_ownership"
    ],
    "names": [
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_original",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_allocated",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipLift_injective",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_exterior",
      "PNP.DirectWire.WireOpenSupportSplice.ownershipRawNode_nested",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_compiled_position",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_partition",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_charged_origin",
      "PNP.DirectWire.WireOpenSupportSplice.ownership_distinct",
      "PNP.DirectWire.WireOpenSupportSplice.physical_ownership",
      "PNP.DirectWire.WireOpenSupportSplice.Receipt.physical_ownership"
    ]
  },
  {
    "part": "PrimitiveOwnership",
    "path": "lean-regression/PNPWireOpenPrimitiveOwnership.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.allocations_nodup",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_charged",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_removed_length",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_conservation",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_charged",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_removed_length",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_partition",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.lift_injective",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_live",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_charged_origin"
    ],
    "names": [
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.allocations_nodup",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_charged",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_removed_length",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.advance_conservation",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_charged",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_removed_length",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.ledger_partition",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.lift_injective",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_live",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_physical_ownership",
      "PNP.DirectWire.WireOpenProgram.PrimitiveOwnership.labelled_charged_origin"
    ]
  },
  {
    "part": "ProgramOwnership",
    "path": "lean-regression/PNPWireOpenProgramOwnership.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership",
      "PNP.DirectWire.WireOpenProgram.Transition.local_charged_origin",
      "PNP.DirectWire.WireOpenProgram.bornBefore_mono",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.initial_wellFormed",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.accounted_before",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_before",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_injective",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_original",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_allocated",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_injective",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.lift_originals",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_live",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charged_length",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_removed_length",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charge_origin",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_physical_position",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_support_compiled_position",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_partition",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_wellFormed",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_wellFormed",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charged_length",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_removed_length",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charge_survives",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_wellFormed",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin",
      "PNP.DirectWire.WireOpenProgram.allocation_namespaces_disjoint"
    ],
    "names": [
      "PNP.DirectWire.WireOpenProgram.Transition.local_physical_ownership",
      "PNP.DirectWire.WireOpenProgram.Transition.local_charged_origin",
      "PNP.DirectWire.WireOpenProgram.bornBefore_mono",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.initial_wellFormed",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.accounted_before",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_before",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.origin_injective",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_original",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_allocated",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.liftOrigin_injective",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.lift_originals",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_live",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charged_length",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_removed_length",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_charge_origin",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_physical_position",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_support_compiled_position",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_partition",
      "PNP.DirectWire.WireOpenProgram.ProgramOwnership.advance_wellFormed",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_wellFormed",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charged_length",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_removed_length",
      "PNP.DirectWire.WireOpenProgram.Execution.carryOwnership_charge_survives",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_wellFormed",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.physical_ownership",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_origin_injective",
      "PNP.DirectWire.WireOpenProgram.CompiledProgram.ownership_charge_origin",
      "PNP.DirectWire.WireOpenProgram.allocation_namespaces_disjoint"
    ]
  },
  {
    "part": "ProperSupport",
    "path": "lean-regression/PNPWireOpenProperSupport.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenProperSupport.program_equivalent",
      "PNP.DirectWire.WireOpenProperSupport.program_causalInterfaceBound",
      "PNP.DirectWire.WireOpenProperSupport.program_compiles",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.output",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.field",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gateCount",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.charge_accounting",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_local_gain",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_net_charges",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictGain",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictResidualDescent",
      "PNP.DirectWire.WireOpenProperSupport.compile_complete",
      "PNP.DirectWire.WireOpenProperSupport.compile_exists_iff",
      "PNP.DirectWire.WireOpenProperSupport.compile_none_iff"
    ],
    "names": [
      "PNP.DirectWire.WireOpenProperSupport.program_equivalent",
      "PNP.DirectWire.WireOpenProperSupport.program_causalInterfaceBound",
      "PNP.DirectWire.WireOpenProperSupport.program_compiles",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.output",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.field",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gateCount",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.charge_accounting",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_local_gain",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.gain_iff_net_charges",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictGain",
      "PNP.DirectWire.WireOpenProperSupport.SplicedProgram.strictResidualDescent",
      "PNP.DirectWire.WireOpenProperSupport.compile_complete",
      "PNP.DirectWire.WireOpenProperSupport.compile_exists_iff",
      "PNP.DirectWire.WireOpenProperSupport.compile_none_iff"
    ]
  },
  {
    "part": "ProperOwnership",
    "path": "lean-regression/PNPWireOpenProperOwnership.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_original",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_allocated",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_injective",
      "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_exterior",
      "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_program",
      "PNP.DirectWire.WireOpenProperSupport.ownership_compiled_position",
      "PNP.DirectWire.WireOpenProperSupport.ownership_partition",
      "PNP.DirectWire.WireOpenProperSupport.ownership_charged_origin",
      "PNP.DirectWire.WireOpenProperSupport.ownership_distinct",
      "PNP.DirectWire.WireOpenProperSupport.physical_ownership"
    ],
    "names": [
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_original",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_allocated",
      "PNP.DirectWire.WireOpenProperSupport.ownershipLift_injective",
      "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_exterior",
      "PNP.DirectWire.WireOpenProperSupport.ownershipRawNode_program",
      "PNP.DirectWire.WireOpenProperSupport.ownership_compiled_position",
      "PNP.DirectWire.WireOpenProperSupport.ownership_partition",
      "PNP.DirectWire.WireOpenProperSupport.ownership_charged_origin",
      "PNP.DirectWire.WireOpenProperSupport.ownership_distinct",
      "PNP.DirectWire.WireOpenProperSupport.physical_ownership"
    ]
  },
  {
    "part": "Certificate",
    "path": "lean-regression/PNPWireOpenCertificate.lean",
    "printedNames": [
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.gateCount",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
      "PNP.DirectWire.WireOpenCertificate.verify_complete",
      "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
      "PNP.DirectWire.WireOpenCertificate.verify_sound",
      "PNP.DirectWire.WireOpenCertificate.verify_decode_none",
      "PNP.DirectWire.WireOpenCertificate.verify_program_none",
      "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
      "PNP.DirectWire.WireOpenCertificate.verify_no_gain"
    ],
    "names": [
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.records_source",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.proper_support",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.output",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.field",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.gateCount",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.charge_accounting",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictGain",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.strictResidualDescent",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.physical_ownership",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.closed_ledger",
      "PNP.DirectWire.WireOpenCertificate.CheckedCertificate.creation_lifecycle",
      "PNP.DirectWire.WireOpenCertificate.verify_complete",
      "PNP.DirectWire.WireOpenCertificate.verify_exists_iff",
      "PNP.DirectWire.WireOpenCertificate.verify_sound",
      "PNP.DirectWire.WireOpenCertificate.verify_decode_none",
      "PNP.DirectWire.WireOpenCertificate.verify_program_none",
      "PNP.DirectWire.WireOpenCertificate.verify_not_proper",
      "PNP.DirectWire.WireOpenCertificate.verify_no_gain"
    ]
  }
];

const text0 = file => readFile(new URL('../' + file,import.meta.url),'utf8');
const compact0 = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu,' ').trim();
const digest0 = source => createHash('sha256').update(compact0(source)).digest('hex');
function inspect0(source,spec) {
  const failures=[],clean=compact0(source);
  if(hasLeanAssumptionDeclaration0(source))failures.push('assumption');
  if(hasUnauditedLeanDeclarationForm0(source))failures.push('unaudited-form');
  if(/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical|implemented_by|csimp)\b|#(?:eval|reduce|guard|synth)\b/u.test(clean))
    failures.push('shortcut');
  if(JSON.stringify(explicitLeanDeclarationHeads0(source).map(({kind,name})=>({kind,name})))!==
      JSON.stringify(spec.heads))failures.push('closed-declarations');
  if(digest0(source)!==spec.sourceContractSha256)failures.push('reviewed-source-contract');
  return failures;
}
let loaded;
function sources0() {
  loaded??=Promise.all(SPECS.map(async spec=>({spec,source:await text0(spec.path)})));
  return loaded;
}
function mutate0(source,from,to) {
  assert.ok(source.includes(from),'mutation target exists: '+from);
  const changed=source.replace(from,to);
  assert.notEqual(changed,source);
  return changed;
}
async function rejectMutations0(suffix,mutations) {
  const {spec,source}=(await sources0()).find(row=>row.spec.part===suffix);
  for(const [label,from,to] of mutations)
    assert.ok(inspect0(mutate0(source,from,to),spec).length>0,label);
}

test('M269 source: all arbitrary-dimension implementation contracts are closed',async()=>{
  assert.deepEqual(SPECS.map(spec=>spec.part),[
    'SupportSplice','ProgramInput','Program','SupportOwnership','PrimitiveOwnership',
    'ProgramOwnership','ProperSupport','ProperOwnership','Certificate',
  ]);
  assert.deepEqual(REGRESSIONS.map(row=>row.names.length),[16,35,11,12,28,14,10,18]);
  const names=REGRESSIONS.flatMap(row=>row.names);
  assert.equal(names.length,144);
  assert.equal(new Set(names).size,144);
  for(const {spec,source} of await sources0())assert.deepEqual(inspect0(source,spec),[],spec.path);
});

test('M269 source: hidden premises, private shortcuts and extra authority reject',async()=>{
  for(const {spec,source} of await sources0()) {
    for(const extra of [
      'axiom hiddenAuthority : True','private axiom hiddenAuthority : True',
      'opaque hiddenAuthority : True','variable (suppliedCorrectness : Prop)',
      'import PNP.Main','unsafe def hiddenAuthority : Nat := 0',
      'private theorem hiddenAuthority : True := by trivial',
      'example : True := by trivial','def hiddenAuthority : Nat := 0',
    ])assert.ok(inspect0(source+'\n'+extra+'\n',spec).length>0,spec.path+': '+extra);
    assert.deepEqual(inspect0(source+'\n/- prose: axiom suppliedCorrectness : True -/\n',spec),[]);
  }
});

test('M269 source: support transfer retains the exact live snapshots and actual costs',async()=>{
  await rejectMutations0('SupportSplice',[
    ['same pending function','pending := before.pending','pending := fun _ => none'],
    ['historical charges','charged := before.charged + executed.run.chargedCount',
      'charged := executed.run.chargedCount'],
    ['historical removals','removed := before.removed + executed.run.removedCount',
      'removed := executed.run.removedCount'],
    ['actual preceding carrier','WireDescendantProperSupport.compile before.current records raw.stages with',
      'WireDescendantProperSupport.compile source records raw.stages with'],
    ['full available values','(available : before.pending field = none)',
      '(available : True)'],
  ]);
});

test('M269 source: the complete dependency graph includes intrinsic creation references',async()=>{
  await rejectMutations0('ProgramInput',[
    ['intrinsic references','event.predecessorIDs ++ event.action.creationDependencies','event.predecessorIDs'],
    ['R6 creation identity','| .primitive (.cancelR6 identity) => [identity]',
      '| .primitive (.cancelR6 identity) => []'],
    ['R7 creation identity','| .primitive (.realizeR7 identity _) => [identity]',
      '| .primitive (.realizeR7 identity _) => []'],
    ['R8 creation identity','| .primitive (.restoreR8 identity) => [identity]',
      '| .primitive (.restoreR8 identity) => []'],
    ['unique event IDs','if unique : uniqueIDs raw = true then','if unique : True then'],
    ['complete references','if complete : completeReferences raw = true then',
      'if complete : True then'],
    ['complete graph','PNP.DependencyScheduler.compile (eventGraph raw)',
      'PNP.DependencyScheduler.compile (eventGraph (raw.take 1))'],
  ]);
});

test('M269 source: complete execution begins internally and ends with genuine closure',async()=>{
  await rejectMutations0('Program',[
    ['entire computed order','(State.initial source) (ordered.order.map raw.get)',
      '(State.initial source) ((ordered.order.map raw.get).take 1)'],
    ['computed final closure','if closed : result.1.isClosed = true then','if closed : True then'],
    ['no supplied initial state','def compile (source : WireCarrier inputs outputs fields) (raw : List RawEvent)',
      'def compile (source : WireCarrier inputs outputs fields) (raw : List RawEvent) (supplied : State source)'],
    ['same snapshot lifecycle','after.pending field = some snapshot ∨ trace.Discharged field snapshot',
      'True'],
    ['closure derived from execution','program.execution.creationsClosed_of_finalClosed program.closed',
      'by assumption'],
    ['all full fields','(field : Fin fields) : program.result.fieldValue valuation field',
      '(field : Fin 1) : program.result.fieldValue valuation field'],
  ]);
});

test('M269 source: local ownership follows actual allocations and physical normalization',async()=>{
  await rejectMutations0('SupportOwnership',[
    ['nested allocation identity','| .allocated stage event localGate => .allocated stage event localGate',
      '| .allocated stage event localGate => .allocated 0 event localGate'],
    ['original physical coordinate','terminalExtractionOrigin before.current.exposed.candidate records gate',
      'suppliedOrigin gate'],
  ]);
  await rejectMutations0('PrimitiveOwnership',[
    ['actual normalization','PhysicalOwnership.normalize before.current.exposed ledger','ledger'],
    ['event allocation identity','| .allocated identity localGate => .allocated 0 identity localGate',
      '| .allocated identity localGate => .allocated 0 0 localGate'],
  ]);
});

test('M269 source: whole-program ownership preserves history and computed namespaces',async()=>{
  await rejectMutations0('ProgramOwnership',[
    ['computed outer namespace','| .allocated stage event localGate => .allocated position stage event localGate',
      '| .allocated stage event localGate => .allocated 0 stage event localGate'],
    ['complete history fold','tail.carryOwnership (position + 1) (ledger.advance position step)',
      'ledger.advance position step'],
    ['past charges persist','ledger.charged ++ step.localLedger.charged.map (ledger.liftOrigin position)',
      'step.localLedger.charged.map (ledger.liftOrigin position)'],
    ['past removals persist','ledger.removed ++ step.localLedger.removed.map (ledger.liftOrigin position)',
      'step.localLedger.removed.map (ledger.liftOrigin position)'],
    ['actual nested ledger','| .support _ _ _ _ receipt => receipt.ownership',
      '| .support _ _ _ _ receipt => suppliedOwnership'],
  ]);
});

test('M271 source: structural actions use actual current decoding and ownership',async()=>{
  await rejectMutations0('ProgramInput',[
    ['raw swaps only','| structural (swaps : List (Nat × Nat))',
      '| structural (swaps : List (Nat × Nat)) (suppliedCorrectness : Prop)'],
  ]);
  await rejectMutations0('Program',[
    ['decode every actual swap','match WireStructuralState.execute before raw with',
      'match WireStructuralState.execute before (raw.take 1) with'],
    ['reject invalid coordinates','| some receipt => some ⟨receipt.next, .structural before event raw kind receipt⟩',
      '| some receipt => suppliedSuccess'],
    ['no invented structural cost','| .structural _ _ _ _ _ => 0',
      '| .structural _ _ _ _ _ => 1'],
    ['no fabricated snapshot event','| .structural _ _ _ _ _ => none',
      '| .structural _ _ _ _ _ => suppliedCreation'],
  ]);
  await rejectMutations0('ProgramOwnership',[
    ['actual structural owner map','| .structural _ _ _ _ receipt => receipt.ownership',
      '| .structural _ _ _ _ receipt => suppliedOwnership'],
  ]);
});

test('M269 source: final literal embedding derives wiring and retains physical ownership',async()=>{
  await rejectMutations0('ProperSupport',[
    ['complete program','WireOpenProgram.compile (localSource carrier records) raw with',
      'WireOpenProgram.compile (localSource carrier records) (raw.take 1) with'],
    ['actual full interface','(fieldCandidate program.result) with',
      '(fieldCandidate (localSource carrier records)) with'],
    ['derived compiler','program_compiles carrier records program','suppliedCompiler'],
    ['actual observations','exact (WireHistoryArbitrarySupport.fieldCandidate_semantics program.result valuation field).trans',
      'exact suppliedSemantics'],
  ]);
  await rejectMutations0('ProperOwnership',[
    ['literal inverse position','executed.compiled.physicalOrigin position','suppliedPosition position'],
    ['historical allocated charge','executed.program.ownership.charged.map (ownershipLift carrier records)','[]'],
    ['historical physical removal','executed.program.ownership.removed.map (ownershipLift carrier records)','[]'],
  ]);
});

test('M269 source: the raw certificate has no witness and rejects incomplete or false gains',async()=>{
  await rejectMutations0('Certificate',[
    ['no supplied correctness','events : List WireOpenProgram.RawEvent',
      'events : List WireOpenProgram.RawEvent\n  suppliedCorrectness : Prop'],
    ['no supplied ownership','events : List WireOpenProgram.RawEvent',
      'events : List WireOpenProgram.RawEvent\n  suppliedOwners : List Nat'],
    ['every raw coordinate','(outputs + fields) 0 raw.records with',
      '(outputs + fields) 0 (raw.records.take 1) with'],
    ['complete mixed program','WireOpenProperSupport.compile carrier records raw.events with',
      'WireOpenProperSupport.compile carrier records (raw.events.take 1) with'],
    ['proper physical support','if proper : 0 < (ArbitrarySupportSplice.exterior records).length then',
      'if proper : 0 ≤ (ArbitrarySupportSplice.exterior records).length then'],
    ['strict final saving','if smaller : executed.program.result.implementation.gateCount <',
      'if smaller : executed.program.result.implementation.gateCount ≤'],
    ['all fields preserved','∀ valuation field, checked.result.fieldValue valuation field =',
      '∀ valuation field, carrier.fieldValue valuation field ='],
    ['failed complete execution','checked.executed.programAt.symm.trans rejected','suppliedAcceptance'],
    ['derived outer compilation','WireOpenProperSupport.compile_complete carrier records raw.events program programAt',
      'suppliedSpliceReceipt'],
    ['historical physical partition','programOriginals carrier.implementation.gateCount ++ checked.ownership.charged',
      'programOriginals carrier.implementation.gateCount'],
  ]);
});

test('M269 preflight: explicit root, exact audit and all regression families agree',async()=>{
  const root=await text0('lean/PNP.lean');
  const audit=await text0('lean-audit/PNPOpenObligationProgramAxiomAudit.lean');
  const printed=source=>[...source.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]);
  assert.match(audit,/^import PNP$/mu);
  assert.deepEqual(printed(audit),REGRESSIONS.flatMap(row=>row.names));
  for(const spec of SPECS)
    assert.ok(root.split('\n').includes('import PNP.NANDWireOpen'+spec.part),spec.path);
  for(const row of REGRESSIONS) {
    const fixture=await text0(row.path);
    assert.deepEqual(printed(fixture),row.printedNames,row.part);
    assert.ok(fixture.startsWith('import PNP.NANDWireOpen'+row.part+'\n'));
    assert.doesNotMatch(fixture,/\b(?:sorry|admit|native_decide|unsafe)\b|#eval!/u);
  }
});
