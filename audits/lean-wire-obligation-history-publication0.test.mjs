import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';
import {
  hasLeanAssumptionDeclaration0, hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Independently reviewed source/type boundary and compiled theorem fingerprints.
// Do not regenerate these expectations merely to accept an unexplained change.
const CONTRACTS = {
  "FiniteDependencyScheduler": [
    35,
    "32f3a9a1303f5357100a876fafe0904ae324c178a2e6efbdf152ca4ca08be2b2"
  ],
  "NANDWireObligationHistoryState": [
    37,
    "6608e10b277c19ae0d45b3e885a7addfaeeacdaa86e180763c3d01e220d484b3"
  ],
  "NANDWireObligationHistory": [
    26,
    "75696e306b8fa1c0cb51a5ac413b6561240ce1c9d03d9f2d7319bb9bdebe00f5"
  ],
  "NANDWireObligationHistoryExecution": [
    56,
    "fb923a33a9ae016f35ce1595f18cdb94d0974522a528df65c8ed36a33def6b40"
  ]
};
const REVIEWED = [
  ["PNP.DependencyScheduler.ReadyStep.remaining_lt","44bff5d1be6c8074e99def406e7faecb346441bedc0ac3b4420e4927f5e1373f","PNP.FiniteDependencyScheduler",["Quot.sound","propext"]],
  ["PNP.DependencyScheduler.Schedule.at_injective","7325e0440ba228aecb1f3ca0bfd787ab82c93ed61aeb267db5b806a17845d360","PNP.FiniteDependencyScheduler",[]],
  ["PNP.DependencyScheduler.Schedule.order_complete","c0bc5ea38e5bef5a3db8cfb385afd687f05970189a64219461a71a0c0cdc8e98","PNP.FiniteDependencyScheduler",["Quot.sound","propext"]],
  ["PNP.DependencyScheduler.Schedule.order_length","ccc28a25035f30ad731ce79d62437d84f497ca2c972ac0ef820cdfe0c6c78e83","PNP.FiniteDependencyScheduler",["propext"]],
  ["PNP.DependencyScheduler.Schedule.order_nodup","6fcec66236c25dbcf4e6eb74c07a06f8ffb1408eca6aaab395877ef05942d704","PNP.FiniteDependencyScheduler",["Quot.sound","propext"]],
  ["PNP.DependencyScheduler.Schedule.wellFounded","ba098126abab3930ba38e3eba6155f6aec86bf83d17d1e9b8e7a7cb9ef872882","PNP.FiniteDependencyScheduler",[]],
  ["PNP.DependencyScheduler.Stop.complete_of_wellFounded","08aae73b031ced880c4c698523e670264020780bb2299593f48647c49c8a73dc","PNP.FiniteDependencyScheduler",[]],
  ["PNP.DependencyScheduler.Stop.unresolved_predecessor","3dc12cd45be6bcb7141fb81a8f29da69532c3374d724539d5e61f78c209193ac","PNP.FiniteDependencyScheduler",[]],
  ["PNP.DependencyScheduler.compile_failure_iff","d49913a5214be6296ea356ed69f4002bbf3adca2218ed7a66f3e35da36f5cf6e","PNP.FiniteDependencyScheduler",["Quot.sound","propext"]],
  ["PNP.DependencyScheduler.compile_success_iff","ff4041ae74888da57f525b104b237572ed7922572b4619e38611029541d78b8e","PNP.FiniteDependencyScheduler",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.cancel_full_value","f39bb7ff18787f0445bbbddb90f22badc6cc0c720066e449ab0256e4bcbf73f4","PNP.NANDWireObligationHistoryState",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.cancel_gateCount","c6b668b242c280f4bc4e947acf75953e8b3d486f1ffa620a3357de1e42466dec","PNP.NANDWireObligationHistoryState",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.closed_field","aad78fb5c71f29dcc02113ec8f755d63ca8a3a2d475a3eda1f28ac90c6d3a1b2","PNP.NANDWireObligationHistoryState",[]],
  ["PNP.DirectWire.WireObligationHistory.State.create_gateCount","c5055ea4079398b0c5de5ba33fead7a9e45e2ffeb9c6b8bed34bd3c42d39cca4","PNP.NANDWireObligationHistoryState",["propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.create_source_snapshot","5e6a73008b9ba035838fc473c3ce1d8aac10e09a8a343cdb47aeeba1160583ea","PNP.NANDWireObligationHistoryState",["propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.currentAgreement","13ccc70890d2b8883766af4ec127af0c5db4d32c4f08c14df0a35b89a8338770","PNP.NANDWireObligationHistoryState",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.normalize_gate_balance","40935311cd19f706866b06b3b69c7931faead7274c31c7a9c0257f704b3a75ac","PNP.NANDWireObligationHistoryState",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.restore_full_value","dad270a9a1c3a769c62fca96c301be597773a74ece28bf44218ed6ddec8b5ac2","PNP.NANDWireObligationHistoryState",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.restore_gate_charge","6bb4d07dacd7838eabe2be506c785034ae0f46fb4e02fd85e72037ab5a7845bc","PNP.NANDWireObligationHistoryState",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.OrderedEvents.identities_nodup","ac8b9a9e2dfa8c944d30f4662958a5d7013379563d60c29150c23bf23dd99d46","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.OrderedEvents.order_complete","441646f4a5b2cb4a59e2ccfc6c8da1304a4ac9a12168930258a8dbf310937d94","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.OrderedEvents.order_length","20d3aff2d74b639edf50bd457633a18516b53a83e7649fb05cdf712d4ee4d7d7","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.OrderedEvents.order_nodup","2abfa0b890cbe1d904f1f8d6fc4896e76d8b14411f872fd45cb3b57b23e6f9fc","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.completeReferences_iff","355c32c56adc705ed0a0190ec224cca20c12a519c46ad7e13432214a0eaa2791","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.graph_dependency_iff","89f258096645cbd1c3edddcd44168ac82c80ee6061cdf7fa65a21071d2f13153","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.orderEvents_failure_iff","1e6aee6d2dcd4caeaed20485b311134540d383f0ff27836ad981c2c1e32de043","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.orderEvents_success_iff","ae1c23179eb625d7939d2c162f30ba70de98db04c30dc8e7f163195eddba6c12","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.uniqueIDs_iff","71bcbb813a106280cbc23056655b1e00d003abe9546142102a9252995d14ce06","PNP.NANDWireObligationHistory",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.creation_lifecycle","931d176535e4d513f8d0c55154d78e8ceb5046c4f00de10429bcaba5e91bbc66","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.dependency_before","eb9fd5eeb6da03880e4e567c1150d9f788db315013c32ec064dc78c0e551010d","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.executed_count","3cd573f4f6711d7024502c0f32d4e095b2d72c472a2683dd98b6dbde45fcb37a","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.executed_identities_nodup","c45b5bc13d7b34725e10435625feec02f58632c53a3de2870daa4b7e3b5a1707","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.full_field","c693beecbd081a97a4cbb69a8d352963830e1ef59577d90930adbc208a3f111f","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.full_output","b424d42f293c35731c15c87699685a7276d36f6535dc9df10d94038525f92c63","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.ClosedHistory.gate_balance","1f6a44c3ae70e9bd68aa2f4c27ee53ca15d367bf7537504601368e758bc05207","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Execution.creationsClosed_of_finalClosed","2cc26c978ca29feaab7f93495679a526a087d81e45d41e79b747581f3c2affb9","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Execution.pending_persists_or_discharged","d6e413063b471ed85b88a8511c3e00cb1b8fbf74c8342ab840a87b0ef833cee2","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Execution.record_identities","99998dc3a2db9727261c6aaa9f719dd7e2e7bc1f07d0b4ed2ada9ceb24736ac5","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Execution.total_charge","7f1fa056790d301cbe44e1ff146522fe5a6de86a0b4f6f6ce8973ee63a100df1","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Execution.total_removed","f904a4305079095ec645306a1d05def1959dce27fb56cbe806f3869f967d4230","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.State.isClosed_sound","1e28a1969b79445ff35e88b8ba4bfbd84dcbf8ab4a5c62dccafa824dd5cd28fa","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Transition.charged_eq","e43b203250254c6888614c96da96a1969c48c462fcf2b82847f344974b2b6b83","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Transition.created_pending","4946de5b4d016cfce8082bf7d22630cb7e7b37867fdc9b668d6213d1e3f3d824","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Transition.dischargeRecord_binding","140da6c4f11123758ced882d33305ac808236012f726b61dbee4f11a3298b351","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Transition.pending_persists_or_discharged","6b9c4958f407e0ffac3ca7d15254ed0070e775cb4b2ab2e2483e7b6a2c8ee192","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]],
  ["PNP.DirectWire.WireObligationHistory.Transition.removed_eq","9ec3017bd5fed872a00ee12b52b2e9b3a414623683270daed4fca66aabd839b4","PNP.NANDWireObligationHistoryExecution",["Quot.sound","propext"]]
];
const NAMES = REVIEWED.map(row => row[0]);
const STATUS_FIELDS = {
  "leanWireObligationHistoryFormalized": true,
  "leanWireObligationHistoryAxiomAuditPassed": true,
  "leanWireObligationHistoryAuditedDeclarationCount": 46,
  "leanWireObligationHistoryDependencySchedulerSuccessIffTheorem": "PNP.DependencyScheduler.compile_success_iff",
  "leanWireObligationHistoryDependencySchedulerFailureIffTheorem": "PNP.DependencyScheduler.compile_failure_iff",
  "leanWireObligationHistoryRawOrderSuccessIffTheorem": "PNP.DirectWire.WireObligationHistory.orderEvents_success_iff",
  "leanWireObligationHistoryRawOrderFailureIffTheorem": "PNP.DirectWire.WireObligationHistory.orderEvents_failure_iff",
  "leanWireObligationHistoryCreationSourceSnapshotTheorem": "PNP.DirectWire.WireObligationHistory.State.create_source_snapshot",
  "leanWireObligationHistoryActualRestorationChargeTheorem": "PNP.DirectWire.WireObligationHistory.State.restore_gate_charge",
  "leanWireObligationHistoryNormalizationBalanceTheorem": "PNP.DirectWire.WireObligationHistory.State.normalize_gate_balance",
  "leanWireObligationHistoryMatchedDischargeBindingTheorem": "PNP.DirectWire.WireObligationHistory.Transition.dischargeRecord_binding",
  "leanWireObligationHistoryCreationLifecycleTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.creation_lifecycle",
  "leanWireObligationHistoryDependencyOrderTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.dependency_before",
  "leanWireObligationHistoryExactlyOnceCountTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.executed_count",
  "leanWireObligationHistoryUniqueEventIdentitiesTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.executed_identities_nodup",
  "leanWireObligationHistoryFullFieldTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.full_field",
  "leanWireObligationHistoryOrdinaryOutputTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.full_output",
  "leanWireObligationHistoryPhysicalGateBalanceTheorem": "PNP.DirectWire.WireObligationHistory.ClosedHistory.gate_balance",
  "leanWireObligationHistoryArbitraryFiniteEventGraphsCovered": true,
  "leanWireObligationHistoryDuplicateAndMissingReferencesRejected": true,
  "leanWireObligationHistoryIntrinsicCreationDependenciesComputed": true,
  "leanWireObligationHistoryCyclicGraphsRejected": true,
  "leanWireObligationHistoryActualEvolvingCarrierExecuted": true,
  "leanWireObligationHistorySourceBoundCreationAndDischargeRecords": true,
  "leanWireObligationHistoryCreationClosesStrictlyLater": true,
  "leanWireObligationHistoryPhysicalNormalizationPreservesOpenSnapshots": true,
  "leanWireObligationHistoryFullReadsRequireClosedField": true,
  "leanWireObligationHistoryFinalOpenObligationsRejected": true,
  "leanWireObligationHistoryComputedSourceIdentityR6": true,
  "leanWireObligationHistoryActualCapturedMaterializerR8": true,
  "leanWireObligationHistoryCompleteAppendedMaterializersCharged": true,
  "leanWireObligationHistoryNoFreeCrossSnapshotSharing": true,
  "leanWireObligationHistoryAllValuationFullOutputAndFieldPreservation": true,
  "leanWireObligationHistoryCallerSuppliedOrderRequired": false,
  "leanWireObligationHistoryCallerSuppliedRankRequired": false,
  "leanWireObligationHistoryCallerSuppliedStateRequired": false,
  "leanWireObligationHistoryCallerSuppliedFullWitnessRequired": false,
  "leanWireObligationHistoryCallerSuppliedChargesRequired": false,
  "leanWireObligationHistoryAcyclicityImpliesValidLifecycle": false,
  "leanWireObligationHistoryConfluenceOfUnderspecifiedEventGraphsProved": false,
  "leanWireObligationHistoryQuotientAgreementClosesObligation": false,
  "leanWireObligationHistoryR5ProjectionRemovesPhysicalGates": false,
  "leanWireObligationHistoryFullR7SemanticsProved": false,
  "leanWireObligationHistoryAllManuscriptRewriteFamiliesProved": false,
  "leanWireObligationHistoryAllManuscriptNormalizationFamiliesProved": false,
  "leanWireObligationHistoryArbitraryObserverOrProfileTransportProved": false,
  "leanWireObligationHistoryMatchedKappaPullExpandProved": false,
  "leanWireObligationHistoryFullManuscriptCarrierProved": false,
  "leanWireObligationHistoryCompletePackageEProved": false,
  "leanWireObligationHistoryGlobalRouteCoverageProved": false,
  "leanWireObligationHistoryUnconditionalSaturatePositiveProved": false,
  "leanWireObligationHistoryUnconditionalBCELReadyProved": false,
  "leanWireObligationHistoryUnconditionalZeroSlackProved": false,
  "leanWireObligationHistoryExactGeneralPCCMinProved": false,
  "leanWireObligationHistoryPolynomialRuntimeProved": false,
  "leanWireObligationHistoryRuntimeExecutionIsProofAuthority": false,
  "leanWireObligationHistoryScope": "arbitrary-finite-raw-event-graphs-computed-order-actual-evolving-carriers-source-bound-R5-R6-R8-full-read-records-strictly-later-matched-discharge-all-full-outputs-and-fields-exact-charged-materializer-and-normalization-gate-balance-no-complete-package-E-global-route-or-polynomial-runtime"
};
const COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-15-263';
const MILESTONE = 'wire-obligation-history';
const SCOPE = "For arbitrary finite input, output, computational-field and event dimensions, M263 computes a complete dependency order from raw event identities, explicit predecessors and intrinsic creation references. Duplicate identities, missing references and cyclic graphs reject. The scheduler succeeds exactly when the actual finite dependency relation is well-founded. The history constructor executes one evolving physical carrier from the original source, without caller-supplied order, rank, state, full-value witness or charge data. R5 captures the actual pre-drop carrier; physical normalization preserves open snapshots; source-identity R6 computes a visible representative; R8 appends and charges the complete materializer from the matching creation snapshot. Full reads require an available field, and final open obligations reject. Every successful history executes every event exactly once in dependency order, every creation discharges strictly later with its full source binding, and every ordinary output and computational field retains its original value for every valuation. Final physical gates plus actual normalization removals equal initial physical gates plus all appended materializer charges.";
const NON_CLAIM = "This is the computational R5/R6/R8 history component, not the complete manuscript obligation calculus or Package E. Acyclicity guarantees a computed order, not a valid lifecycle or confluence of underspecified event graphs. R5 projection alone removes no physical gates; repeated restorations receive no free cross-snapshot sharing, and restoration can increase physical size. Quotient-only agreement cannot discharge a full obligation. Full R7 and other R1-R9 semantics, all N1-N10 transports, arbitrary observers and profile histories, noncomputational carrier records, matched-kappa Pull/Expand, complete Package E, global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-input-size polynomial runtime, output and certificate bounds remain open. Runtime fixtures are regression evidence, not proof authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.";
const TEST_FILES = [
  "audits/lean-finite-dependency-scheduler0.test.mjs",
  "audits/lean-wire-obligation-history-state0.test.mjs",
  "audits/lean-wire-obligation-history0.test.mjs",
  "audits/lean-wire-obligation-history-execution0.test.mjs",
  "audits/lean-wire-obligation-history-publication0.test.mjs"
];
const COMMAND = 'node --test ' + TEST_FILES.join(' ');
const AUDIT = 'lean-audit/PNPWireObligationHistoryAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPWireObligationHistory.lean';
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();

function contract0(source) {
  const clean = stripLeanCommentsAndStrings0(source);
  const starts = [...clean.matchAll(/^[ \t]*(?:(?:private|protected|noncomputable)[ \t]+)*(?:(def|theorem|inductive|structure|abbrev)[ \t]+([^\s({:]+)|(variable|namespace|section|end|import|open|set_option|attribute|include|omit|universe|export|initialize)\b)/gmu)];
  const blocks = starts.map((match, index) => {
    const text = clean.slice(match.index, starts[index + 1]?.index ?? clean.length)
      .replace(/\s+/gu, ' ').trim();
    return match[1] === 'theorem' ? text.slice(0, text.indexOf(' := ')) : text;
  });
  return [blocks.length, createHash('sha256').update(blocks.join('\n') + '\n').digest('hex')];
}

function inspect0(source, module) {
  const failures = [];
  const clean = stripLeanCommentsAndStrings0(source);
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-form');
  if (/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|implemented_by|csimp|partial_fixpoint)\b|#/u.test(clean))
    failures.push('unchecked-authority');
  if (JSON.stringify(contract0(source)) !== JSON.stringify(CONTRACTS[module]))
    failures.push('closed-source-and-type-contract');
  return failures;
}

test('M263 preflight: every general source interface and physical definition matches review', async () => {
  for (const module of Object.keys(CONTRACTS))
    assert.deepEqual(inspect0(await text0('lean/PNP/' + module + '.lean'), module), [], module);
});

test('M263 preflight: source review rejects supplied premises and changed physical construction', async () => {
  for (const [module, before, after] of [
    ['FiniteDependencyScheduler', 'structure Graph (nodes : Nat)', 'structure Graph (nodes : Nat) (supplied : True)'],
    ['NANDWireObligationHistoryState', 'carrier := state.current', 'carrier := source'],
    ['NANDWireObligationHistory', 'predecessorIDs : List Nat', 'predecessorIDs : List Nat\n  supplied : True'],
    ['NANDWireObligationHistoryExecution', 'theorem full_field (history : ClosedHistory source raw)',
      'theorem full_field (history : ClosedHistory source raw) (supplied : True)'],
    ['NANDWireObligationHistoryExecution', 'step.created = some ⟨field, snapshot⟩ → tail.Discharged field snapshot',
      'step.created = some ⟨field, snapshot⟩ → True'],
  ]) {
    const source = await text0('lean/PNP/' + module + '.lean');
    assert.ok(source.includes(before), module);
    assert.ok(inspect0(source.replaceAll(before, after), module)
      .includes('closed-source-and-type-contract'), module);
  }
});

test('M263 preflight: every source rejects hidden authority and unchecked execution', async () => {
  for (const module of Object.keys(CONTRACTS)) {
    const source = await text0('lean/PNP/' + module + '.lean');
    for (const declaration of ['axiom hidden : False', 'private axiom hidden : False', 'opaque hidden : False'])
      assert.ok(inspect0(source + '\n' + declaration + '\n', module).includes('assumption'));
    for (const declaration of ['attribute [implemented_by hidden] compileHistory',
      'unsafe def hidden : Bool := true', '#eval true'])
      assert.ok(inspect0(source + '\n' + declaration + '\n', module).includes('unchecked-authority'));
  }
});

test('M263 preflight: explicit root, audit, inventory and regression boundaries agree', async () => {
  const [root, audit, inventory, regression] = await Promise.all([
    text0('lean/PNP.lean'), text0(AUDIT), text0('lean-audit/PNPTheoremInventory.lean'), text0(REGRESSION),
  ]);
  assert.equal(NAMES.length, 46);
  assert.equal(new Set(NAMES).size, 46);
  for (const module of Object.keys(CONTRACTS))
    assert.equal(root.split('import PNP.' + module + '\n').length - 1, 1, module);
  for (const source of [audit, regression])
    assert.deepEqual([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]), ['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match => match[1]), NAMES);
  for (const name of NAMES) {
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(value => value === name).length, 1, name);
    assert.equal(inventory.split(String.fromCharCode(96) + name + ',').length - 1, 1, name);
  }
  for (const fixture of ['fanIn', 'stuckAfterProgress', 'selfLoop', 'missingExplicit',
    'missingIntrinsic', 'duplicateIdentity', 'restoreAfterNormalize', 'repeatedField',
    'rebasedCancel', 'withOutput', 'emptyCarrier'])
    assert.ok(regression.includes(fixture), fixture);
  assert.ok(regression.includes('stale-identity or incompletely discharged lifecycle accepted'));
  assert.ok(regression.includes('regression evidence, never theorem authority'));
});

test('M263 preflight: package, verifier and durable CI consume the same reviewed boundary', async () => {
  const [pkg, surface, verifier, workflow] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m263'], COMMAND);
  assert.ok(surface.includes("'audit:m263': '" + COMMAND + "'"));
  for (const file of TEST_FILES) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes(COMMAND));
  for (const path of [AUDIT, REGRESSION])
    assert.ok(workflow.includes('lake env lean -DwarningAsError=true ' + path), path);
  for (const name of NAMES)
    assert.equal(workflow.split('"' + name + '"').length - 1, 1, name);
});

let sourcesPromise;
function sources0() {
  sourcesPromise ??= Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'), text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([status, inventory, progress, map]) => ({
    status:JSON.parse(status), inventory:JSON.parse(inventory),
    inventoryBytes:Buffer.from(inventory), progress:JSON.parse(progress), map:JSON.parse(map),
  }));
  return sourcesPromise;
}

test('M263 release: compiled types, axioms and conservative publication claims match review', async () => {
  const {status, inventory, inventoryBytes, map} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes, status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === MILESTONE);
  assert.equal(row?.earned, true);
  assert.equal(row.classification, 'formalized-foundation-only');
  assert.deepEqual(row.requiredTheorems, NAMES);
  assert.equal(row.scope, SCOPE);
  assert.equal(row.nonClaim, NON_CLAIM);
  for (const [name, typeHash, module, axioms] of REVIEWED) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, module, name);
      assert.deepEqual(declaration.axioms, axioms, name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), typeHash, name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], typeHash, name);
  }
  for (const [field, value] of Object.entries(STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
});

test('M263 release: every type pin rejects weakened or supplied statements', async () => {
  const {status, inventory, map} = await sources0();
  const mutatedTypes = new Map();
  for (const [name, expected] of REVIEWED) {
    const current = inventory.milestoneCandidates.find(row => row.name === name).kernelType;
    const alternatives = ['Lean.Expr.const ' + String.fromCharCode(96) + 'True []',
      'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + current + ') (' + current
        + ') (Lean.BinderInfo.default)'];
    for (const changed of alternatives)
      assert.notEqual(MilestoneTheoremKernelTypeSha2560(name, changed), expected, name);
    mutatedTypes.set(name, alternatives);
  }
  // Exercise the common derivation gate across all four modules, without
  // serializing the entire unchanged inventory for every identical rejection.
  const representatives = new Map(REVIEWED.map(row => [row[2], row[0]]));
  for (const name of representatives.values()) for (const changed of mutatedTypes.get(name)) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:changed} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M263 release: publication rejects hidden authority, missing evidence and widened claims', async () => {
  const {status, inventory, inventoryBytes, map} = await sources0();
  const name = 'PNP.DirectWire.WireObligationHistory.ClosedHistory.creation_lifecycle';
  const addAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const mutation = {...inventory, declarations:inventory.declarations.map(addAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(addAuthority)};
  const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), status.leanSourceClosureSha256);
  assert.equal(result.milestones.find(row => row.id === MILESTONE).earned, false);
  assert.equal(result.gate.passed, false);
  const missing = {...inventory, milestoneCandidates:inventory.milestoneCandidates.filter(row => row.name !== name)};
  assert.throws(() => DeriveFormalPublication0(missing, map, canonical0(missing), status.leanSourceClosureSha256),
    /reviewed milestone theorem candidate inventory mismatch/u);
  for (const field of ['scope', 'nonClaim']) {
    const widened = {...map, milestones:map.milestones.map(row => row.id === MILESTONE
      ? {...row, [field]:'Acyclic raw data proves complete Package E, free restoration and polynomial ZeroSlack.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, status.leanSourceClosureSha256),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, status.leanSourceClosureSha256),
    /map drifted from the reviewed specification/u);
});

test('M263 release: status rejects altered identity, lifecycle, runtime and scope claims', async () => {
  const {status} = await sources0();
  for (const field of ['leanWireObligationHistoryFullFieldTheorem',
    'leanWireObligationHistoryAuditedDeclarationCount',
    'leanWireObligationHistoryAcyclicityImpliesValidLifecycle',
    'leanWireObligationHistoryPolynomialRuntimeProved', 'leanWireObligationHistoryScope']) {
    const value = STATUS_FIELDS[field];
    const mutation = {...status, [field]:typeof value === 'boolean' ? !value
      : typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({
      writeOutput:false, statusOverride:mutation, siteOverride:mutation,
    });
    assert.equal(result.tag, 'reject', field);
    assert.equal(result.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('M263 release: history coverage earns no fixed checkpoint or global proof credit', async () => {
  const {status, inventory, progress} = await sources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const reviews = progress.history.filter(entry => entry.asOfCoordinate === COORDINATE);
  assert.equal(reviews.length, 1);
  const review = reviews[0];
  assert.equal(review.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.equal(review.globalGatesAvailable, 5);
  assert.ok(prose0(review.rationale).includes('No fixed load-bearing checkpoint changes state'));
  if (progress.asOfCoordinate !== COORDINATE) return;
  assert.deepEqual(review.formalArtefactCoverage, {
    earnedRows:status.formalPublicationMilestones.filter(row => row.earned).length,
    totalRows:status.formalPublicationMilestones.length,
  });
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.equal(progress.globalGates.length, 5);
  assert.ok(progress.globalGates.every(gate => gate.status === 'open'));
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(inventory.declarations.some(row => row.name === 'PNP.Main.p_eq_np'), false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.equal(progress.publicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {name:'PNP.Main.p_eq_np', present:false, built:false, axiomAuditPassed:false});
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M263 release: documentation retains exact history scope and deferred site publication', async () => {
  const {progress} = await sources0();
  const documentation = prose0(await text0('docs/lean_wire_obligation_history.md'));
  const plan = prose0(await text0('docs/plans/2026-09-15-dependency-ordered-wire-obligation-history.md'));
  assert.ok(documentation.includes(COORDINATE));
  for (const boundary of ['strictly later', 'actual pre-drop carrier', 'no free cross-snapshot sharing',
    'not semantic admissibility', 'not the complete Package E', 'No fixed weighted checkpoint',
    'Publication decision: defer PNPLabs'])
    assert.ok(documentation.includes(boundary), boundary);
  assert.ok(plan.includes('Publication decision: defer PNPLabs'));
  if (progress.asOfCoordinate !== COORDINATE) return;
  const p = progress.proofCompletion, a = progress.formalArtefactCoverage;
  const metrics = [
    'Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + p.percent + '%.',
    'Uncertainty range: ' + p.uncertaintyLowPercent + '% to ' + p.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length + ' of 5.',
  ];
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md', 'docs/lean_wire_obligation_history.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
