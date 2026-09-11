import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';
import {
  DeriveFormalPublication0, MilestoneTheoremKernelTypeSha2560,
  REQUIRED_MILESTONE_THEOREMS0, stableStringify0,
} from '../formal-publication0.mjs';
import { validateProofProgress0 } from '../pcc-proof-progress0.mjs';

const SOURCE = 'lean/PNP/ResidualTerminalGainProfileFirewall.lean';
const AUDIT = 'lean-audit/PNPResidualTerminalGainProfileFirewallAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPResidualTerminalGainProfileFirewall.lean';
const NAMES = [
  "firstTerminalGainProfileMismatch_eq_none_iff",
  "firstTerminalGainProfileMismatch_spec",
  "terminalFullProfileMinimum_eq_of_fullRealization",
  "classifyTerminalCandidateGainProfile_accepted_iff",
  "classifyTerminalCandidateGainProfile_noGain_iff",
  "classifyTerminalCandidateGainProfile_mismatch_iff",
  "TerminalCandidateFullProfileGain.fullSlack_gain"
];
const SIGNATURES = [
  "theorem firstTerminalGainProfileMismatch_eq_none_iff {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current replacement : Implementation inputs outputs) : firstTerminalGainProfileMismatch system current replacement = none ↔ ∀ coordinate, system.observe replacement coordinate = system.observe current coordinate",
  "theorem firstTerminalGainProfileMismatch_spec {inputs outputs profileWidth : Nat} (system : TerminalProfileSystem inputs outputs profileWidth) (current replacement : Implementation inputs outputs) (coordinate : Fin profileWidth) (foundAt : firstTerminalGainProfileMismatch system current replacement = some coordinate) : system.observe replacement coordinate ≠ system.observe current coordinate ∧ ∃ before after : List (Fin profileWidth), allFin profileWidth = before ++ coordinate :: after ∧ ∀ earlier, earlier ∈ before → system.observe replacement earlier = system.observe current earlier",
  "theorem terminalFullProfileMinimum_eq_of_fullRealization {inputs outputs profileWidth : Nat} {system : TerminalProfileSystem inputs outputs profileWidth} {current : Implementation inputs outputs} (full : TerminalFullCarrierRealization system current) : terminalFullProfileMinimum system full.realization.implementation = terminalFullProfileMinimum system current",
  "theorem classifyTerminalCandidateGainProfile_accepted_iff {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) : (classifyTerminalCandidateGainProfile candidate model).tag = .accepted ↔ ∃ replacement : Implementation inputs outputs, findTerminalCandidatePhysicalGain candidate model = some replacement ∧ ∀ coordinate, model.profileSystem.observe replacement coordinate = model.profileSystem.observe candidate.toImplementation coordinate",
  "theorem classifyTerminalCandidateGainProfile_noGain_iff {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) : (classifyTerminalCandidateGainProfile candidate model).tag = .noPhysicalGain ↔ findTerminalCandidatePhysicalGain candidate model = none",
  "theorem classifyTerminalCandidateGainProfile_mismatch_iff {inputs gates outputs profileWidth : Nat} (candidate : Candidate inputs gates outputs) (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate) : (classifyTerminalCandidateGainProfile candidate model).tag = .profileMismatch ↔ ∃ (replacement : Implementation inputs outputs) (coordinate : Fin profileWidth), findTerminalCandidatePhysicalGain candidate model = some replacement ∧ firstTerminalGainProfileMismatch model.profileSystem candidate.toImplementation replacement = some coordinate",
  "theorem TerminalCandidateFullProfileGain.fullSlack_gain {inputs gates outputs profileWidth : Nat} {candidate : Candidate inputs gates outputs} {model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate} (gain : TerminalCandidateFullProfileGain candidate model) : ∃ found : TerminalCandidateProperPositiveSupport candidate model, findTerminalCandidateProperPositiveSupport candidate model = some found ∧ (gain.implementation.gateCount - terminalFullProfileMinimum model.profileSystem gain.implementation) + terminalSupportLocalGain candidate (terminalCandidateSaturationSystem candidate model) found.seed = gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation ∧ gain.implementation.gateCount - terminalFullProfileMinimum model.profileSystem gain.implementation < gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation"
];
const PUBLIC_HEADS = [
  "firstTerminalGainProfileMismatch",
  "firstTerminalGainProfileMismatch_eq_none_iff",
  "firstTerminalGainProfileMismatch_spec",
  "terminalFullProfileMinimum_eq_of_fullRealization",
  "TerminalCandidateFullProfileGain",
  "TerminalCandidateFullProfileGain.fullRealization",
  "TerminalGainProfileTag",
  "TerminalCandidateGainProfileOutcome",
  "TerminalCandidateGainProfileOutcome.tag",
  "classifyTerminalCandidateGainProfile",
  "classifyTerminalCandidateGainProfile_accepted_iff",
  "classifyTerminalCandidateGainProfile_noGain_iff",
  "classifyTerminalCandidateGainProfile_mismatch_iff",
  "TerminalCandidateFullProfileGain.fullSlack_gain"
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const compact0 = value => stripLeanCommentsAndStrings0(value).replace(/\s+/gu, ' ').trim();
function block0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex(head => head.name === name);
  return index < 0 ? '' : source.slice(heads[index].index, heads[index + 1]?.index ?? source.length);
}
function declarationHeader0(source) {
  const clean = stripLeanCommentsAndStrings0(source);
  const openings = new Map([['(', ')'], ['[', ']'], ['{', '}'], ['⟨', '⟩']]);
  const closings = new Set(openings.values());
  const stack = [];
  for (let index = 0; index < clean.length; index += 1) {
    const char = clean[index];
    if (openings.has(char)) stack.push(openings.get(char));
    else if (closings.has(char)) {
      if (stack.pop() !== char) return '';
    } else if (char === ':' && clean[index + 1] === '=' && stack.length === 0
        && /^\s*by\b/u.test(clean.slice(index + 2))) {
      return compact0(clean.slice(0, index));
    }
  }
  return '';
}

function validateSource0(source) {
  const failures = [];
  const require0 = (condition, category) => { if (!condition) failures.push(category); };
  const clean = compact0(source);
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|suppliedSearch|suppliedProfileScan|callerCertificate)\b/u
    .test(clean), 'shortcut-or-certificate');
  require0(JSON.stringify([...source.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match => match[1]))
    === JSON.stringify(['PNP.ResidualTerminalPhysicalGain']), 'closed-imports');
  require0(JSON.stringify(explicitLeanDeclarationHeads0(source).map(head => head.name)) ===
    JSON.stringify(PUBLIC_HEADS), 'public-interface');
  for (const [index,name] of NAMES.entries())
    require0(declarationHeader0(block0(source,name)) === SIGNATURES[index], 'signature:' + name);
  const scan = compact0(block0(source,'firstTerminalGainProfileMismatch'));
  for (const token of [
    '(allFin profileWidth).find? fun coordinate =>',
    '!boolEqual (system.observe replacement coordinate) (system.observe current coordinate)',
  ]) require0(scan.includes(token), 'complete-coordinate-scan');
  require0(!scan.includes('projection'), 'full-mode-not-quotient');
  const classifier = compact0(block0(source,'classifyTerminalCandidateGainProfile'));
  for (const token of [
    'match foundAt : findTerminalCandidatePhysicalGain candidate model with',
    '| none => .noPhysicalGain foundAt',
    'match mismatchAt : firstTerminalGainProfileMismatch model.profileSystem candidate.toImplementation replacement with',
    '| some coordinate => .profileMismatch replacement foundAt coordinate mismatchAt',
    '| none => .accepted',
    'implementation := replacement',
    'physicalFoundAt := foundAt',
    '(firstTerminalGainProfileMismatch_eq_none_iff model.profileSystem candidate.toImplementation replacement).mp mismatchAt',
  ]) require0(classifier.includes(token), 'computed-production-classifier');
  require0(!/\b(?:equivalentBool|terminalQuotientProfileMatchBool|terminalFullProfileMinimumImplementation)\b/u
    .test(classifier), 'no-redundant-or-quotient-substitution');
  const full = compact0(block0(source,'TerminalCandidateFullProfileGain.fullRealization'));
  require0(full.includes('findTerminalCandidatePhysicalGain_sound candidate model gain.implementation gain.physicalFoundAt')
    && full.includes('profileEqual := gain.profileEqual'), 'actual-full-carrier-evidence');
  for (const dependency of [
    'terminalFullProfileMinimumRealization system current',
    'terminalFullProfileMinimumRealization system replacement',
    'terminalFullProfileMinimum_le toCurrent',
    'terminalFullProfileMinimum_le toReplacement',
    'terminalFullProfileMinimum_eq_of_fullRealization gain.fullRealization',
    'gainProfile_slack_balance',
  ]) require0(clean.includes(dependency), 'full-minimum-and-slack-transport');
  return [...new Set(failures)];
}

test('M239 declaration headers retain exact named arguments and computed let-bindings', () => {
  const head = 'theorem sample (model : M (width := width)) : let result := compute model result = model';
  assert.equal(declarationHeader0(head + ' := by exact proof'), head);
  assert.equal(declarationHeader0(head + ' :=\n by exact proof'), head);
  assert.equal(declarationHeader0('theorem broken (model : M := by exact proof'), '');
});

test('M239 computes full-profile acceptance and all seven universal interfaces', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE)), []);
});

test('M239 explicit root, axiom audit and reviewed-name producers agree', async () => {
  const [source,audit,inventorySource,root] = await Promise.all([
    text0(SOURCE),text0(AUDIT),text0('lean-audit/PNPTheoremInventory.lean'),text0('lean/PNP.lean'),
  ]);
  for (const name of NAMES) {
    assert.equal(explicitLeanDeclarationHeads0(source).filter(head => head.name === name).length,1);
    const fullName = 'PNP.DirectWire.' + name;
    assert.equal(REQUIRED_MILESTONE_THEOREMS0.filter(item => item === fullName).length,1);
    assert.equal(inventorySource.split(String.fromCharCode(96) + fullName + ',').length - 1,1);
  }
  assert.deepEqual([...audit.matchAll(/^import\s+(\S+)\s*$/gmu)].map(match=>match[1]),['PNP']);
  assert.deepEqual([...audit.matchAll(/^#print axioms\s+(\S+)\s*$/gmu)].map(match=>match[1]),
    NAMES.map(name=>'PNP.DirectWire.'+name));
  assert.match(root,/^import PNP\.ResidualTerminalGainProfileFirewall\s*$/mu);
});

test('M239 regression coverage keeps runtime assertions distinct from general proofs', async () => {
  const raw = await text0(REGRESSION), regression = compact0(raw);
  for (const name of NAMES) assert.ok(regression.includes(name + ' '),name);
  for (const token of [
    'searchCandidate : Candidate 1 2 1',
    'semanticModel.profileSystem.observe searchCandidate.toImplementation 0 = true',
    'semanticModel.profileSystem.observe wireCandidate.toImplementation 0 = false',
    'outcomeSummary (classifyTerminalCandidateGainProfile searchCandidate semanticModel)',
    'if actual == (TerminalGainProfileTag.accepted, some 1, none)',
    'IO.println', 'throw (IO.userError',
    '(.profileMismatch, some 1, some 1)',
    'mismatchModel.projection.keep 1 = false',
    '(zeroProfileModel searchCandidate)) = (.accepted, some 1, none)',
    '(zeroProfileModel zeroCandidate)) = (.noPhysicalGain, none, none)',
    'gain.fullRealization.obligationsDischarged discharged',
    '¬ openObligationSystem.ObligationsDischarged searchCandidate.toImplementation',
  ]) assert.ok(regression.includes(token),token);
  assert.equal([...raw.matchAll(/^#eval\b/gmu)].length,1);
  assert.ok(raw.includes('m239-semantic-observer-acceptance-execution-ok'));
  assert.doesNotMatch(regression,/\b(?:sorry|admit|native_decide|Classical)\b/u);
});

test('M239 rejects truncated scans, quotient shortcuts, supplied results and weakened descent', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    ['{inputs outputs profileWidth : Nat}','{inputs outputs profileWidth : Fin 2}','signature:'+NAMES[0]],
    ['firstTerminalGainProfileMismatch system current replacement = none ↔',
      'firstTerminalGainProfileMismatch system current replacement = none →','signature:'+NAMES[0]],
    ['∀ coordinate, system.observe replacement coordinate',
      '∀ coordinate, False → system.observe replacement coordinate','signature:'+NAMES[0]],
    ['allFin profileWidth = before ++ coordinate :: after ∧','True ∧','signature:'+NAMES[1]],
    ['terminalFullProfileMinimum system full.realization.implementation =',
      'referenceMinimum full.realization.implementation =','signature:'+NAMES[2]],
    ['findTerminalCandidatePhysicalGain candidate model = some replacement ∧',
      'True ∧','signature:'+NAMES[3]],
    ['findTerminalCandidatePhysicalGain candidate model = none := by',
      'findTerminalCandidatePhysicalGain candidate model = none ∨ True := by','signature:'+NAMES[4]],
    ['terminalFullProfileMinimum model.profileSystem gain.implementation <',
      'terminalFullProfileMinimum model.profileSystem gain.implementation ≤','signature:'+NAMES[6]],
    ['(allFin profileWidth).find? fun coordinate =>',
      '(allFin profileWidth).reverse.find? fun coordinate =>','complete-coordinate-scan'],
    ['match foundAt : findTerminalCandidatePhysicalGain candidate model with',
      'match foundAt : suppliedSearch candidate model with','computed-production-classifier'],
    ['match mismatchAt : firstTerminalGainProfileMismatch model.profileSystem',
      'match mismatchAt : suppliedProfileScan model.profileSystem','computed-production-classifier'],
    ['| none => .accepted','| none => .noPhysicalGain','computed-production-classifier'],
  ];
  for (const [before,after,category] of mutations) {
    assert.ok(source.includes(before),'mutation anchor: '+category);
    assert.ok(validateSource0(source.replaceAll(before,after)).includes(category),category);
  }
  assert.ok(validateSource0(source+'\naxiom unauthorized : False\n').includes('assumption'));
  assert.ok(validateSource0(source+'\nexample : True := by trivial\n').includes('unaudited-form'));
});

test('M239 durable workflow includes source contracts, strict root audit and guarded regressions', async () => {
  const [packageText,surface,verifier,workflow] = await Promise.all([
    text0('package.json'),text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditPath = 'audits/lean-residual-terminal-gain-profile-firewall0.test.mjs';
  assert.equal(JSON.parse(packageText).scripts['audit:m239'],'node --test '+auditPath);
  assert.ok(surface.includes("'audit:m239': 'node --test "+auditPath+"'"));
  assert.ok(verifier.includes(auditPath));
  assert.ok(workflow.includes('run: node --test '+auditPath));
  for (const path of [auditPath,'docs/lean_residual_terminal_gain_profile_firewall.md'])
    assert.equal(workflow.split("      - '"+path+"'").length-1,2);
  assert.ok(workflow.includes(AUDIT));
  assert.ok(workflow.includes(REGRESSION));
});

const M239_COORDINATE = 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-12-239';
const M239_MILESTONE = 'residual-terminal-gain-profile-firewall';
const M239_HASHES = Object.freeze({
  "PNP.DirectWire.firstTerminalGainProfileMismatch_eq_none_iff": "52aa9325d4a4b8f913638324e694e3d80d7640a630e29e2000b040a28d4dfcb8",
  "PNP.DirectWire.firstTerminalGainProfileMismatch_spec": "0296facc7457cb22362c0ba0417f1d9db05f472c05a7a80785270f1d0778f7a6",
  "PNP.DirectWire.terminalFullProfileMinimum_eq_of_fullRealization": "e86e3fcdfbc81b6f1a6d14d631dae151b60d34950ac04f4a0b71b5c1c76764f9",
  "PNP.DirectWire.classifyTerminalCandidateGainProfile_accepted_iff": "5271b9a9fdc0a1e07d5fe34f74d101a6ebd23ca15f7e21cc9779020761caeefa",
  "PNP.DirectWire.classifyTerminalCandidateGainProfile_noGain_iff": "1d9f1e3ab39bdfed1ef6692e9aef6042a169a2d74f5d5dae632d5ad5ab036e4a",
  "PNP.DirectWire.classifyTerminalCandidateGainProfile_mismatch_iff": "dfc8ea46b715beacd6afa5b64988becc4d208d8c19ef8191d592bd4f3dc34a20",
  "PNP.DirectWire.TerminalCandidateFullProfileGain.fullSlack_gain": "52a4af27b6946c6dee5fc9a0d00f3f5b1fc80a7a8a23c7153f0621953fff3ab9"
});
const M239_STATUS_FIELDS = Object.freeze({
  "leanResidualTerminalGainProfileFirewallFormalized": true,
  "leanResidualTerminalGainProfileFirewallAxiomAuditPassed": true,
  "leanResidualTerminalGainProfileFirewallAuditedDeclarationCount": 7,
  "leanResidualTerminalGainProfileFirewallProfileScanTheorem": "PNP.DirectWire.firstTerminalGainProfileMismatch_eq_none_iff",
  "leanResidualTerminalGainProfileFirewallFirstMismatchTheorem": "PNP.DirectWire.firstTerminalGainProfileMismatch_spec",
  "leanResidualTerminalGainProfileFirewallFullMinimumTheorem": "PNP.DirectWire.terminalFullProfileMinimum_eq_of_fullRealization",
  "leanResidualTerminalGainProfileFirewallAcceptanceTheorem": "PNP.DirectWire.classifyTerminalCandidateGainProfile_accepted_iff",
  "leanResidualTerminalGainProfileFirewallSearchFailureTheorem": "PNP.DirectWire.classifyTerminalCandidateGainProfile_noGain_iff",
  "leanResidualTerminalGainProfileFirewallRejectionTheorem": "PNP.DirectWire.classifyTerminalCandidateGainProfile_mismatch_iff",
  "leanResidualTerminalGainProfileFirewallFullSlackTheorem": "PNP.DirectWire.TerminalCandidateFullProfileGain.fullSlack_gain",
  "leanResidualTerminalGainProfileFirewallScope": "all-finite-candidates-supplied-executable-profile-models-computed-physical-gain-full-coordinate-first-mismatch-acceptance-and-exact-accepted-full-profile-slack-descent-only"
});
const M239_AXIOMS = Object.freeze({
  "PNP.DirectWire.firstTerminalGainProfileMismatch_eq_none_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.firstTerminalGainProfileMismatch_spec": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.terminalFullProfileMinimum_eq_of_fullRealization": [
    "propext"
  ],
  "PNP.DirectWire.classifyTerminalCandidateGainProfile_accepted_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.classifyTerminalCandidateGainProfile_noGain_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.classifyTerminalCandidateGainProfile_mismatch_iff": [
    "Quot.sound",
    "propext"
  ],
  "PNP.DirectWire.TerminalCandidateFullProfileGain.fullSlack_gain": [
    "Quot.sound",
    "propext"
  ]
});

let compiledSourcesPromise0;
function compiledSources0() {
  compiledSourcesPromise0 ??= Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
    text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('status/PROOF_PROGRESS.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(([status, inventory, progress, map]) => ({
    status:JSON.parse(status), inventory:JSON.parse(inventory),
    progress:JSON.parse(progress), map:JSON.parse(map), inventoryBytes:Buffer.from(inventory),
  }));
  return compiledSourcesPromise0;
}
const canonicalBytes0 = value => Buffer.from(stableStringify0(value) + '\n');
const prose0 = value => value.replace(/\s+/gu, ' ').trim();
function metrics0(progress) {
  const coverage = progress.formalArtefactCoverage, proof = progress.proofCompletion;
  return [
    'Formal artefact coverage: ' + coverage.earnedRows + ' of ' + coverage.totalRows
      + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + proof.percent + '%.',
    'Uncertainty range: ' + proof.uncertaintyLowPercent + '% to ' + proof.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length
      + ' of ' + progress.globalGates.length + '.',
  ];
}

test('M239 compiled full-profile acceptance, mismatch and slack interfaces match the exact reviewed types and status', async () => {
  const {status, inventory, inventoryBytes, map} = await compiledSources0();
  assert.ok(canonicalBytes0(inventory).equals(inventoryBytes));
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes,
    status.leanSourceClosureSha256);
  const row = publication.milestones.find(item => item.id === M239_MILESTONE);
  assert.equal(row?.earned, true);
  if (status.coordinate === M239_COORDINATE)
    assert.equal(map.coordinate, 'PNP-FORMAL-PUBLICATION-MAP-2026-09-12-239');
  assert.deepEqual(row.requiredTheorems, Object.keys(M239_HASHES));
  for (const name of row.requiredTheorems) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const declaration = collection.find(item => item.name === name);
      assert.equal(declaration?.kind, 'theorem', name);
      assert.equal(declaration.module, 'PNP.ResidualTerminalGainProfileFirewall', name);
      assert.deepEqual(declaration.axioms, M239_AXIOMS[name], name);
    }
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), M239_HASHES[name]);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], M239_HASHES[name]);
  }
  for (const [field,value] of Object.entries(M239_STATUS_FIELDS))
    assert.deepEqual(status[field], value, field);
  for (const boundary of [
  "computed finite full-profile acceptance and accepted-result transport laws",
  "not a derivation of manuscript carrier data or a theorem that every physical gain is full-profile compatible",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "does not search alternative physical gains after a mismatch",
  "No fixed weighted checkpoint or global gate closes"
]) assert.ok(row.nonClaim.includes(boundary), boundary);
});

test('M239 publication rejects weakened, supplied, assumption-backed and widened gain/search substitutes', async () => {
  const {status, inventory, map} = await compiledSources0();
  for (const name of Object.keys(M239_HASHES)) for (const substitute of ['weakened', 'supplied']) {
    const mutation = {...inventory, milestoneCandidates:inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType:substitute === 'weakened'
        ? 'Lean.Expr.const ' + String.fromCharCode(96) + 'True []'
        : 'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + row.kernelType
          + ') (' + row.kernelType + ') (Lean.BinderInfo.default)'} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonicalBytes0(mutation),
      status.leanSourceClosureSha256);
    assert.equal(result.milestones.find(row => row.id === M239_MILESTONE).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
  const name = 'PNP.DirectWire.' + NAMES[4];
  const withAuthority = row => row.name === name
    ? {...row, axioms:['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const assumptionBacked = {...inventory,
    declarations:inventory.declarations.map(withAuthority),
    milestoneCandidates:inventory.milestoneCandidates.map(withAuthority)};
  const rejected = DeriveFormalPublication0(assumptionBacked, map, canonicalBytes0(assumptionBacked),
    status.leanSourceClosureSha256);
  assert.equal(rejected.milestones.find(row => row.id === M239_MILESTONE).earned, false);
  const widened = {...map, milestones:map.milestones.map(row => row.id === M239_MILESTONE
    ? {...row, nonClaim:'The complete full-profile replacement and unconditional polynomial ZeroSlack are proved.'}
    : row)};
  assert.throws(() => DeriveFormalPublication0(inventory, widened, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256:{
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]:'0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, canonicalBytes0(inventory),
    status.leanSourceClosureSha256), /map drifted from the reviewed specification/u);
});

test('M239 adds full-profile acceptance coverage without universal compatibility, global or weighted credit', async () => {
  const {status, inventory, progress} = await compiledSources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const review = progress.history.find(entry => entry.asOfCoordinate === M239_COORDINATE);
  assert.equal(review?.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  for (const boundary of [
  "full-mode acceptance boundary for the actual production physical gain",
  "guarded runtime execution test, not theorem authority",
  "not a proof that every physical gain is full-profile compatible",
  "observer remains supplied",
  "influence, seed search and reference minima remain exhaustive",
  "No fixed checkpoint or global gate changes"
]) assert.ok(review.rationale.includes(boundary), boundary);
  assert.equal(progress.formalArtefactCoverage.earnedRows,
    status.formalPublicationMilestones.filter(row => row.earned).length);
  assert.equal(progress.formalArtefactCoverage.totalRows, status.formalPublicationMilestones.length);
  if (progress.asOfCoordinate !== M239_COORDINATE) return;
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {
    name:'PNP.Main.p_eq_np', present:false, built:false, axiomAuditPassed:false,
  });
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M239 current summaries distinguish accepted full-profile gain from global route completion and retain metrics and site deferral', async () => {
  const {progress} = await compiledSources0();
  const documentation = prose0(await text0('docs/lean_residual_terminal_gain_profile_firewall.md'));
  for (const name of NAMES) assert.ok(documentation.includes(name), name);
  for (const boundary of [
  "accepted-result laws for a supplied executable profile model",
  "not a theorem that every physical gain is full-profile compatible",
  "observer and profile model remain supplied data",
  "exhaustive finite reference constructions",
  "Runtime execution is test evidence, not theorem authority",
  "Finite termination and a smaller output do not prove a polynomial encoded-size or runtime bound",
  "No fixed checkpoint or global gate closes"
]) assert.ok(documentation.includes(boundary), boundary);
  const plan = prose0(await text0('docs/plans/2026-09-12-computed-full-profile-gain-firewall.md'));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== M239_COORDINATE) return;
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md',
    'docs/lean_residual_terminal_gain_profile_firewall.md']) {
    const current = prose0(await text0(file));
    for (const metric of metrics0(progress)) assert.ok(current.includes(metric), file + ': ' + metric);
  }
});
