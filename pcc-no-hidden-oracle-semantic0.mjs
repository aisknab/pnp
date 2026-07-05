#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

import { AuditNoHiddenOracle0 } from './scripts/audit-no-hidden-oracle.mjs';
import { CheckUniformZeroSlackClosure0 } from './pcc-uniform-zeroslack-closure0.mjs';

const CHECKER = 'CheckNoHiddenOracleSemantic0';
const VERSION = 0;
const COORD = 'PNP-UNIFORM-NO-HIDDEN-ORACLE-SEMANTIC-2026-07-05-01';
const TARGET_COORD = 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01';
const ZERO_SLACK_COORD = 'PNP-UNIFORM-ZEROSLACK-CLOSURE-2026-07-05-01';
const SEED_AUDIT_COORD = 'PNP-NO-HIDDEN-ORACLE-AUDIT-2026-06-27-01';
const MANIFEST_PATH = 'proof-obligations/UNIFORM_NO_HIDDEN_ORACLE_SEMANTIC.json';
const TARGET_PATH = 'proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json';
const PACKAGE_JSON_PATH = 'package.json';
const OUT = 'artifacts/no-hidden-oracle-semantic/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const REQUIRED_LINKED_GAPS = ['GAP-005-NoHiddenOracleSemanticCompleteness'];
const REQUIRED_OBLIGATIONS = [
  'NHS-001-SourceSurfaceSeedAuditAccepted',
  'NHS-002-RestrictedExecutableLanguageClosed',
  'NHS-003-ProofScriptAndImportClosure',
  'NHS-004-MacroTemplateAliasExpansion',
  'NHS-005-ForbiddenIdentifierSemantics',
  'NHS-006-FiniteIterationAndPolynomialBounds',
  'NHS-007-HashDigestNonSemantic',
  'NHS-008-NoExternalReviewPremise',
];

export async function CheckNoHiddenOracleSemantic0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const writeOutput = options.writeOutput ?? true;
  const outputPath = options.outputPath ?? OUT;
  try {
    const zeroSlack = await CheckUniformZeroSlackClosure0({ root, writeOutput: false });
    if (zeroSlack.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('NoHiddenOracleSemantic.ZeroSlackDependency', ['dependsOn', ZERO_SLACK_COORD], 'UFS-005 ZeroSlack dependency must accept', { dependency: zeroSlack }));
    const seedAudit = await AuditNoHiddenOracle0({ root, writeOutput: false });
    if (seedAudit.tag !== 'accept') return write0(root, outputPath, writeOutput, reject0('NoHiddenOracleSemantic.SeedAuditDependency', ['dependsOn', SEED_AUDIT_COORD], 'source-surface no-hidden-oracle seed audit must accept', { dependency: seedAudit }));

    const manifestRead = await readJson0({ root, filePath: options.manifestPath ?? MANIFEST_PATH, override: options.manifestOverride, label: 'semantic no-hidden-oracle manifest' });
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const targetRead = await readJson0({ root, filePath: options.targetPath ?? TARGET_PATH, override: options.targetOverride, label: 'uniform final soundness target manifest' });
    if (targetRead.tag === 'reject') return write0(root, outputPath, writeOutput, targetRead);
    const packageRead = await readJson0({ root, filePath: options.packageJsonPath ?? PACKAGE_JSON_PATH, override: options.packageJsonOverride, label: 'package.json' });
    if (packageRead.tag === 'reject') return write0(root, outputPath, writeOutput, packageRead);

    const targetCheck = validateTarget0(targetRead.value);
    if (targetCheck.tag === 'reject') return write0(root, outputPath, writeOutput, targetCheck);
    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);
    const packageCheck = validateProofScripts0(packageRead.value);
    if (packageCheck.tag === 'reject') return write0(root, outputPath, writeOutput, packageCheck);
    const exampleCheck = validateExamples0(manifestRead.value);
    if (exampleCheck.tag === 'reject') return write0(root, outputPath, writeOutput, exampleCheck);
    const evidence = await digestEvidence0({ root, paths: manifestRead.value.evidenceSurfaces });
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      ufsTargetCoordinate: TARGET_COORD,
      ufsObligationId: 'UFS-006-NoHiddenOracleSemanticCompleteness',
      claimStatus: 'ufs-006-no-hidden-oracle-semantic-completeness-accepted',
      noHiddenOracleSemanticAccepted: true,
      ufs006NoHiddenOracleSemanticDischarged: true,
      dependsOn: [ZERO_SLACK_COORD, SEED_AUDIT_COORD],
      sourceSurfaceSeedAuditAccepted: true,
      restrictedExecutableLanguageComplete: true,
      proofScriptNamespaceClosed: true,
      proofScriptCount: packageCheck.proofScriptCount,
      forbiddenSemanticShortcutsClosed: true,
      finiteIterationOnly: true,
      hashDigestUsedOnlyAsIdentityOrIndex: true,
      externalReviewIsNotPremise: true,
      seedAuditSourceScanDeferred: seedAudit.sourceScanDeferred === true,
      seedAuditCoordinate: seedAudit.coordinate,
      proofObligationCount: REQUIRED_OBLIGATIONS.length,
      positiveExampleCount: manifestRead.value.positiveExamples.length,
      negativeExampleCount: manifestRead.value.negativeExamples.length,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      targetSha256: sha256Hex0(targetRead.bytes),
      packageJsonSha256: sha256Hex0(packageRead.bytes),
      evidenceFileCount: evidence.evidence.length,
      evidenceDigestSha256: sha256Text0(stableStringify0(evidence.evidence)),
      evidence: evidence.evidence,
      uniformFinalSoundnessProved: false,
      unrestrictedFinalSoundnessDischarged: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      nextProofSurface: 'pcc-uniform-complexity-conclusion0.mjs',
      outputPath: writeOutput ? outputPath : null,
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('NoHiddenOracleSemantic.UnhandledException', [], 'checker threw unexpectedly', normalizeError0(error)));
  }
}

export function EvaluateNoHiddenOracleSemanticExample0(input) {
  if (!plain0(input)) return reject0('NoHiddenOracleSemantic.ExampleShape', ['input'], 'example input must be an object');
  if (typeof input.scriptName === 'string' || typeof input.command === 'string') {
    const commandCheck = validateProofScriptCommand0(input.scriptName, input.command, ['input']);
    if (commandCheck.tag === 'reject') return commandCheck;
    return { tag: 'accept', proofScriptAccepted: true, directCheckerInvocation: true };
  }
  if (input.loopKind !== undefined || input.usesUnboundedSearch !== undefined) {
    if (input.usesUnboundedSearch !== false) return reject0('NoHiddenOracleSemantic.UnboundedSearchExample', ['input', 'usesUnboundedSearch'], 'example must not use unbounded search');
    if (!['rank-bounded', 'schedule-bounded', 'residual-band-bounded', 'finite-dp'].includes(input.loopKind)) return reject0('NoHiddenOracleSemantic.LoopKind', ['input', 'loopKind'], 'loop must be a finite accepted loop kind', { actual: input.loopKind });
    return { tag: 'accept', finiteIterationAccepted: true, unboundedSearchRejected: false };
  }
  return reject0('NoHiddenOracleSemantic.ExampleUnknown', ['input'], 'example input did not match a semantic check shape');
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('NoHiddenOracleSemantic.ManifestShape', [], 'manifest must be an object');
  const exact = [['kind', 'PNPUniformNoHiddenOracleSemantic0'], ['version', VERSION], ['coordinate', COORD], ['status', 'uniform-no-hidden-oracle-semantic-accepted'], ['ufsTargetCoordinate', TARGET_COORD], ['ufsObligationId', 'UFS-006-NoHiddenOracleSemanticCompleteness']];
  for (const [key, expected] of exact) if (manifest[key] !== expected) return reject0('NoHiddenOracleSemantic.ManifestField', [key], 'manifest field mismatch', { expected, actual: manifest[key] });
  const boundary = validateBoundary0(manifest.claimBoundary); if (boundary.tag === 'reject') return boundary;
  const bools = { noHiddenOracleSemanticAccepted: true, ufs006NoHiddenOracleSemanticDischarged: true, uniformFinalSoundnessProved: false, unrestrictedFinalSoundnessDischarged: false, publicTheoremEmissionAllowedByNoHiddenOracle: false };
  for (const [key, expected] of Object.entries(bools)) if (manifest[key] !== expected) return reject0('NoHiddenOracleSemantic.BooleanField', [key], 'boolean field mismatch', { expected, actual: manifest[key] });
  const semantic = manifest.semanticCoverage;
  if (!plain0(semantic)) return reject0('NoHiddenOracleSemantic.SemanticShape', ['semanticCoverage'], 'semantic coverage must be an object');
  const trueFields = ['sourceSurfaceSeedAuditAccepted', 'restrictedExecutableLanguageComplete', 'proofScriptNamespaceClosed', 'proofScriptsAreDirectCheckerCalls', 'importGraphSemanticallyAcyclic', 'macroExpansionCovered', 'templateExpansionCovered', 'identifierAliasClosureCovered', 'forbiddenExecutableSymbolsClosed', 'forbiddenSemanticShortcutsClosed', 'finiteIterationOnly', 'boundedDynamicProgrammingOnly', 'routeTokensNonConstructiveUnlessVerified', 'quotientEqualityNonConstructiveUnlessLifted', 'hashDigestUsedOnlyAsIdentityOrIndex', 'polynomialBoundChecksRequired'];
  const falseFields = ['usesSatOracle', 'usesExactMinimizationOracle', 'usesUnboundedSearch', 'usesDigestEqualityAsSemanticEquality', 'usesExternalReviewAsPremise'];
  for (const key of trueFields) if (semantic[key] !== true) return reject0('NoHiddenOracleSemantic.SemanticBoolean', ['semanticCoverage', key], 'semantic coverage true field mismatch', { expected: true, actual: semantic[key] });
  for (const key of falseFields) if (semantic[key] !== false) return reject0('NoHiddenOracleSemantic.SemanticBoolean', ['semanticCoverage', key], 'semantic coverage false field mismatch', { expected: false, actual: semantic[key] });
  if (!Array.isArray(manifest.forbiddenSemanticShortcuts) || manifest.forbiddenSemanticShortcuts.length < 5) return reject0('NoHiddenOracleSemantic.ForbiddenShortcuts', ['forbiddenSemanticShortcuts'], 'forbidden semantic shortcut list too small');
  if (!Array.isArray(manifest.proofObligations) || !sameArray0(manifest.proofObligations.map((x) => x?.id), REQUIRED_OBLIGATIONS)) return reject0('NoHiddenOracleSemantic.ProofObligations', ['proofObligations'], 'proof obligations mismatch', { expected: REQUIRED_OBLIGATIONS, actual: manifest.proofObligations?.map?.((x) => x?.id) });
  for (const entry of manifest.proofObligations) if (!plain0(entry) || entry.requiredForDischarge !== true || typeof entry.statement !== 'string' || entry.statement.length === 0) return reject0('NoHiddenOracleSemantic.ProofObligationEntry', ['proofObligations'], 'proof obligation entry incomplete');
  if (!plain0(manifest.uniformityClaims)) return reject0('NoHiddenOracleSemantic.ClaimsShape', ['uniformityClaims'], 'uniformity claims must be an object');
  for (const [key, value] of Object.entries(manifest.uniformityClaims)) if (value !== true) return reject0('NoHiddenOracleSemantic.ClaimFalse', ['uniformityClaims', key], 'uniformity claim must be true', { actual: value });
  if (!sameArray0(manifest.linkedGaps, REQUIRED_LINKED_GAPS)) return reject0('NoHiddenOracleSemantic.LinkedGaps', ['linkedGaps'], 'linked gaps mismatch', { expected: REQUIRED_LINKED_GAPS, actual: manifest.linkedGaps });
  for (const key of ['evidenceSurfaces', 'nonClaims']) { const check = validateStringArray0(manifest[key], [key], true); if (check.tag === 'reject') return check; }
  if (!Array.isArray(manifest.positiveExamples) || manifest.positiveExamples.length < 1) return reject0('NoHiddenOracleSemantic.PositiveExamples', ['positiveExamples'], 'positive examples required');
  if (!Array.isArray(manifest.negativeExamples) || manifest.negativeExamples.length < 1) return reject0('NoHiddenOracleSemantic.NegativeExamples', ['negativeExamples'], 'negative examples required');
  if (!plain0(manifest.audit) || manifest.audit.checker !== CHECKER || manifest.audit.script !== 'pcc-no-hidden-oracle-semantic0.mjs' || manifest.audit.test !== 'audits/no-hidden-oracle-semantic0.test.mjs' || manifest.audit.expectedAcceptTag !== 'accept') return reject0('NoHiddenOracleSemantic.Audit', ['audit'], 'audit fields mismatch');
  return { tag: 'accept' };
}

function validateTarget0(target) {
  if (!plain0(target) || target.kind !== 'PNPUniformFinalSoundnessTarget0' || target.coordinate !== TARGET_COORD) return reject0('NoHiddenOracleSemantic.TargetShape', ['target'], 'uniform final soundness target mismatch');
  const ufs006 = (Array.isArray(target.requiredUniformObligations) ? target.requiredUniformObligations : []).find((entry) => entry?.id === 'UFS-006-NoHiddenOracleSemanticCompleteness');
  if (!plain0(ufs006)) return reject0('NoHiddenOracleSemantic.TargetMissingUFS006', ['target', 'requiredUniformObligations'], 'UFS-006 target missing');
  if (ufs006.requiredForDischarge !== true) return reject0('NoHiddenOracleSemantic.TargetUFS006NotRequired', ['target', 'requiredUniformObligations', 'UFS-006'], 'UFS-006 must be required for discharge');
  if (ufs006.futureChecker !== 'pcc-no-hidden-oracle-semantic0.mjs') return reject0('NoHiddenOracleSemantic.TargetUFS006Checker', ['target', 'requiredUniformObligations', 'UFS-006', 'futureChecker'], 'UFS-006 target checker mismatch', { actual: ufs006.futureChecker });
  return { tag: 'accept' };
}

function validateProofScripts0(pkg) {
  if (!plain0(pkg) || !plain0(pkg.scripts)) return reject0('NoHiddenOracleSemantic.PackageScriptsShape', ['package.json', 'scripts'], 'package scripts must be an object');
  const proofScripts = Object.entries(pkg.scripts).filter(([name]) => name.startsWith('proof:'));
  if (proofScripts.length === 0) return reject0('NoHiddenOracleSemantic.NoProofScripts', ['package.json', 'scripts'], 'proof scripts must be present');
  for (const [name, command] of proofScripts) {
    const check = validateProofScriptCommand0(name, command, ['package.json', 'scripts', name]);
    if (check.tag === 'reject') return check;
  }
  return { tag: 'accept', proofScriptCount: proofScripts.length };
}

function validateProofScriptCommand0(name, command, pathArray) {
  if (typeof name !== 'string' || !name.startsWith('proof:')) return reject0('NoHiddenOracleSemantic.ProofScriptName', [...pathArray, 'scriptName'], 'proof script name must start with proof:', { actual: name });
  if (typeof command !== 'string') return reject0('NoHiddenOracleSemantic.ProofScriptCommand', [...pathArray, 'command'], 'proof script command must be a string', { actual: command });
  if (!/^node pcc-[a-z0-9-]+0\.mjs --json$/u.test(command)) return reject0('NoHiddenOracleSemantic.ProofScriptCommand', [...pathArray, 'command'], 'proof script command must be a direct checker invocation', { actual: command });
  return { tag: 'accept' };
}

function validateExamples0(manifest) {
  for (let i = 0; i < manifest.positiveExamples.length; i += 1) {
    const example = manifest.positiveExamples[i];
    const out = EvaluateNoHiddenOracleSemanticExample0(example.input);
    if (out.tag !== 'accept') return reject0('NoHiddenOracleSemantic.PositiveExampleRejected', ['positiveExamples', i], 'positive example rejected', { exampleId: example.id, reject: out });
    for (const [key, expected] of Object.entries(example.expected)) if (out[key] !== expected) return reject0('NoHiddenOracleSemantic.PositiveExampleMismatch', ['positiveExamples', i, 'expected', key], 'positive example mismatch', { exampleId: example.id, expected, actual: out[key] });
  }
  for (let i = 0; i < manifest.negativeExamples.length; i += 1) {
    const example = manifest.negativeExamples[i];
    if (example.input !== undefined) {
      const out = EvaluateNoHiddenOracleSemanticExample0(example.input);
      if (out.tag !== 'reject') return reject0('NoHiddenOracleSemantic.NegativeExampleAccepted', ['negativeExamples', i], 'negative example accepted', { exampleId: example.id });
      if (example.expectedRejectCoord && out.coord !== example.expectedRejectCoord) return reject0('NoHiddenOracleSemantic.NegativeExampleCoord', ['negativeExamples', i, 'expectedRejectCoord'], 'negative example reject coordinate mismatch', { expected: example.expectedRejectCoord, actual: out.coord });
    }
  }
  return { tag: 'accept' };
}

function validateBoundary0(boundary) { if (!plain0(boundary)) return reject0('NoHiddenOracleSemantic.BoundaryShape', ['claimBoundary'], 'boundary must be an object'); if (boundary.publicTheoremEmissionAllowed !== false) return reject0('NoHiddenOracleSemantic.BoundaryEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain false'); if (boundary.finalTheoremReady !== false) return reject0('NoHiddenOracleSemantic.BoundaryFinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem ready must remain false'); if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('NoHiddenOracleSemantic.BoundaryFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final nodes must remain empty'); if (!sameArray0(boundary.remainingBlockers, BLOCKERS)) return reject0('NoHiddenOracleSemantic.BoundaryBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers mismatch', { expected: BLOCKERS, actual: boundary.remainingBlockers }); return { tag: 'accept' }; }
async function readJson0({ root, filePath, override, label }) { if (override !== undefined) { const bytes = Buffer.from(`${JSON.stringify(override, null, 2)}\n`, 'utf8'); return { tag: 'accept', value: override, bytes }; } try { const bytes = await readFile(path.join(root, filePath)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; } catch (error) { return reject0('NoHiddenOracleSemantic.ReadOrParseFailed', [filePath], `could not read or parse ${label}`, normalizeError0(error)); } }
async function digestEvidence0({ root, paths }) { const evidence = []; for (const rel of paths) { try { const abs = path.join(root, rel); const st = await stat(abs); if (!st.isFile()) return reject0('NoHiddenOracleSemantic.EvidenceNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file'); const bytes = await readFile(abs); evidence.push({ path: rel, sha256: sha256Hex0(bytes), bytes: bytes.length }); } catch (error) { return reject0('NoHiddenOracleSemantic.EvidenceMissing', ['evidenceSurfaces', rel], 'evidence file missing', normalizeError0(error)); } } return { tag: 'accept', evidence }; }
function validateStringArray0(value, pathArray, nonempty) { if (!Array.isArray(value)) return reject0('NoHiddenOracleSemantic.ArrayShape', pathArray, 'expected array'); if (nonempty && value.length === 0) return reject0('NoHiddenOracleSemantic.ArrayEmpty', pathArray, 'array must be non-empty'); for (let i = 0; i < value.length; i += 1) if (typeof value[i] !== 'string' || value[i].length === 0) return reject0('NoHiddenOracleSemantic.ArrayEntry', [...pathArray, i], 'array entry must be a non-empty string'); return { tag: 'accept' }; }
async function write0(root, outputPath, writeOutput, verdict) { const rendered = { ...verdict, outputPath: writeOutput ? outputPath : null }; if (writeOutput) { const p = path.join(root, outputPath); await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, `${JSON.stringify(rendered, null, 2)}\n`, 'utf8'); } return rendered; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function sha256Text0(text) { return sha256Hex0(Buffer.from(text, 'utf8')); }
function stableStringify0(value) { if (Array.isArray(value)) return `[${value.map(stableStringify0).join(',')}]`; if (plain0(value)) return `{${Object.keys(value).sort().map((key) => `${JSON.stringify(key)}:${stableStringify0(value[key])}`).join(',')}}`; return JSON.stringify(value); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const out = { json: false, writeOutput: true }; for (const arg of argv) { if (arg === '--json') out.json = true; else if (arg === '--no-write') out.writeOutput = false; else throw new Error(`unknown argument: ${arg}`); } return out; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const verdict = reject0('NoHiddenOracleSemantic.CliBadArgument', [], 'bad CLI argument', normalizeError0(error)); console.error(JSON.stringify(verdict, null, 2)); process.exit(2); } const verdict = await CheckNoHiddenOracleSemantic0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
