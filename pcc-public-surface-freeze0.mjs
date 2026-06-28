import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import * as publicEntry0 from './index.mjs';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const PUBLIC_SURFACE_BASELINE0 = Object.freeze({
  kind: 'PublicSurfaceBaseline0',
  version: CHECKER_VERSION,
  coordinate: 'PUBLIC-SURFACE-BASELINE-2026-06-27-LOCKED-NAND-SAT-SMALL-MODELS-01',
  status: 'public-review-surface-rebased-for-locked-nand-sat-small-models',
  rationale: 'The public package script surface is intentionally extensible while the repository is being converted into a self-verifying audit stack; this baseline includes cross-runtime verification, independent-verifier no-shared-code auditing, the top-level pnp:verify entrypoint, checker-totality seed auditing, negative checker mutation auditing, rule-family coverage auditing, checker-dependency graph generation, checker no-circular-authority auditing, NAND direct-wire semantics auditing, NAND small-model auditing, and locked NAND SAT small-model auditing.',
});

export const PUBLIC_ENTRY_EXPORT_KEYS0 = Object.freeze([
  'ACCEPT_RUN_PHASES0',
  'CheckAcceptRun0',
  'CheckIntegratedPipeline0',
  'CheckReleaseAudit0',
  'CheckRunAll0',
  'EmitFinalVerdict0',
  'INTEGRATED_PIPELINE_PHASES0',
  'RELEASE_AUDIT_REQUIRED_EXPORTS0',
  'RELEASE_AUDIT_REQUIRED_MODULES0',
  'RELEASE_AUDIT_REQUIRED_SCRIPTS0',
  'RELEASE_AUDIT_REQUIRED_TESTS0',
  'RUNALL_CHECKER_COVERAGE0',
  'RUNALL_PUBLIC_CONCLUSION0',
  'ReplayAcceptRun0',
  'RunAll0',
  'RunIntegratedPCC0',
  'makeReleaseAuditConfig0',
  'makeSyntheticAcceptRun0',
  'makeSyntheticIntegratedPipeline0',
  'makeSyntheticRejectAcceptRun0',
  'makeSyntheticRunAllInput0',
  'CheckMaterializedFinalCertificate0',
  'makeMaterializedFinalCertificate0',
  'makeMaterializedFinalCertificateConfig0',
  'writeMaterializedFinalCertificateFiles0',
  'CheckFinalCertificatePublicStatus0',
  'FINAL_CERTIFICATE_PUBLIC_STATUS_PHASES0',
  'makeFinalCertificatePublicStatus0',
  'makeFinalCertificatePublicStatusConfig0',
  'writeFinalCertificatePublicStatusFiles0',
  'CheckReleaseAuditFinalCertificateGate0',
  'RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_PHASES0',
  'makeReleaseAuditFinalCertificateGate0',
  'makeReleaseAuditFinalCertificateGateConfig0',
  'writeReleaseAuditFinalCertificateGateFiles0',
  'CheckReleaseAuditConcreteFinalCertificateGate0',
  'RELEASE_AUDIT_CONCRETE_FINAL_CERTIFICATE_GATE_PHASES0',
  'makeReleaseAuditConcreteFinalCertificateGate0',
  'makeReleaseAuditConcreteFinalCertificateGateConfig0',
  'writeReleaseAuditConcreteFinalCertificateGateFiles0',
  'CheckConcreteReleaseAppendix0',
  'makeConcreteReleaseAppendix0',
  'makeConcreteReleaseAppendixConfig0',
  'writeConcreteReleaseAppendixFiles0',
  'CheckConcreteFinalAcceptanceReplay0',
  'CONCRETE_FINAL_ACCEPTANCE_REPLAY_PHASES0',
  'makeConcreteFinalAcceptanceReplay0',
  'makeConcreteFinalAcceptanceReplayConfig0',
  'writeConcreteFinalAcceptanceReplayFiles0',
  'CheckFinalPNPCertificate0',
  'FINAL_PNP_CERTIFICATE_PHASES0',
  'makeFinalPNPCertificate0',
  'makeFinalPNPCertificateConfig0',
  'writeFinalPNPCertificateFiles0',
  'CheckFinalPNPReleaseGate0',
  'FINAL_PNP_RELEASE_GATE_PHASES0',
  'makeFinalPNPReleaseGate0',
  'makeFinalPNPReleaseGateConfig0',
  'writeFinalPNPReleaseGateFiles0',
  'CheckFinalPNPProofReport0',
  'FINAL_PNP_PROOF_REPORT_PHASES0',
  'makeFinalPNPProofReport0',
  'makeFinalPNPProofReportConfig0',
  'writeFinalPNPProofReportFiles0',
].sort());

export const PUBLIC_PACKAGE_EXPORTS0 = Object.freeze({
  '.': './index.mjs',
  './accept-run0': './pcc-accept-run0.mjs',
  './integrated-pipeline0': './pcc-integrated-pipeline0.mjs',
  './release-audit0': './pcc-release-audit0.mjs',
  './final-certificate0': './pcc-final-certificate-materialized0.mjs',
  './final-certificate-public-status0': './pcc-final-certificate-public-status0.mjs',
  './release-audit-final-certificate-gate0': './pcc-release-audit-final-certificate-gate0.mjs',
  './runall0': './pcc-runall0.mjs',
  './release-audit-concrete-final-certificate-gate0': './pcc-release-audit-final-certificate-concrete-gate0.mjs',
  './concrete-release-appendix0': './pcc-concrete-release-appendix0.mjs',
  './concrete-final-acceptance-replay0': './pcc-final-acceptance-replay0.mjs',
  './final-pnp-certificate0': './pcc-final-pnp-certificate0.mjs',
  './final-pnp-release-gate0': './pcc-final-pnp-release-gate0.mjs',
  './final-pnp-proof-report0': './pcc-final-proof-report0.mjs',
});

export const PUBLIC_PACKAGE_BIN0 = Object.freeze({
  'pnp-release-audit0': './bin/release-audit0.mjs',
  'pnp-runall0': './bin/runall0.mjs',
});

export const PUBLIC_PACKAGE_SCRIPT_TARGETS0 = Object.freeze({
  check: 'node --check pcc-core.mjs',
  test: 'node --test',
  'test:negative': 'node --test test/reviewer-negative-invariants.test.mjs',
  validate: 'npm run check && npm test',
  'cross-verify': 'node scripts/cross-verify.mjs',
  'cross-verify:json': 'node scripts/cross-verify.mjs --json',
  'independent:no-shared-code': 'node scripts/audit-independent-verifiers-no-shared-code.mjs --json',
  'checker:totality': 'node scripts/audit-checker-totality.mjs --json',
  'checker:mutations': 'node scripts/audit-negative-checker-mutations.mjs --json',
  'checker:graph': 'node scripts/generate-checker-dependency-graph.mjs --json',
  'checker:cycles': 'node scripts/audit-checker-cycles.mjs --json',
  'rule-family:coverage': 'node pcc-rule-family-coverage0.mjs --json',
  'semantics:nand': 'node pcc-nand-direct-wire-semantics0.mjs --json',
  'semantics:nand:small-models': 'node pcc-nand-small-models0.mjs --json',
  'semantics:locked-nand:sat-small-models': 'node pcc-locked-nand-sat-small-models0.mjs --json',
  'pnp:verify': 'node scripts/pnp-verify-all.mjs --json',
  'examples:minimal': 'node examples/minimal/run-all.mjs',
  runall: 'node ./bin/runall0.mjs',
  smoke: 'node ./bin/runall0.mjs',
  'smoke:full': 'node ./bin/runall0.mjs --full',
  'release:audit': 'node ./bin/release-audit0.mjs',
  'release:audit:full': 'node ./bin/release-audit0.mjs --full',
  'materialized:shell': 'node ./bin/check-materialized-shell0.mjs',
  'materialized:shell:full': 'node ./bin/check-materialized-shell0.mjs --full',
  'materialized:aggregate': 'node ./bin/check-materialized-aggregate0.mjs',
  'materialized:aggregate:full': 'node ./bin/check-materialized-aggregate0.mjs --full',
  'materialized:bridge': 'node ./bin/check-materialized-acceptance-bridge0.mjs',
  'materialized:bridge:full': 'node ./bin/check-materialized-acceptance-bridge0.mjs --full',
  'materialized:write-fixtures': 'node ./bin/write-materialized-fixtures0.mjs',
  'materialized:write-fixtures:full': 'node ./bin/write-materialized-fixtures0.mjs --full',
  'materialized:resolve-digest': 'node ./bin/resolve-materialized-digest0.mjs',
  'materialized:resolve-digest:full': 'node ./bin/resolve-materialized-digest0.mjs --full',
  'materialized:accept-run': 'node ./bin/check-materialized-accept-run0.mjs',
  'materialized:accept-run:full': 'node ./bin/check-materialized-accept-run0.mjs --full',
  'materialized:write-accept-runs': 'node ./bin/write-materialized-accept-run-fixtures0.mjs',
  'materialized:write-accept-runs:full': 'node ./bin/write-materialized-accept-run-fixtures0.mjs --full',
  'materialized:final-verdict': 'node ./bin/check-materialized-final-verdict0.mjs',
  'materialized:final-verdict:full': 'node ./bin/check-materialized-final-verdict0.mjs --full',
  'materialized:write-final-runs': 'node ./bin/write-materialized-final-run-fixtures0.mjs',
  'materialized:write-final-runs:full': 'node ./bin/write-materialized-final-run-fixtures0.mjs --full',
  'materialized:public-status': 'node ./bin/check-materialized-public-status0.mjs',
  'materialized:public-status:full': 'node ./bin/check-materialized-public-status0.mjs --full',
  'materialized:public-status-roundtrip': 'node ./bin/check-materialized-public-status-roundtrip0.mjs',
  'materialized:public-status-roundtrip:full': 'node ./bin/check-materialized-public-status-roundtrip0.mjs --full',
  'materialized:final-certificate': 'node ./bin/write-materialized-final-certificate0.mjs',
  'materialized:final-certificate:full': 'node ./bin/write-materialized-final-certificate0.mjs --full',
  'materialized:final-certificate-public-status': 'node ./bin/write-final-certificate-public-status0.mjs',
  'materialized:final-certificate-public-status:full': 'node ./bin/write-final-certificate-public-status0.mjs --full',
  'release:audit:final-certificate-gate': 'node ./bin/write-release-audit-final-certificate-gate0.mjs',
  'release:audit:final-certificate-gate:full': 'node ./bin/write-release-audit-final-certificate-gate0.mjs --full',
  'release:audit:concrete-final-certificate-gate': 'node ./bin/write-release-audit-concrete-final-certificate-gate0.mjs',
  'release:audit:concrete-final-certificate-gate:full': 'node ./bin/write-release-audit-concrete-final-certificate-gate0.mjs --full',
  'release:audit:concrete-release-appendix': 'node ./bin/write-concrete-release-appendix0.mjs',
  'release:audit:concrete-release-appendix:full': 'node ./bin/write-concrete-release-appendix0.mjs --full',
  'release:audit:concrete-final-acceptance-replay': 'node ./bin/write-concrete-final-acceptance-replay0.mjs',
  'release:audit:concrete-final-acceptance-replay:full': 'node ./bin/write-concrete-final-acceptance-replay0.mjs --full',
  'release:audit:final-pnp-certificate': 'node ./bin/write-final-pnp-certificate0.mjs',
  'release:audit:final-pnp-certificate:full': 'node ./bin/write-final-pnp-certificate0.mjs --full',
  'release:audit:final-pnp-release-gate': 'node ./bin/write-final-pnp-release-gate0.mjs',
  'release:audit:final-pnp-release-gate:full': 'node ./bin/write-final-pnp-release-gate0.mjs --full',
  'release:audit:final-pnp-proof-report': 'node ./bin/write-final-pnp-proof-report0.mjs',
  'release:audit:final-pnp-proof-report:full': 'node ./bin/write-final-pnp-proof-report0.mjs --full',
});

export const PUBLIC_PACKAGE_SCRIPT_KEYS0 = Object.freeze(Object.keys(PUBLIC_PACKAGE_SCRIPT_TARGETS0).sort());

export function makePublicSurfaceFreezeConfig0(overrides = {}) {
  return {
    kind: 'PublicSurfaceFreezeConfig0',
    version: CHECKER_VERSION,
    rootDir: REPO_ROOT,
    publicEntryOverride: null,
    packageJsonOverride: null,
    ...overrides,
  };
}

export async function CheckPublicEntryReleaseSurface0(config = makePublicSurfaceFreezeConfig0()) {
  const checker = 'CheckPublicEntryReleaseSurface0';
  const ledger = [];
  const cfg = makePublicSurfaceFreezeConfig0(config);
  const configCheck = validateConfig0(cfg);
  ledger.push(makeLedgerEntry0('config', configCheck));
  if (!configCheck.ok) return makeRejectRecord0({ checker, coord: `${checker}.config`, path: configCheck.path, witness: configCheck.witness, ledger });
  const entrySurface = validateExactKeys0(cfg.publicEntryOverride ?? publicEntry0, PUBLIC_ENTRY_EXPORT_KEYS0, ['index.mjs', 'exports']);
  ledger.push(makeLedgerEntry0('publicEntryExports', entrySurface));
  if (!entrySurface.ok) return makeRejectRecord0({ checker, coord: `${checker}.publicEntryExports`, path: entrySurface.path, witness: entrySurface.witness, ledger });
  const packageJson = cfg.packageJsonOverride ?? await readPackageJson0(cfg.rootDir);
  if (isRejectLike0(packageJson)) {
    ledger.push({ phase: 'readPackageJson', status: 'fail', digest: digestCanonical0(packageJson.witness) });
    return makeRejectRecord0({ checker, coord: `${checker}.packageJson`, path: packageJson.path, witness: packageJson.witness, ledger });
  }
  const main = validatePackageMain0(packageJson);
  ledger.push(makeLedgerEntry0('packageMain', main));
  if (!main.ok) return makeRejectRecord0({ checker, coord: `${checker}.packageMain`, path: main.path, witness: main.witness, ledger });
  const exportsSurface = validateExactMapping0(packageJson.exports, PUBLIC_PACKAGE_EXPORTS0, ['package.json', 'exports']);
  ledger.push(makeLedgerEntry0('packageExports', exportsSurface));
  if (!exportsSurface.ok) return makeRejectRecord0({ checker, coord: `${checker}.packageExports`, path: exportsSurface.path, witness: exportsSurface.witness, ledger });
  const binSurface = validateExactMapping0(packageJson.bin, PUBLIC_PACKAGE_BIN0, ['package.json', 'bin']);
  ledger.push(makeLedgerEntry0('packageBin', binSurface));
  if (!binSurface.ok) return makeRejectRecord0({ checker, coord: `${checker}.packageBin`, path: binSurface.path, witness: binSurface.witness, ledger });
  const scriptSurface = validateExactMapping0(packageJson.scripts, PUBLIC_PACKAGE_SCRIPT_TARGETS0, ['package.json', 'scripts']);
  ledger.push(makeLedgerEntry0('packageScripts', scriptSurface));
  if (!scriptSurface.ok) return makeRejectRecord0({ checker, coord: `${checker}.packageScripts`, path: scriptSurface.path, witness: scriptSurface.witness, ledger });
  const nf = {
    kind: 'PublicEntryReleaseSurface0NF',
    checker,
    version: CHECKER_VERSION,
    publicEntryExportCount: PUBLIC_ENTRY_EXPORT_KEYS0.length,
    publicEntryExportKeys: PUBLIC_ENTRY_EXPORT_KEYS0,
    packageExportCount: Object.keys(PUBLIC_PACKAGE_EXPORTS0).length,
    packageExportKeys: Object.keys(PUBLIC_PACKAGE_EXPORTS0).sort(),
    packageBinCount: Object.keys(PUBLIC_PACKAGE_BIN0).length,
    packageBinKeys: Object.keys(PUBLIC_PACKAGE_BIN0).sort(),
    packageScriptCount: PUBLIC_PACKAGE_SCRIPT_KEYS0.length,
    packageScriptKeys: PUBLIC_PACKAGE_SCRIPT_KEYS0,
    packageMain: './index.mjs',
    packageType: 'module',
    surfaceFrozen: true,
    surfaceBaseline: PUBLIC_SURFACE_BASELINE0,
  };
  return makeAcceptRecord0({ checker, nf, ledger });
}

function makeLedgerEntry0(phase, result) { return { phase, status: result.ok ? 'pass' : 'fail', digest: digestCanonical0(result.nf ?? result.witness ?? null) }; }
function validateConfig0(config) {
  if (!isPlainObject0(config)) return validationReject0([], 'PublicSurfaceFreezeConfig0 must be an object', { actual: typeof config });
  if (config.kind !== undefined && config.kind !== 'PublicSurfaceFreezeConfig0') return validationReject0(['kind'], 'PublicSurfaceFreezeConfig0 kind mismatch', { actual: config.kind });
  if (config.version !== undefined && config.version !== CHECKER_VERSION) return validationReject0(['version'], `PublicSurfaceFreezeConfig0 version must be ${CHECKER_VERSION} when present`, { actual: config.version });
  if (typeof config.rootDir !== 'string' || config.rootDir.length === 0) return validationReject0(['rootDir'], 'PublicSurfaceFreezeConfig0 rootDir must be a non-empty string', { actual: config.rootDir });
  if (config.publicEntryOverride !== null && (typeof config.publicEntryOverride !== 'object' || config.publicEntryOverride === null)) return validationReject0(['publicEntryOverride'], 'PublicSurfaceFreezeConfig0 publicEntryOverride must be null or an object', { actual: typeof config.publicEntryOverride });
  if (config.packageJsonOverride !== null && !isPlainObject0(config.packageJsonOverride)) return validationReject0(['packageJsonOverride'], 'PublicSurfaceFreezeConfig0 packageJsonOverride must be null or a plain object', { actual: typeof config.packageJsonOverride });
  return validationAccept0({ kind: 'PublicSurfaceFreezeConfig0NF' });
}
function validatePackageMain0(packageJson) {
  if (!isPlainObject0(packageJson)) return validationReject0(['package.json'], 'package.json must be an object', { actual: typeof packageJson });
  if (packageJson.type !== 'module') return validationReject0(['package.json', 'type'], 'package.json type must remain module', { expected: 'module', actual: packageJson.type });
  if (packageJson.main !== './index.mjs') return validationReject0(['package.json', 'main'], 'package.json main must remain ./index.mjs', { expected: './index.mjs', actual: packageJson.main });
  return validationAccept0({ kind: 'PackageMainSurface0NF' });
}
function validateExactMapping0(actual, expected, pathArray) {
  const keyCheck = validateExactKeys0(actual, Object.keys(expected).sort(), pathArray);
  if (!keyCheck.ok) return keyCheck;
  for (const key of Object.keys(expected).sort()) if (actual[key] !== expected[key]) return validationReject0([...pathArray, key], 'public release surface mapping value changed', { key, expected: expected[key], actual: actual[key] });
  return validationAccept0({ kind: 'PublicSurfaceExactMapping0NF', keys: Object.keys(expected).sort() });
}
function validateExactKeys0(value, expectedKeys, pathArray) {
  if (value === null || typeof value !== 'object') return validationReject0(pathArray, 'public release surface target must be an object', { actual: typeof value });
  const actualKeys = Object.keys(value).sort();
  const frozenExpected = [...expectedKeys].sort();
  if (stableStringify0(actualKeys) !== stableStringify0(frozenExpected)) return validationReject0(pathArray, 'public release surface keys changed', { expectedKeys: frozenExpected, actualKeys, missingKeys: frozenExpected.filter((key) => !actualKeys.includes(key)), extraKeys: actualKeys.filter((key) => !frozenExpected.includes(key)) });
  return validationAccept0({ kind: 'PublicSurfaceExactKeys0NF', keys: actualKeys });
}
async function readPackageJson0(rootDir) {
  try { return JSON.parse(await fs.readFile(path.join(rootDir, 'package.json'), 'utf8')); }
  catch (error) { return { tag: 'rejectLike', path: ['package.json'], witness: { reason: 'package.json must be readable JSON', detail: { rootDir, error: error.message } } }; }
}
function isRejectLike0(value) { return isPlainObject0(value) && value.tag === 'rejectLike'; }
function makeAcceptRecord0({ checker, nf, ledger }) { const digest = digestCanonical0(nf); return { tag: 'accept', kind: 'accept', checker, version: CHECKER_VERSION, NF: nf, Digest: digest, Ledger: ledger, nf, digest, ledger }; }
function makeRejectRecord0({ checker, coord, path: pathArray, witness, ledger }) { const rejectNF = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path: pathArray, witness, ledger }; const digest = digestCanonical0(rejectNF); return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: pathArray, Witness: witness, Digest: digest, Ledger: ledger, coord, path: pathArray, witness, digest, ledger }; }
function validationAccept0(nf) { return { ok: true, nf }; }
function validationReject0(pathArray, reason, detail) { return { ok: false, path: pathArray, witness: { reason, detail } }; }
function isPlainObject0(value) { if (value === null || typeof value !== 'object') return false; const proto = Object.getPrototypeOf(value); return proto === Object.prototype || proto === null; }
