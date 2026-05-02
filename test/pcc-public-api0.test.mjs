import assert from 'node:assert/strict';
import fs from 'node:fs';
import { test } from 'node:test';

import * as publicApi from '../index.mjs';

const EXPECTED_INDEX_EXPORTS0 = Object.freeze([
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
].sort());

const EXPECTED_PACKAGE_EXPORTS0 = Object.freeze({
  '.': './index.mjs',
  './runall0': './pcc-runall0.mjs',
  './integrated-pipeline0': './pcc-integrated-pipeline0.mjs',
  './accept-run0': './pcc-accept-run0.mjs',
  './release-audit0': './pcc-release-audit0.mjs',
  './final-certificate0': './pcc-final-certificate-materialized0.mjs',
  './final-certificate-public-status0': './pcc-final-certificate-public-status0.mjs',
  './release-audit-final-certificate-gate0': './pcc-release-audit-final-certificate-gate0.mjs',
});

const EXPECTED_BIN_EXPORTS0 = Object.freeze({
  'pnp-runall0': './bin/runall0.mjs',
  'pnp-release-audit0': './bin/release-audit0.mjs',
});

const REQUIRED_PUBLIC_SCRIPTS0 = Object.freeze([
  'runall',
  'smoke',
  'smoke:full',
  'release:audit',
  'release:audit:full',
  'validate',
  'materialized:shell',
  'materialized:shell:full',
  'materialized:aggregate',
  'materialized:aggregate:full',
  'materialized:bridge',
  'materialized:bridge:full',
  'materialized:write-fixtures',
  'materialized:write-fixtures:full',
  'materialized:resolve-digest',
  'materialized:resolve-digest:full',
  'materialized:accept-run',
  'materialized:accept-run:full',
  'materialized:write-accept-runs',
  'materialized:write-accept-runs:full',
  'materialized:final-verdict',
  'materialized:final-verdict:full',
  'materialized:write-final-runs',
  'materialized:write-final-runs:full',
  'materialized:public-status',
  'materialized:public-status:full',
  'materialized:public-status-roundtrip',
  'materialized:public-status-roundtrip:full',              
  'materialized:final-certificate',
  'materialized:final-certificate:full',
  'materialized:final-certificate-public-status',
  'materialized:final-certificate-public-status:full',
  'release:audit:final-certificate-gate',
  'release:audit:final-certificate-gate:full',
]);

test('index.mjs exports exactly the intended public API surface', () => {
  assert.deepEqual(Object.keys(publicApi).sort(), EXPECTED_INDEX_EXPORTS0);
});

test('index.mjs does not leak internal phase constructors or package builders', () => {
  const forbiddenPatterns = [
    /^makeBoot/i,
    /^makeBootstrap/i,
    /^makeKernel/i,
    /^makeSigma/i,
    /^makeReflection/i,
    /^makeSyntheticBoot/i,
    /^makeSyntheticK/i,
    /^makeSyntheticHard/i,
    /^makeSyntheticRow/i,
    /^makeSyntheticGlobal/i,
    /^makeSyntheticLocal/i,
    /^makeSyntheticGPack/i,
    /^makeSyntheticFinalTheorem/i,
    /^makeSyntheticPCCPack/i,
    /^CheckBoot/i,
    /^CheckKImpl/i,
    /^CheckHard/i,
    /^CheckRows/i,
    /^CheckGlobalProofDAG/i,
    /^CheckLocalPackages/i,
    /^CheckGlobalFirewalls/i,
    /^CheckGPack/i,
    /^CheckFinal0/i,
    /^CheckPackSufficiency/i,
  ];

  const leaked = Object.keys(publicApi).filter((name) => {
    return forbiddenPatterns.some((pattern) => pattern.test(name));
  });

  assert.deepEqual(leaked, []);
});

test('public RunAll0 conclusion remains conditional', async () => {
  const out = await publicApi.RunAll0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'complete');
  assert.equal(out.NF.claimBoundary, 'conditional-on-accepted-generated-package');
  assert.deepEqual(out.NF.publicConclusion, publicApi.RUNALL_PUBLIC_CONCLUSION0);
  assert.equal(out.NF.publicConclusion.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});

test('package.json exposes exactly the intended public subpaths', () => {
  const pkg = JSON.parse(
    fs.readFileSync(new URL('../package.json', import.meta.url), 'utf8'),
  );

  assert.equal(pkg.main, './index.mjs');
  assert.deepEqual(pkg.exports, EXPECTED_PACKAGE_EXPORTS0);
  assert.deepEqual(pkg.bin, EXPECTED_BIN_EXPORTS0);

  for (const script of REQUIRED_PUBLIC_SCRIPTS0) {
    assert.equal(typeof pkg.scripts[script], 'string');
    assert.equal(pkg.scripts[script].length > 0, true);
  }
});

test('release audit constants agree with package exports and scripts', () => {
  assert.deepEqual(publicApi.RELEASE_AUDIT_REQUIRED_EXPORTS0, Object.keys(EXPECTED_PACKAGE_EXPORTS0));

  for (const script of publicApi.RELEASE_AUDIT_REQUIRED_SCRIPTS0) {
    assert.equal(REQUIRED_PUBLIC_SCRIPTS0.includes(script), true);
  }
});

test('package subpath exports expose final-certificate gates', async () => {
  const finalCertificate = await import('@aisknab/pnp/final-certificate0');
  const publicStatus = await import('@aisknab/pnp/final-certificate-public-status0');
  const releaseGate = await import('@aisknab/pnp/release-audit-final-certificate-gate0');

  assert.equal(typeof finalCertificate.CheckMaterializedFinalCertificate0, 'function');
  assert.equal(typeof finalCertificate.makeMaterializedFinalCertificate0, 'function');
  assert.equal(typeof finalCertificate.writeMaterializedFinalCertificateFiles0, 'function');

  assert.equal(typeof publicStatus.CheckFinalCertificatePublicStatus0, 'function');
  assert.equal(typeof publicStatus.makeFinalCertificatePublicStatus0, 'function');
  assert.equal(Array.isArray(publicStatus.FINAL_CERTIFICATE_PUBLIC_STATUS_PHASES0), true);

  assert.equal(typeof releaseGate.CheckReleaseAuditFinalCertificateGate0, 'function');
  assert.equal(typeof releaseGate.makeReleaseAuditFinalCertificateGate0, 'function');
  assert.equal(Array.isArray(releaseGate.RELEASE_AUDIT_FINAL_CERTIFICATE_GATE_PHASES0), true);
});
