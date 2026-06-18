import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('final PNP proof report CLI emits compact accepted summary and replayable files', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-proof-report-cli-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const cliPath = fileURLToPath(new URL('../bin/write-final-pnp-proof-report0.mjs', import.meta.url));
  const child = spawnSync(process.execPath, [cliPath, dir], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalPNPProofReport0');
  assert.equal(out.finalPNPProofReportAccepted, true);
  assert.equal(out.status, 'accepted');
  assert.equal(out.theorem.statement, 'P = NP');
  assert.equal(out.theorem.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.theorem.consequent, 'P = NP');
  assert.equal(out.theorem.conditional, true);
  assert.equal(out.finalPNPReleaseGateAccepted, true);
  assert.equal(out.finalPNPCertificateAccepted, true);
  assert.equal(out.releaseAuditAccepted, true);
  assert.equal(out.finalAcceptanceReplayClosed, true);
  assert.equal(out.generator, 'GeneratePCCPack');
  assert.equal(out.checkerName, 'CheckPCCPackexp0');
  assert.equal(out.checkPCCPackexpAccepted, true);
  assert.equal(out.checkAcceptRunAccepted, true);
  assert.equal(out.replayAccepted, true);
  assert.equal(out.finalVerdictAccepted, true);
  assert.equal(out.publicConclusionStatement, 'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP');

  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.finalPNPReleaseGateRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.releaseAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.certificateDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.acceptRunDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.pccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.acceptanceTranscriptDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.finalVerdictRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.reportDigest.hex, /^[0-9a-f]{64}$/);

  for (const filePath of [
    out.files.envelopePath,
    out.files.reportPath,
    out.files.releaseGatePath,
    out.files.releaseGateCheckPath,
    out.files.certificatePath,
    out.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('final PNP proof report CLI full mode emits accepted check record', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-proof-report-cli-full-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const cliPath = fileURLToPath(new URL('../bin/write-final-pnp-proof-report0.mjs', import.meta.url));
  const child = spawnSync(process.execPath, [cliPath, dir, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalPNPProofReport0');
  assert.equal(out.NF.kind, 'FinalPNPProofReport0NF');
  assert.equal(out.NF.finalPNPProofReportAccepted, true);
  assert.equal(out.NF.theorem.statement, 'P = NP');
  assert.equal(out.NF.finalPNPReleaseGateAccepted, true);
  assert.equal(out.NF.finalPNPCertificateAccepted, true);
  assert.equal(out.NF.releaseAuditAccepted, true);
  assert.equal(out.NF.finalAcceptanceReplayClosed, true);
  assert.equal(out.NF.generator, 'GeneratePCCPack');
  assert.equal(out.NF.checkerName, 'CheckPCCPackexp0');
  assert.equal(out.NF.publicConclusionStatement, 'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);

  const checkPath = path.join(dir, 'FinalPNPProofReport0.check.json');
  const checkText = await fs.readFile(checkPath, 'utf8');
  const checkRecord = JSON.parse(checkText);

  assert.equal(checkRecord.tag, 'accept');
  assert.equal(checkRecord.checker, 'CheckFinalPNPProofReport0');
});
