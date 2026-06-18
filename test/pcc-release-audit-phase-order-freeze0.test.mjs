import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  RELEASE_AUDIT_PHASE_ORDER0,
  makeReleaseAuditConfig0,
  validateReleaseAuditPhaseOrder0,
  validateReleaseAuditSurface0,
} from '../pcc-release-audit0.mjs';

test('CheckReleaseAudit0 emits the frozen release audit phase order', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');

  const phaseOrder = out.Ledger.map((entry) => entry.phase);

  assert.deepEqual(phaseOrder, RELEASE_AUDIT_PHASE_ORDER0);

  const surfaceFreeze = out.Ledger.find((entry) => entry.phase === 'surfaceFreeze');

  assert.equal(surfaceFreeze.status, 'pass');
});

test('validateReleaseAuditPhaseOrder0 accepts the frozen phase order', () => {
  const out = validateReleaseAuditPhaseOrder0(RELEASE_AUDIT_PHASE_ORDER0);

  assert.equal(out.ok, true);
  assert.equal(out.nf.kind, 'ReleaseAuditPhaseOrderFreeze0NF');
  assert.deepEqual(out.nf.phaseOrder, RELEASE_AUDIT_PHASE_ORDER0);
});

test('validateReleaseAuditPhaseOrder0 rejects reordered release audit phases', () => {
  const reordered = [
    ...RELEASE_AUDIT_PHASE_ORDER0,
  ];

  const left = reordered.indexOf('publicSurfaceFreeze');
  const right = reordered.indexOf('materializedPublicStatusGate');

  [
    reordered[left],
    reordered[right],
  ] = [
    reordered[right],
    reordered[left],
  ];

  const out = validateReleaseAuditPhaseOrder0(reordered);

  assert.equal(out.ok, false);
  assert.deepEqual(out.path, ['Ledger', 'phaseOrder']);
  assert.equal(out.witness.reason, 'release audit phase order changed');
  assert.deepEqual(out.witness.detail.expectedPhaseOrder, RELEASE_AUDIT_PHASE_ORDER0);
  assert.deepEqual(out.witness.detail.actualPhaseOrder, reordered);
});

test('validateReleaseAuditPhaseOrder0 rejects missing release audit phases', () => {
  const missing = RELEASE_AUDIT_PHASE_ORDER0.filter((phase) => phase !== 'publicSurfaceFreeze');

  const out = validateReleaseAuditPhaseOrder0(missing);

  assert.equal(out.ok, false);
  assert.deepEqual(out.path, ['Ledger', 'phaseOrder']);
  assert.equal(out.witness.reason, 'release audit phase order changed');
  assert.deepEqual(out.witness.detail.missingPhases, ['publicSurfaceFreeze']);
});

test('validateReleaseAuditPhaseOrder0 rejects extra release audit phases', () => {
  const extra = [
    ...RELEASE_AUDIT_PHASE_ORDER0,
    'unexpectedPhase',
  ];

  const out = validateReleaseAuditPhaseOrder0(extra);

  assert.equal(out.ok, false);
  assert.deepEqual(out.path, ['Ledger', 'phaseOrder']);
  assert.equal(out.witness.reason, 'release audit phase order changed');
  assert.deepEqual(out.witness.detail.extraPhases, ['unexpectedPhase']);
});

test('validateReleaseAuditSurface0 rejects wrong phase order when supplied', async () => {
  const audit = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
  }));

  const badPhaseOrder = RELEASE_AUDIT_PHASE_ORDER0.filter((phase) => phase !== 'surfaceFreeze');

  const out = validateReleaseAuditSurface0(audit.NF, badPhaseOrder);

  assert.equal(out.ok, false);
  assert.deepEqual(out.path, ['Ledger', 'phaseOrder']);
  assert.equal(out.witness.reason, 'release audit phase order changed');
  assert.deepEqual(out.witness.detail.missingPhases, ['surfaceFreeze']);
});

test('release audit phase order keeps surfaceFreeze last', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
  }));

  const phaseOrder = out.Ledger.map((entry) => entry.phase);

  assert.equal(phaseOrder.at(-1), 'surfaceFreeze');
  assert.equal(phaseOrder.includes('publicSurfaceFreeze'), true);
  assert.equal(phaseOrder.includes('materializedPublicStatusGate'), true);
});

test('README documents release audit phase-order freeze', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit phase-order freeze'), true);
  assert.equal(readme.includes('publicSurfaceFreeze'), true);
  assert.equal(readme.includes('materializedPublicStatusGate'), true);
  assert.equal(readme.includes('surfaceFreeze'), true);
  assert.equal(readme.includes('Future phase insertions, deletions, or reorderings should fail loudly'), true);
});