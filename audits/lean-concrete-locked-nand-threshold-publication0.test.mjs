import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/Concrete/LockedNANDThresholdPublication.lean';
const AUDIT_PATH =
  'lean-audit/PNPConcreteLockedNANDThresholdPublicationAxiomAudit.lean';
const THEOREM = 'PNP.Main.locked_nand_threshold';
const TYPE_SHA256 =
  '951ec63c09e9a096aacc26332a97607dade4a1f412229f9185aff5c7f36aa591';

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

test('report-facing locked-NAND threshold theorem is a closed concrete reduction', async () => {
  const source = await text0(SOURCE_PATH);
  const compact = compact0(source);
  assert.deepEqual(imports0(source), ['PNP.Concrete.CNFToNANDPolynomialReduction']);
  assert.equal(hasLeanAssumptionDeclaration0(source), false);
  assert.equal(hasPrivateLeanDeclaration0(source), false);
  assert.equal(hasUnauditedLeanDeclarationForm0(source), false);
  assert.deepEqual(
    explicitLeanDeclarationHeads0(source).map(({ kind, name }) => [kind, name]),
    [['theorem', 'locked_nand_threshold']],
  );
  assert.match(compact,
    /theorem locked_nand_threshold : PNP\.Concrete\.ReducesTo PNP\.Concrete\.CNFSAT PNP\.Concrete\.LockedNAND\.EncodedLockedNANDThreshold := PNP\.Concrete\.CNFToNAND\.cnfSAT_reducesTo_encodedLockedNANDThreshold/u);
  assert.doesNotMatch(compact,
    /PNP\.(?:LockedNANDThreshold|ResidualBandExactMinimization)|\b(?:sorry|admit|axiom|opaque|constant)\b/u);
});

test('root closure and exact axiom transcript include the publication theorem', async () => {
  const [root, audit] = await Promise.all([
    text0('lean/PNP.lean'),
    text0(AUDIT_PATH),
  ]);
  assert.equal(imports0(root).includes(
    'PNP.Concrete.LockedNANDThresholdPublication'), true);
  assert.deepEqual(imports0(audit), [
    'PNP.Concrete.LockedNANDThresholdPublication',
  ]);
  assert.deepEqual(
    [...audit.matchAll(/^#print axioms (.+?)\s*$/gmu)].map((match) => match[1]),
    [THEOREM],
  );
});

test('compiled inventory earns only the concrete locked-NAND publication milestone', async () => {
  const [inventory, status] = await Promise.all([
    text0('status/LEAN_THEOREM_INVENTORY.json').then(JSON.parse),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
  ]);
  const candidate = inventory.milestoneCandidates.find(
    (entry) => entry.name === THEOREM,
  );
  assert.notEqual(candidate, undefined);
  assert.equal(candidate.module,
    'PNP.Concrete.LockedNANDThresholdPublication');
  assert.deepEqual(candidate.axioms, ['Quot.sound', 'propext']);
  const milestone = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'global-locked-nand-threshold',
  );
  assert.equal(milestone.earned, true);
  assert.equal(milestone.status,
    'formalized-concrete-locked-nand-threshold');
  assert.equal(milestone.theoremRows[0].actualKernelTypeSha256, TYPE_SHA256);
  assert.equal(milestone.theoremRows[0].kernelTypeFingerprintMatches, true);
  assert.equal(status.leanLockedNANDPolynomialBuilderFormalized, true);
  assert.equal(status.leanLockedNANDBuilderFormalized, true);
  assert.equal(status.leanLockedNANDThresholdFormalized, true);
  assert.equal(status.remainingBlockers.includes('Formal.LockedNANDThreshold'), false);
  assert.equal(status.remainingBlockers.includes('Formal.ZeroSlack'), true);
  assert.equal(status.remainingBlockers.includes('Formal.RootTheoremAndAxiomAudit'), true);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});

test('workflow executes the dedicated theorem audit and hostile source test', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /lake env lean -DwarningAsError=true lean-audit\/PNPConcreteLockedNANDThresholdPublicationAxiomAudit\.lean/u);
  assert.match(workflow,
    /node --test audits\/lean-concrete-locked-nand-threshold-publication0\.test\.mjs/u);
});

test('hostile mutations cannot substitute the legacy label or weaken the source language', async () => {
  const source = await text0(SOURCE_PATH);
  assert.doesNotMatch(compact0(source), /PNP\.LockedNANDThreshold/u);
  const legacyTarget = source.replace(
    'PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold',
    'PNP.LockedNANDThreshold',
  );
  assert.notEqual(legacyTarget, source);
  assert.match(legacyTarget, /PNP\.LockedNANDThreshold/u);
  const weakenedSource = source.replace(
    'PNP.Concrete.CNFSAT',
    'PNP.Concrete.LockedNAND.EncodedNANDSAT',
  );
  assert.notEqual(weakenedSource, source);
  assert.doesNotMatch(compact0(weakenedSource),
    /ReducesTo PNP\.Concrete\.CNFSAT/u);
});
