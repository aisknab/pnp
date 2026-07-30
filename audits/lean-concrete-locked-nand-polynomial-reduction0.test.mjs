import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const MODULE =
  'lean/PNP/Concrete/LockedNANDPolynomialReduction.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteLockedNANDPolynomialReductionAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteLockedNANDPolynomialReduction.lean';
const DOCS =
  'docs/lean_concrete_locked_nand_polynomial_reduction.md';
const TEST =
  'audits/lean-concrete-locked-nand-polynomial-reduction0.test.mjs';
const NAMESPACE = 'PNP.Concrete.LockedNAND';

const REUSED_DECLARATIONS = Object.freeze([
  'PNP.Concrete.PolynomialReduction',
  'PNP.Concrete.ReducesTo',
  `${NAMESPACE}.EncodedNANDSAT`,
  `${NAMESPACE}.EncodedLockedNANDThreshold`,
  `${NAMESPACE}.buildLockedNANDInstance`,
  `${NAMESPACE}.buildLockedNANDInstance_correct`,
  `${NAMESPACE}.TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction`,
  `${NAMESPACE}.TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction_output`,
  `${NAMESPACE}.TargetEmitterControllerCompiled.strictLockedNANDRawRefinement`,
]);

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.strictLockedNANDPolynomialReduction`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_function`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_output`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_correct`,
  `${NAMESPACE}.encodedNANDSAT_reducesTo_encodedLockedNANDThreshold`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_rawRefinement`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_hasRawRefinement`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_function`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_output`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_correct`,
  `${NAMESPACE}.encodedNANDSAT_reducesTo_encodedLockedNANDThreshold`,
  `${NAMESPACE}.strictLockedNANDPolynomialReduction_hasRawRefinement`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source)
    .replace(/\s+/gu, ' ')
    .trim();
}

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);

  if (hasLeanAssumptionDeclaration0(source)) {
    failures.push('assumption');
  }
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('declaration-form');
  }
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u
    .test(stripped)) {
    failures.push('shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)
      || /\b(?:hostLookup|hostSideLookup|scheduleLookup|hostDecoder|hostSchedule|scheduleOracle|precomputedSchedule)\b/u
        .test(stripped)) {
    failures.push('host-lookup');
  }
  if (/\b(?:callerCertificate|executionCertificate|traceCertificate|proofCertificate|trustFlag)\b/u
    .test(stripped)) {
    failures.push('caller-certificate');
  }
  if (/\b(?:NPComplete|cnfSATInP|p_eq_np|LockedNANDThreshold)\b/u
    .test(stripped.replaceAll('EncodedLockedNANDThreshold', ''))) {
    failures.push('overclaim');
  }
  if (!compact.includes(
    'def strictLockedNANDPolynomialReduction : PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold := { function := TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction')) {
    failures.push('function-boundary');
  }
  if (!compact.includes(
    'rw [ TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction_output ] exact buildLockedNANDInstance_correct bits')) {
    failures.push('semantic-boundary');
  }
  if (!compact.includes(
    'theorem strictLockedNANDPolynomialReduction_correct (bits : BitString) : EncodedNANDSAT bits ↔ EncodedLockedNANDThreshold (strictLockedNANDPolynomialReduction.function.output bits)')) {
    failures.push('language-equivalence');
  }
  if (!compact.includes(
    'theorem encodedNANDSAT_reducesTo_encodedLockedNANDThreshold : ReducesTo EncodedNANDSAT EncodedLockedNANDThreshold := ⟨strictLockedNANDPolynomialReduction⟩')) {
    failures.push('reduction-witness');
  }
  if (!compact.includes(
    'def strictLockedNANDPolynomialReduction_rawRefinement : FunctionProgram.RawRefinement strictLockedNANDPolynomialReduction.function.program')) {
    failures.push('raw-refinement');
  }
  if (!compact.includes(
    'theorem strictLockedNANDPolynomialReduction_hasRawRefinement : Nonempty (FunctionProgram.RawRefinement strictLockedNANDPolynomialReduction.function.program)')) {
    failures.push('raw-refinement-pin');
  }
  return [...new Set(failures)];
}

test('reduction package binds the exact composed function and languages',
  async () => {
    const source = await text0(MODULE);
    assert.deepEqual(imports0(source), [
      'PNP.Concrete.LockedNANDTargetEmitter',
    ]);
    assert.deepEqual(validateSource0(source), []);
    assert.deepEqual(
      explicitLeanDeclarationHeads0(source)
        .map(({ kind, name }) => [kind, name]),
      [
        ['def', 'strictLockedNANDPolynomialReduction'],
        ['theorem', 'strictLockedNANDPolynomialReduction_function'],
        ['theorem', 'strictLockedNANDPolynomialReduction_output'],
        ['theorem', 'strictLockedNANDPolynomialReduction_correct'],
        ['theorem',
          'encodedNANDSAT_reducesTo_encodedLockedNANDThreshold'],
        ['def',
          'strictLockedNANDPolynomialReduction_rawRefinement'],
        ['theorem',
          'strictLockedNANDPolynomialReduction_hasRawRefinement'],
      ],
    );
  });

test('axiom transcript covers all new and reused exact interfaces',
  async () => {
    const audit = await text0(AXIOM_AUDIT);
    assert.deepEqual(imports0(audit), [
      'PNP.Concrete.LockedNANDPolynomialReduction',
    ]);
    assert.deepEqual(printed0(audit), [
      ...REUSED_DECLARATIONS,
      ...PUBLIC_DECLARATIONS,
    ]);
    assert.equal(new Set(printed0(audit)).size, 16);

    const inventory = JSON.parse(
      await text0('status/LEAN_THEOREM_INVENTORY.json'),
    );
    const rows = new Map(
      inventory.declarations.map((entry) => [entry.name, entry]),
    );
    for (const name of [...REUSED_DECLARATIONS, ...PUBLIC_DECLARATIONS]) {
      const row = rows.get(name);
      assert.notEqual(row, undefined, name);
      assert.equal(
        row.axioms.every((axiom) =>
          ['Quot.sound', 'propext'].includes(axiom)),
        true,
        `${name}:${row.axioms.join(',')}`,
      );
    }
  });

test('constructive regression covers fail-closed and size-independent cases',
  async () => {
    const regression = await text0(REGRESSION);
    for (const fragment of [
      'strictLockedNANDPolynomialReduction_function',
      'strictLockedNANDPolynomialReduction_output',
      'strictLockedNANDPolynomialReduction_correct',
      'encodedNANDSAT_reducesTo_encodedLockedNANDThreshold',
      'strictLockedNANDPolynomialReduction_rawRefinement',
      'strictLockedNANDPolynomialReduction_hasRawRefinement',
      'strictLockedNANDPolynomialReduction.function.output [] = []',
      'empty_not_encodedLockedNANDThreshold',
      'invalidReferenceCircuit',
      'buildLockedNANDInstance_of_malformed',
      'zeroGateCircuit',
      'oneGateCircuit',
      'multiGateCircuit',
    ]) assert.equal(regression.includes(fragment), true, fragment);
    assert.doesNotMatch(
      stripLeanCommentsAndStrings0(regression),
      /\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u,
    );
  });

test('root, status, milestone, workflow, and documentation publish the boundary',
  async () => {
    const [root, status, map, workflow, docs, packageJson, verifier] =
      await Promise.all([
        text0('lean/PNP.lean'),
        text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
        text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
        text0('.github/workflows/lean-bridge.yml'),
        text0(DOCS),
        text0('package.json').then(JSON.parse),
        text0('scripts/pnp-verify-all.mjs'),
      ]);

    assert.match(root,
      /^import PNP\.Concrete\.LockedNANDPolynomialReduction$/mu);
    for (const field of [
      'leanConcreteLockedNANDPolynomialReductionFormalized',
      'leanConcreteLockedNANDPolynomialReductionAxiomAuditPassed',
      'leanConcreteLockedNANDPolynomialReductionExactFunctionFormalized',
      'leanConcreteLockedNANDPolynomialReductionExactOutputFormalized',
      'leanConcreteLockedNANDPolynomialReductionLanguageEquivalenceFormalized',
      'leanConcreteLockedNANDPolynomialReductionWitnessFormalized',
      'leanConcreteLockedNANDPolynomialReductionRawRefinementFormalized',
    ]) assert.equal(status[field], true, field);
    assert.equal(
      status.leanConcreteLockedNANDPolynomialReductionAuditedDeclarationCount,
      16,
    );
    assert.equal(
      status.leanConcreteLockedNANDPolynomialReductionScope,
      'strict-version-zero-parser-emitter-polynomial-reduction-with-exact-language-equivalence-and-recursive-raw-refinement',
    );
    assert.equal(status.projectSpecificAxiomInventory.length, 4);
    assert.equal(status.remainingBlockers.length, 6);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);

    const milestone = status.formalPublicationMilestones.find(
      ({ id }) => id === 'concrete-locked-nand-polynomial-reduction',
    );
    assert.equal(milestone?.earned, true);
    assert.equal(milestone.status, 'formalized-polynomial-reduction');
    assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
    for (const name of MILESTONE_THEOREMS) {
      assert.match(
        map.earnedMilestoneTheoremKernelTypeSha256[name],
        /^[0-9a-f]{64}$/u,
        name,
      );
    }
    for (const id of [
      'global-locked-nand-threshold',
      'global-zeroslack-pccmin',
      'concrete-publication-root',
    ]) {
      assert.equal(
        status.formalPublicationMilestones.find(
          (milestoneRow) => milestoneRow.id === id,
        )?.earned,
        false,
        id,
      );
    }

    for (const fragment of [
      'PNPConcreteLockedNANDPolynomialReductionAxiomAudit.lean',
      'PNPConcreteLockedNANDPolynomialReduction.lean',
      'lean-concrete-locked-nand-polynomial-reduction0.test.mjs',
    ]) assert.equal(workflow.includes(fragment), true, fragment);
    assert.equal(packageJson.scripts.test.includes(TEST), true);
    assert.equal(verifier.includes(TEST), true);

    const compactDocs = docs.replaceAll(/\s+/gu, ' ');
    for (const fragment of [
      status.leanTheoremInventoryCoordinate,
      status.formalPublicationMapCoordinate,
      status.coordinate,
      'PolynomialReduction',
      'EncodedNANDSAT',
      'EncodedLockedNANDThreshold',
      'strictLockedNANDPolynomialTimeFunction',
      'buildLockedNANDInstance',
      'RawRefinement',
      'legacy',
      'abstract',
      'P = NP',
    ]) assert.equal(compactDocs.includes(fragment), true, fragment);
  });

test('hostile mutations revoke reduction credit', async () => {
  const source = await text0(MODULE);

  assert.ok(validateSource0(
    `${source}\naxiom hidden : True\n`,
  ).includes('assumption'));
  assert.ok(validateSource0(
    source.replace(
      'TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction',
      'PolynomialTimeFunction.identity',
    ),
  ).includes('function-boundary'));
  assert.ok(validateSource0(
    source.replace(
      'PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold',
      'PolynomialReduction EncodedLockedNANDThreshold EncodedLockedNANDThreshold',
    ),
  ).includes('function-boundary'));
  assert.ok(validateSource0(
    source.replace(
      'EncodedNANDSAT bits ↔',
      'EncodedNANDSAT bits →',
    ),
  ).includes('language-equivalence'));
  assert.ok(validateSource0(
    source.replace(
      'exact buildLockedNANDInstance_correct bits',
      'exact callerCertificate bits',
    ),
  ).includes('caller-certificate'));
  assert.ok(validateSource0(
    `${source}\ndef hostLookup := true\n`,
  ).includes('host-lookup'));
  assert.ok(validateSource0(
    source.replace(
      'strictLockedNANDPolynomialReduction.function.program',
      'PolynomialTimeFunction.identity.program',
    ),
  ).includes('raw-refinement'));
  assert.ok(validateSource0(
    `${source}\ntheorem p_eq_np : True := by trivial\n`,
  ).includes('overclaim'));
  assert.ok(validateSource0(
    `${source}\ntheorem fake : True := by native_decide\n`,
  ).includes('shortcut'));
});
