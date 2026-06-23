import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from '../pcc-global-infrastructure-semantic0.mjs';

import {
  makeSyntheticRowPack0,
} from '../pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from '../pcc-gpack0.mjs';

import {
  CheckGlobalRowSemantic0,
  makeGlobalRowSemanticInput0,
  makeGlobalRowSemanticSuite0,
} from '../pcc-global-row-semantic0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticFiniteRelJudgment0,
  makeSemanticFiniteRelClaim0,
  makeSemanticFiniteRelDomain0,
  makeSemanticFiniteRelNode0,
  makeSemanticFiniteRelProgram0,
  makeSemanticFiniteRelSpec0,
  makeSemanticFiniteRelTuple0,
} from '../pcc-kernel-finiterel-semantic0.mjs';

function makeFiniteRelProof0() {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const literal = makeSemanticFiniteRelNode0({
    index: 0,
    id: 'R',
    op: 'literal',
    domainIds: ['D', 'D'],
    tuples: [makeSemanticFiniteRelTuple0({ index: 0, values: ['a', 'b'] })],
  });
  const closure = makeSemanticFiniteRelNode0({
    index: 1,
    id: 'R.rtc',
    op: 'reflexive-transitive-closure',
    domainIds: ['D', 'D'],
    inputIds: ['R'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'global.rows.semantic.program',
