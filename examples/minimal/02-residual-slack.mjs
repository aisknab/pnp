import {
  CheckFinalFrameworkMatch0,
  CheckSATDecision0,
  makeSyntheticFinalFrameworkMatch0,
  makeSyntheticSATDecision0,
} from '../../pcc-final-framework0.mjs';

import {
  expectAccept,
  expectReject,
  printExample,
} from './lib.mjs';

const framework = makeSyntheticFinalFrameworkMatch0();
const frameworkRecord = await CheckFinalFrameworkMatch0(framework);
const frameworkPass = expectAccept(frameworkRecord, {
  checker: 'CheckFinalFrameworkMatch0',
  inspect: (record) => ({
    baseline: record.NF.baseline,
    fullWordSize: record.NF.fullWordSize,
  }),
});

const decision = makeSyntheticSATDecision0();
const decisionRecord = await CheckSATDecision0(decision);
const decisionPass = expectAccept(decisionRecord, {
  checker: 'CheckSATDecision0',
  inspect: (record) => ({
    baseline: record.NF.baseline,
    fullWordSize: record.NF.fullWordSize,
    comparator: record.NF.comparator,
  }),
});

const badFramework = makeSyntheticFinalFrameworkMatch0();
badFramework.SlackMap = {
  ...badFramework.SlackMap,
  lockedResidualSlackMax: 5,
};

const badRecord = await CheckFinalFrameworkMatch0(badFramework);
const failingCase = expectReject(badRecord, {
  checker: 'CheckFinalFrameworkMatch0',
  coord: 'CheckFinalFrameworkMatch0.slack',
  path: ['SlackMap', 'lockedResidualSlackMax'],
  reason: 'locked residual slack must be an integer at most four',
});

printExample({
  id: '02-residual-slack',
  concept: 'Residual slack and the exact SAT threshold comparator',
  humanInput: {
    passing: 'The locked word has size baseline + 4, both packages use Lambda(C)=|C|-mu(C), and SAT is decided by exact minimum size > baseline.',
    failing: 'The framework record claims the locked residual-slack bound is 5 instead of at most 4.',
  },
  expectedCertificate: 'Accepted framework and SAT-decision normal forms using the same exact minimum notion, residual definition, and minSize>baseline comparator.',
  passingCase: {
    framework: frameworkPass,
    satDecision: decisionPass,
  },
  failingCase,
  proves: 'The current framework checker enforces the displayed residual-slack bound and the SAT-decision checker records the exact threshold comparator.',
  doesNotProve: 'It does not independently compute mu(C), prove Lambda(W_phi)<=4, or prove that the threshold characterizes SAT.',
});
