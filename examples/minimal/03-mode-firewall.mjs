import {
  COORD,
  MODE,
  checkModeUse0,
} from '../../pcc-core.mjs';

import {
  expectCoreErr,
  expectCoreOk,
  printExample,
} from './lib.mjs';

const comparisonUse = checkModeUse0(MODE.QUOT, 'ProjectionDefect');
const passingCase = expectCoreOk(comparisonUse, () => ({
  equalityMode: MODE.QUOT,
  consumer: 'ProjectionDefect',
}));

const constructiveUse = checkModeUse0(MODE.QUOT, 'ReplacementEquality');
const failingCase = expectCoreErr(constructiveUse, {
  coord: COORD.MODE_PROMOTION,
  path: [],
  inspect: (result) => ({
    equalityMode: result.witness.eqMode,
    consumer: result.witness.consumerKind,
  }),
});

printExample({
  id: '03-mode-firewall',
  concept: 'Quotient information may support comparison but not a full-mode replacement',
  humanInput: {
    passing: 'Use a quotient-mode equality only to calculate projection defect.',
    failing: 'Use the same quotient-mode equality as a constructive replacement equality.',
  },
  expectedCertificate: 'The comparison use is accepted; the constructive use rejects with Mode.Promotion.',
  passingCase,
  failingCase,
  proves: 'The core mode-use checker distinguishes declared comparison consumers from consumers requiring full-mode evidence.',
  doesNotProve: 'It does not show that every caller invokes this firewall, that every mode label is correct, or that every full lift and obligation discharge is mathematically sound.',
});
