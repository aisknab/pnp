import {
  CheckPackSufficiency0,
  makeSyntheticPCCPack0,
} from '../../pcc-pack-sufficiency0.mjs';

import {
  expectAccept,
  expectReject,
  printExample,
} from './lib.mjs';

const acceptedPack = makeSyntheticPCCPack0();
const acceptedRecord = await CheckPackSufficiency0(acceptedPack);
const passingCase = expectAccept(acceptedRecord, {
  checker: 'CheckPackSufficiency0',
  inspect: (record) => ({
    zeroSlackSound: record.NF.zeroSlackSound,
    contradictionFromPositiveSlack: record.NF.zeroSlackContradictionFromPositiveSlack,
    finalClosureComplete: record.NF.zeroSlackFinalClosureComplete,
  }),
});

const rejectedPack = makeSyntheticPCCPack0();
rejectedPack.PackSufficiencyTheorem = {
  ...rejectedPack.PackSufficiencyTheorem,
  residualBandMinimization: {
    ...rejectedPack.PackSufficiencyTheorem.residualBandMinimization,
    zeroSlackSound: false,
  },
};

const rejectedRecord = await CheckPackSufficiency0(rejectedPack);
const failingCase = expectReject(rejectedRecord, {
  checker: 'CheckPackSufficiency0',
  coord: 'CheckPackSufficiency0.PackSufficiencyTheorem',
  path: ['PackSufficiencyTheorem', 'residualBandMinimization', 'zeroSlackSound'],
  reason: 'residualBandMinimization must certify zeroSlackSound',
});

printExample({
  id: '06-zero-slack',
  concept: 'ZeroSlack is a terminal exactness obligation, not a bare status token',
  humanInput: {
    passing: 'The synthetic package presents the full residual-band theorem record, including zeroSlackSound and the positive-slack contradiction fields.',
    failing: 'The identical theorem record changes zeroSlackSound to false.',
  },
  expectedCertificate: 'An accepted package-sufficiency normal form with ZeroSlack soundness, positive-slack contradiction, and final closure all recorded as true.',
  passingCase,
  failingCase,
  proves: 'The package-sufficiency checker requires the named ZeroSlack soundness field and exposes a precise rejection when it is false.',
  doesNotProve: 'It does not independently derive the ZeroSlack contradiction, prove route completeness, or show that the assertion-shaped theorem fields have sound underlying proofs.',
});
