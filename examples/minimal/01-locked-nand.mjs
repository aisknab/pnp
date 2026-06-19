import {
  CheckGPack0,
  makeSyntheticGPack0,
} from '../../pcc-gpack0.mjs';

import {
  expectAccept,
  expectReject,
  printExample,
} from './lib.mjs';

const acceptedInput = makeSyntheticGPack0();
const acceptedRecord = await CheckGPack0(acceptedInput);
const passingCase = expectAccept(acceptedRecord, {
  checker: 'CheckGPack0',
  inspect: (record) => ({
    gateCount: record.NF.gateCount,
    baseline: record.NF.baseline,
    fullWordSize: record.NF.fullWordSize,
    residualSlackMax: record.NF.residualSlackMax,
  }),
});

const rejectedInput = makeSyntheticGPack0();
rejectedInput.SlotAlloc = {
  ...rejectedInput.SlotAlloc,
  families: {
    ...rejectedInput.SlotAlloc.families,
    O: [
      rejectedInput.SlotAlloc.families.X[0],
      ...rejectedInput.SlotAlloc.families.O.slice(1),
    ],
  },
};

const rejectedRecord = await CheckGPack0(rejectedInput);
const failingCase = expectReject(rejectedRecord, {
  checker: 'CheckGPack0',
  coord: 'CheckGPack0.slotAlloc',
  path: ['SlotAlloc', 'families', 'O', 0],
  reason: 'SlotAlloc slots must be globally unique',
});

printExample({
  id: '01-locked-nand',
  concept: 'Locked NAND slot separation and threshold record',
  humanInput: {
    passing: 'The synthetic two-gate NAND source uses disjoint X, T, O, R, L, and z slot families.',
    failing: 'The first occurrence slot O[0] is replaced with the primary-input slot X[0].',
  },
  expectedCertificate: 'An accepted GPack0 normal form with fullWordSize = baseline + 4 and residualSlackMax = 4.',
  passingCase,
  failingCase,
  proves: 'The current CheckGPack0 implementation accepts the synthetic GPack and rejects this explicit cross-family slot collision at a named coordinate.',
  doesNotProve: 'It does not prove SAT preservation, baseline distinctness, or the locked-NAND threshold theorem for all inputs.',
});
