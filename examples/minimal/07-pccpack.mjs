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
    packageKind: record.NF.packageKind,
    phaseCount: record.NF.phaseOrder.length,
    theoremIds: record.NF.theoremIds,
    publicConclusion: record.NF.publicConclusion,
  }),
});

const rejectedPack = makeSyntheticPCCPack0();
rejectedPack.AcceptRun = {
  kind: 'AcceptRun0',
  Verdict: 'accept',
};

const rejectedRecord = await CheckPackSufficiency0(rejectedPack);
const failingCase = expectReject(rejectedRecord, {
  checker: 'CheckPackSufficiency0',
  coord: 'CheckPackSufficiency0.core',
  path: ['AcceptRun'],
  reason: 'PCCPack0 core package must not contain AcceptRun',
});

printExample({
  id: '07-pccpack',
  concept: 'The finite proof-carrying package is checked separately from its acceptance run',
  humanInput: {
    passing: 'A synthetic PCCPack contains the declared core, manifest, kernel, rows, proof DAG, package records, GPack, and final records, but no acceptance run inside the core.',
    failing: 'An AcceptRun record is inserted into the PCCPack core itself.',
  },
  expectedCertificate: 'An accepted PackSufficiency0 normal form with the declared phase order and theorem identifiers.',
  passingCase,
  failingCase,
  proves: 'The current package checker enforces this concrete package/run separation and checks the synthetic package through its configured phases.',
  doesNotProve: 'It does not prove that every accepted phase predicate is mathematically sufficient, that the synthetic package is the sealed release package, or that P = NP.',
});
