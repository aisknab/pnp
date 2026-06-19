import {
  COORD,
  SORT,
  concatBytes,
  encodeName0,
  makeMinimalBootstrapContext,
  parseTop0,
} from '../../pcc-core.mjs';

import {
  expectCoreErr,
  expectCoreOk,
  printExample,
} from './lib.mjs';

const ctx = makeMinimalBootstrapContext();
const canonicalBytes = encodeName0('review');

const passingCase = expectCoreOk(
  parseTop0(ctx, canonicalBytes, SORT.Name),
  (result) => ({
    parsedKind: result.value.kind,
    parsedValue: result.value.value,
    bytesConsumed: result.state.pos,
  }),
);

const trailingBytes = concatBytes(canonicalBytes, new Uint8Array([0xff]));
const failingCase = expectCoreErr(
  parseTop0(ctx, trailingBytes, SORT.Name),
  {
    coord: COORD.PARSE_TRAILING_BYTES,
    path: [],
    inspect: (result) => ({
      consumed: result.witness.pos,
      supplied: result.witness.limit,
    }),
  },
);

printExample({
  id: '05-canonical-parser',
  concept: 'Top-level certificate bytes must parse canonically and consume the entire input',
  humanInput: {
    passing: 'The canonical encoded UTF-8 name review.',
    failing: 'The same canonical name followed by one unconsumed byte 0xff.',
  },
  expectedCertificate: 'A single Name object with no trailing bytes.',
  passingCase,
  failingCase,
  proves: 'The minimal top-level parser accepts the canonical name and rejects this exact trailing-byte mismatch.',
  doesNotProve: 'It does not prove parser correctness for every record type, canonical-map rule, malformed Unicode case, or full PCCPack byte stream.',
});
