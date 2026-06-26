import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckFinal0 } from '../pcc-final0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeFinalTheorem0() {
  const surfaces = makeFinalPrefixSurfaces0();
  return {
    ...surfaces.PCCPack.FinalTheorem,
    NoHiddenMinCert: {
      ...surfaces.PCCPack.FinalTheorem.NoHiddenMinCert,
      occurrences: surfaces.PCCPack.FinalTheorem.NoHiddenMinCert.occurrences.map(
        (entry) => (entry.identifier === 'PCCMin'
          ? { ...entry, occurrenceClass: 'AssumeOnly' }
          : entry),
      ),
    },
  };
}

test('diagnose CheckFinal0 acceptance for phase 39 fixture', async () => {
  const record = await CheckFinal0(makeFinalTheorem0());
  assert.equal(
    record.tag,
    'accept',
    JSON.stringify({ coord: record.Coord, path: record.Path, witness: record.Witness }),
  );
});
