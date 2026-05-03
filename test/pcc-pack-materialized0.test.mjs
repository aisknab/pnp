import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedPCCPack0,
  makeMaterializedPCCPack0,
  writeMaterializedPCCPackFiles0,
} from '../pcc-pack-materialized0.mjs';

import {
  CheckPackSufficiency0,
  PACK_SUFFICIENCY_PHASES0,
} from '../pcc-pack-sufficiency0.mjs';

test('CheckMaterializedPCCPack0 accepts a materialized PCCPack envelope', async () => {
  const envelope = await makeMaterializedPCCPack0();
  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.NF.kind, 'MaterializedPCCPack0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.checkPCCPackChecker, 'CheckPCCPackexp');
  assert.deepEqual(out.NF.phaseOrder, PACK_SUFFICIENCY_PHASES0);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckPackSufficiency0 accepts the materialized PCCPack core', async () => {
  const envelope = await makeMaterializedPCCPack0();
  const out = await CheckPackSufficiency0(envelope.PCCPack);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPackSufficiency0');
  assert.equal(out.NF.kind, 'PackSufficiency0NF');
  assert.deepEqual(out.NF.phaseOrder, PACK_SUFFICIENCY_PHASES0);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});

test('CheckMaterializedPCCPack0 exposes pack-sufficiency checker failures', async () => {
  const envelope = await makeMaterializedPCCPack0();

  envelope.PCCPack = {
    ...envelope.PCCPack,
    HardCheck: {
      ...envelope.PCCPack.HardCheck,
      HashCheck: {
        ...envelope.PCCPack.HardCheck.HashCheck,
        fullKeyCompareAfterHash: false,
        canonicalByteCompareAfterHash: false,
      },
    },
  };

  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPack0.CheckPackSufficiency0');
  assert.equal(out.Witness.detail.inner.coord, 'CheckPackSufficiency0.HardCheck');
});

test('CheckMaterializedPCCPack0 rejects component-envelope mismatch', async () => {
  const envelope = await makeMaterializedPCCPack0();

  envelope.PCCPack = {
    ...envelope.PCCPack,
    RowPack: {
      ...envelope.PCCPack.RowPack,
      SchedHash: {
        alg: 'SHA256',
        hex: '0000000000000000000000000000000000000000000000000000000000000000',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    pccPackDigest: undefined,
    rowPackDigest: undefined,
  };

  const out = await CheckMaterializedPCCPack0(envelope, {
    checkPackSufficiency: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPack0.linkage');
  assert.deepEqual(out.Path, ['PCCPack', 'rowPack']);
});

test('CheckMaterializedPCCPack0 rejects forbidden fixture marker text', async () => {
  const envelope = await makeMaterializedPCCPack0();

  envelope.PCCPack = {
    ...envelope.PCCPack,
    PackSufficiencyTheorem: {
      ...envelope.PCCPack.PackSufficiencyTheorem,
      PiPackSufficiency: {
        ...envelope.PCCPack.PackSufficiencyTheorem.PiPackSufficiency,
        note: 'todo marker must reject',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    pccPackDigest: undefined,
  };

  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPack0.fixtureMarkers');
});

test('CheckMaterializedPCCPack0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeMaterializedPCCPack0();

  envelope.PCCPack = {
    ...envelope.PCCPack,
    PackSufficiencyTheorem: {
      ...envelope.PCCPack.PackSufficiencyTheorem,
      PiPackSufficiency: {
        ...envelope.PCCPack.PackSufficiencyTheorem.PiPackSufficiency,
        note: 'synthetic marker must reject in strict marker mode',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    pccPackDigest: undefined,
  };

  const out = await CheckMaterializedPCCPack0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPack0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('CheckMaterializedPCCPack0 rejects stale linkage digest', async () => {
  const envelope = await makeMaterializedPCCPack0();

  envelope.Linkage = {
    ...envelope.Linkage,
    pccPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPack0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'pccPackDigest']);
});

test('writeMaterializedPCCPackFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-pcc-pack-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedPCCPackFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.pccPackPath,
    result.files.corePath,
    result.files.manifestPath,
    result.files.theoremPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('makeMaterializedPCCPack0 uses concrete materialized rows by default', async () => {
  const envelope = await makeMaterializedPCCPack0();

  assert.equal(envelope.RowsEnvelope.kind, 'ConcreteMaterializedRows0');
  assert.equal(envelope.RowsEnvelope.RowPack.kind, 'RowPack0');
  assert.equal(envelope.PCCPack.RowPack.IfaceHash.hex, envelope.RowsEnvelope.RowPack.IfaceHash.hex);
  assert.equal(envelope.PCCPack.RowPack.SchedHash.hex, envelope.RowsEnvelope.RowPack.SchedHash.hex);
  assert.equal(envelope.PCCPack.RowPack.Rows.some((row) => row.IfaceHash === 'IfaceDict0.synthetic'), false);

  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.NF.rowsEnvelopeKind, 'ConcreteMaterializedRows0');
  assert.equal(out.NF.concreteRows, true);
});

test('makeMaterializedPCCPack0 uses concrete materialized local packages by default', async () => {
  const envelope = await makeMaterializedPCCPack0();

  assert.equal(envelope.LocalPackagesEnvelope.kind, 'ConcreteMaterializedLocalPackages0');
  assert.equal(envelope.LocalPackagesEnvelope.ConcreteRowsEnvelope.kind, 'ConcreteMaterializedRows0');
  assert.equal(envelope.PCCPack.LocalPackages.RowPackDigest.hex, envelope.PCCPack.RowPack ? envelope.LocalPackagesEnvelope.RowPack ? envelope.LocalPackagesEnvelope.RowPackDigest?.hex ?? envelope.LocalPackagesEnvelope.Linkage.rowPackDigest.hex : envelope.LocalPackagesEnvelope.Linkage.rowPackDigest.hex : envelope.LocalPackagesEnvelope.Linkage.rowPackDigest.hex);

  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.NF.localPackagesEnvelopeKind, 'ConcreteMaterializedLocalPackages0');
  assert.equal(out.NF.concreteLocalPackages, true);
});

test('makeMaterializedPCCPack0 uses concrete materialized global firewalls by default', async () => {
  const envelope = await makeMaterializedPCCPack0();

  assert.equal(envelope.GlobalFirewallsEnvelope.kind, 'ConcreteMaterializedGlobalFirewalls0');
  assert.equal(envelope.GlobalFirewallsEnvelope.ConcreteLocalPackagesEnvelope.kind, 'ConcreteMaterializedLocalPackages0');
  assert.deepEqual(envelope.PCCPack.GlobalFirewalls.SchedHash, envelope.GlobalFirewallsEnvelope.GlobalFirewalls.SchedHash);
  assert.deepEqual(envelope.PCCPack.GlobalFirewalls.IfaceHash, envelope.GlobalFirewallsEnvelope.GlobalFirewalls.IfaceHash);

  const out = await CheckMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
  assert.equal(out.NF.globalFirewallsEnvelopeKind, 'ConcreteMaterializedGlobalFirewalls0');
  assert.equal(out.NF.concreteGlobalFirewalls, true);
});
