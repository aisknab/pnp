import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedFinalCertificate0,
  makeConcreteMaterializedFinalCertificate0,
  summarizeConcreteFinalCertificateChain0,
  writeConcreteMaterializedFinalCertificateFiles0,
} from '../pcc-final-certificate-concrete-materialized0.mjs';

import {
  CheckMaterializedFinalCertificate0,
} from '../pcc-final-certificate-materialized0.mjs';

test('CheckConcreteMaterializedFinalCertificate0 accepts a final certificate over the concrete accept-run chain', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();
  const out = await CheckConcreteMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedFinalCertificate0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);

  assert.equal(out.NF.finalCertificateUsesConcreteAcceptRun, true);
  assert.equal(out.NF.certificatePccPackDigestMatchesConcreteRun, true);
  assert.equal(out.NF.certificateAcceptRunDigestMatchesConcreteRun, true);
  assert.equal(out.NF.certificateFinalVerdictDigestMatchesRecord, true);
  assert.equal(out.NF.publicTheoremMatchesAcceptedFinalVerdict, true);
  assert.equal(out.NF.publicTheorem.consequent, 'P = NP');

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized final certificate accepts the concrete-chain final certificate envelope', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();
  const out = await CheckMaterializedFinalCertificate0(envelope.FinalCertificateEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.NF.kind, 'MaterializedFinalCertificate0NF');
});

test('CheckConcreteMaterializedFinalCertificate0 rejects a non-concrete final-certificate chain summary', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.ConcreteChain = {
    ...envelope.ConcreteChain,
    concreteGlobalProofDAG: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects final certificate accept-run drift', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.FinalCertificateEnvelope = {
    ...envelope.FinalCertificateEnvelope,
    GeneratedAcceptRunEnvelope: {
      ...envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope,
      AcceptRun: {
        ...envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
        RunID: 'drifted-run-id',
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificateEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalCertificateUsesConcreteAcceptRun']);
});

test('CheckConcreteMaterializedFinalCertificate0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.FinalCertificateEnvelope = {
    ...envelope.FinalCertificateEnvelope,
    Certificate: {
      ...envelope.FinalCertificateEnvelope.Certificate,
      ScaffoldWitness: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificateEnvelopeDigest: undefined,
    finalCertificateDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkFinalCertificate: false,
    checkConcreteChain: false,
    checkLinkage: false,
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedFinalCertificateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-final-certificate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedFinalCertificateFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.concreteAcceptRunPath,
    result.files.finalCertificateEnvelopePath,
    result.files.certificatePath,
    result.files.chainPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});
