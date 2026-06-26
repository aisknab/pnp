import crypto from 'node:crypto';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;
const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));

export const DOCUMENTATION_REVISION_COORDINATE0 =
  'urn:pnp:documentation-revision:phase40:2026-06-26:01';

export const DOCUMENTATION_REVISION_ROOT0 =
  'documentation-revisions/phase40-2026-06-26-01';

export const DOCUMENTATION_REVISION_REPOSITORY0 =
  'https://github.com/aisknab/pnp';

export const DOCUMENTATION_REVISION_REVIEW_LEDGER0 =
  'https://github.com/aisknab/pnp/issues/13';

export const DOCUMENTATION_REVISION_TEX_SHA2560 =
  'b64bc0a8c1ad948ec6b1a83496bb686695a6ac59bc446da7848798259491b097';

export const DOCUMENTATION_REVISION_PDF_SHA2560 =
  'af59afad26cb2651c5506afe806cb452e2bb9b3a2609c10f50fa46a64d505492';

export const DOCUMENTATION_REVISION_MANIFEST_SHA2560 =
  '09b3ad406515fe03990879cbf8325dc555f99501d11791c43ee6492781d87b96';

export const DOCUMENTATION_REVISION_README_SHA2560 =
  '4bf4a1fe9376946a9cf8eff5207f550a338ddbc7e3b33c0c0123f4277eeede38';

export const DOCUMENTATION_REVISION_CHECKSUM_LEDGER_SHA2560 =
  '61e9365cc28ac4ba1133f538c9b7633a84f465af3daa79bce470ab0846ecf51c';

export const DOCUMENTATION_REVISION_DETACHED_FILE_SHA2560 =
  'ac117c6165e099bcd0a101f05fd9163433b73bd82d64b8c675512ecbedae31ff';

export const DOCUMENTATION_REVISION_FILES0 = Object.freeze([
  'canonical_proof_report.tex',
  'canonical_proof_report.pdf',
  'documentation-coordinate.json',
  'README.md',
  'SHA256SUMS',
  'SHA256SUMS.sha256',
]);

export const DOCUMENTATION_REVISION_POLICY0 = Object.freeze({
  kind: 'PNPDocumentationRevisionPolicy0',
  version: CHECKER_VERSION,
  exactImmutableCoordinateRequired: true,
  exactRevisionRootRequired: true,
  texAndPdfHashesRequired: true,
  manifestHashRequired: true,
  checksumLedgerRequired: true,
  detachedChecksumRequired: true,
  directProofWordingForbidden: true,
  publicRepositoryAccessRequired: true,
  emailAccessRequestForbidden: true,
  checkerRelativeClaimBoundaryRequired: true,
  sealedReleaseMustRemainUnchanged: true,
  publicTheoremEmissionMustRemainDisabled: true,
  unrestrictedTheoremSoundnessMustRemainUnclaimed: true,
  callerReadinessAssertionsForbidden: true,
});

export function makeDocumentationRevisionInput0({
  Root = DOCUMENTATION_REVISION_ROOT0,
  ExpectedCoordinate = DOCUMENTATION_REVISION_COORDINATE0,
  ExpectedTexSHA256 = DOCUMENTATION_REVISION_TEX_SHA2560,
  ExpectedPdfSHA256 = DOCUMENTATION_REVISION_PDF_SHA2560,
  ExpectedManifestSHA256 = DOCUMENTATION_REVISION_MANIFEST_SHA2560,
  ExpectedReadmeSHA256 = DOCUMENTATION_REVISION_README_SHA2560,
  ExpectedChecksumLedgerSHA256 =
    DOCUMENTATION_REVISION_CHECKSUM_LEDGER_SHA2560,
  ExpectedDetachedFileSHA256 =
    DOCUMENTATION_REVISION_DETACHED_FILE_SHA2560,
} = {}) {
  return Object.freeze({
    kind: 'PNPDocumentationRevisionInput0',
    version: CHECKER_VERSION,
    Root,
    ExpectedCoordinate,
    ExpectedTexSHA256,
    ExpectedPdfSHA256,
    ExpectedManifestSHA256,
    ExpectedReadmeSHA256,
    ExpectedChecksumLedgerSHA256,
    ExpectedDetachedFileSHA256,
    Policy: { ...DOCUMENTATION_REVISION_POLICY0 },
  });
}

export async function CheckDocumentationRevisionCoordinate0(input) {
  const checker = 'CheckDocumentationRevisionCoordinate0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const rootResolution = resolveRevisionRoot0(input.Root);
  ledger.push(makeLedgerEntry0(
    'rootResolution',
    rootResolution.ok,
    rootResolution.nf ?? rootResolution.witness,
  ));
  if (!rootResolution.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.root`,
      rootResolution,
      ledger,
    );
  }

  const read = await readRevisionFiles0(rootResolution.nf.absoluteRoot);
  ledger.push(makeLedgerEntry0('readFiles', read.ok, read.nf ?? read.witness));
  if (!read.ok) {
    return makeRejectFromValidation0(checker, `${checker}.files`, read, ledger);
  }

  const manifestResult = parseAndValidateManifest0(
    read.nf.buffers['documentation-coordinate.json'],
    input.ExpectedCoordinate,
  );
  ledger.push(makeLedgerEntry0(
    'manifest',
    manifestResult.ok,
    manifestResult.nf ?? manifestResult.witness,
  ));
  if (!manifestResult.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.manifest`,
      manifestResult,
      ledger,
    );
  }

  const hashes = validateFileHashes0(
    read.nf.buffers,
    manifestResult.nf.manifest,
    input,
  );
  ledger.push(makeLedgerEntry0('fileHashes', hashes.ok, hashes.nf ?? hashes.witness));
  if (!hashes.ok) {
    return makeRejectFromValidation0(checker, `${checker}.hashes`, hashes, ledger);
  }

  const checksum = validateChecksumLedger0(read.nf.buffers, hashes.nf);
  ledger.push(makeLedgerEntry0(
    'checksumLedger',
    checksum.ok,
    checksum.nf ?? checksum.witness,
  ));
  if (!checksum.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.checksumLedger`,
      checksum,
      ledger,
    );
  }

  const content = validateRevisionContent0(
    read.nf.buffers,
    manifestResult.nf.manifest,
  );
  ledger.push(makeLedgerEntry0(
    'contentBoundary',
    content.ok,
    content.nf ?? content.witness,
  ));
  if (!content.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.content`,
      content,
      ledger,
    );
  }

  const manifest = manifestResult.nf.manifest;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'PNPDocumentationRevisionCoordinate0NF',
      checker,
      version: CHECKER_VERSION,
      documentationRevisionAccepted: true,
      immutableDocumentationCoordinateReady: true,
      documentationCoordinate: manifest.coordinate,
      revisionId: manifest.revisionId,
      revisionRoot: input.Root,

      texPath: manifest.files.tex.path,
      pdfPath: manifest.files.pdf.path,
      texDigest: digestRecord0(hashes.nf.actual.tex),
      pdfDigest: digestRecord0(hashes.nf.actual.pdf),
      manifestDigest: digestRecord0(hashes.nf.actual.manifest),
      readmeDigest: digestRecord0(hashes.nf.actual.readme),
      checksumLedgerDigest: digestRecord0(hashes.nf.actual.checksumLedger),
      detachedChecksumDigest: digestRecord0(hashes.nf.actual.detached),
      texBytes: read.nf.buffers['canonical_proof_report.tex'].byteLength,
      pdfBytes: read.nf.buffers['canonical_proof_report.pdf'].byteLength,

      sourceRepository: manifest.repository,
      reviewLedger: manifest.reviewLedger,
      publicSourceAccessCorrected: true,
      emailAccessRequestRequired: false,
      directProofWordingRemoved: true,
      checkerRelativeClaimBoundaryExplicit: true,

      parentSealedSourceTag: manifest.parentSealedSourceTag,
      parentSealedArtifactTag: manifest.parentSealedArtifactTag,
      parentSealedSourceCommit: manifest.parentSealedSourceCommit,
      sealedReleasePreserved: true,
      sealedReleaseOverwritten: false,

      boundedSemanticNodeCoverageReady: true,
      unrestrictedTheoremSoundnessEstablished: false,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionAllowed: false,
      documentationOnlySuccessor: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'documentation revision input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'PNPDocumentationRevisionInput0') {
    return validationReject0(
      ['kind'],
      'documentation revision input kind must be PNPDocumentationRevisionInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `documentation revision input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'Root',
    'ExpectedCoordinate',
    'ExpectedTexSHA256',
    'ExpectedPdfSHA256',
    'ExpectedManifestSHA256',
    'ExpectedReadmeSHA256',
    'ExpectedChecksumLedgerSHA256',
    'ExpectedDetachedFileSHA256',
    'Policy',
  ]);
  for (const field of allowed) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'documentation revision input is missing a required field',
        { field },
      );
    }
  }
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'documentation revision checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (input.Root !== DOCUMENTATION_REVISION_ROOT0) {
    return validationReject0(
      ['Root'],
      'documentation revision root must be the immutable phase-40 revision path',
      { expected: DOCUMENTATION_REVISION_ROOT0, actual: input.Root },
    );
  }
  if (input.ExpectedCoordinate !== DOCUMENTATION_REVISION_COORDINATE0) {
    return validationReject0(
      ['ExpectedCoordinate'],
      'documentation revision coordinate must match the immutable phase-40 coordinate',
      {
        expected: DOCUMENTATION_REVISION_COORDINATE0,
        actual: input.ExpectedCoordinate,
      },
    );
  }
  const expectedHashes = {
    ExpectedTexSHA256: DOCUMENTATION_REVISION_TEX_SHA2560,
    ExpectedPdfSHA256: DOCUMENTATION_REVISION_PDF_SHA2560,
    ExpectedManifestSHA256: DOCUMENTATION_REVISION_MANIFEST_SHA2560,
    ExpectedReadmeSHA256: DOCUMENTATION_REVISION_README_SHA2560,
    ExpectedChecksumLedgerSHA256:
      DOCUMENTATION_REVISION_CHECKSUM_LEDGER_SHA2560,
    ExpectedDetachedFileSHA256:
      DOCUMENTATION_REVISION_DETACHED_FILE_SHA2560,
  };
  for (const [field, expected] of Object.entries(expectedHashes)) {
    if (input[field] !== expected || !isHexDigest0(input[field])) {
      return validationReject0(
        [field],
        'documentation revision expected hash must match its immutable phase-40 value',
        { field, expected, actual: input[field] },
      );
    }
  }
  if (!sameCanonical0(input.Policy, DOCUMENTATION_REVISION_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'documentation revision policy must match the fail-closed policy',
      { expected: DOCUMENTATION_REVISION_POLICY0, actual: input.Policy },
    );
  }
  return validationAccept0({
    kind: 'PNPDocumentationRevisionInputShape0NF',
  });
}

function resolveRevisionRoot0(root) {
  const absoluteRoot = path.resolve(MODULE_DIR, root);
  const expectedRoot = path.resolve(MODULE_DIR, DOCUMENTATION_REVISION_ROOT0);
  if (absoluteRoot !== expectedRoot) {
    return validationReject0(
      ['Root'],
      'documentation revision root resolves outside the immutable phase-40 coordinate',
      { expectedRoot, absoluteRoot },
    );
  }
  return validationAccept0({
    kind: 'PNPDocumentationRevisionRoot0NF',
    absoluteRoot,
  });
}

async function readRevisionFiles0(absoluteRoot) {
  const buffers = {};
  try {
    for (const filename of DOCUMENTATION_REVISION_FILES0) {
      buffers[filename] = await fs.readFile(path.join(absoluteRoot, filename));
    }
  } catch (error) {
    return validationReject0(
      ['Root'],
      'documentation revision file set is incomplete or unreadable',
      {
        errorName: error?.name ?? null,
        errorCode: error?.code ?? null,
        errorMessage: error?.message ?? String(error),
      },
    );
  }
  return validationAccept0({
    kind: 'PNPDocumentationRevisionFiles0NF',
    buffers,
    filenames: [...DOCUMENTATION_REVISION_FILES0],
  });
}

function parseAndValidateManifest0(buffer, expectedCoordinate) {
  let manifest;
  try {
    manifest = JSON.parse(buffer.toString('utf8'));
  } catch (error) {
    return validationReject0(
      ['documentation-coordinate.json'],
      'documentation coordinate manifest must be valid JSON',
      { errorMessage: error?.message ?? String(error) },
    );
  }
  if (!isPlainObject0(manifest)
      || manifest.kind !== 'PNPDocumentationRevisionCoordinate0'
      || manifest.version !== CHECKER_VERSION
      || manifest.coordinate !== expectedCoordinate
      || manifest.revisionId !== 'phase40-2026-06-26-01'
      || manifest.status !== 'documentation-revision') {
    return validationReject0(
      ['documentation-coordinate.json'],
      'documentation coordinate manifest identity mismatch',
      { actual: manifest },
    );
  }
  const expectedCustody = {
    repository: DOCUMENTATION_REVISION_REPOSITORY0,
    reviewLedger: DOCUMENTATION_REVISION_REVIEW_LEDGER0,
    parentSealedSourceTag: 'final-pnp-proof-report-hardened-7072f8d',
    parentSealedArtifactTag:
      'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
    parentSealedSourceCommit:
      '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
    sealedReleaseOverwritten: false,
  };
  for (const [field, expected] of Object.entries(expectedCustody)) {
    if (manifest[field] !== expected) {
      return validationReject0(
        ['documentation-coordinate.json', field],
        'documentation coordinate custody field mismatch',
        { field, expected, actual: manifest[field] },
      );
    }
  }
  const expectedBoundary = {
    corrections: {
      directProofWordingRemoved: true,
      publicSourceAccessCorrected: true,
      emailAccessRequestRequired: false,
      checkerRelativeClaimBoundaryExplicit: true,
    },
    semanticBoundary: {
      predecessorPhase: 39,
      boundedSemanticNodeCoverageReady: true,
      unrestrictedTheoremSoundnessEstablished: false,
      publicTheoremEmissionAllowed: false,
    },
  };
  if (!sameCanonical0(manifest.corrections, expectedBoundary.corrections)
      || !sameCanonical0(
        manifest.semanticBoundary,
        expectedBoundary.semanticBoundary,
      )) {
    return validationReject0(
      ['documentation-coordinate.json'],
      'documentation coordinate correction or semantic boundary mismatch',
      { expected: expectedBoundary, actual: manifest },
    );
  }
  if (manifest.files?.tex?.path !== 'canonical_proof_report.tex'
      || manifest.files?.pdf?.path !== 'canonical_proof_report.pdf'
      || !isHexDigest0(manifest.files?.tex?.sha256)
      || !isHexDigest0(manifest.files?.pdf?.sha256)) {
    return validationReject0(
      ['documentation-coordinate.json', 'files'],
      'documentation coordinate manifest must bind TeX and PDF paths and hashes',
      { actual: manifest.files },
    );
  }
  return validationAccept0({
    kind: 'PNPDocumentationRevisionManifest0NF',
    manifest,
  });
}

function validateFileHashes0(buffers, manifest, input) {
  const actual = {
    tex: sha256Hex0(buffers['canonical_proof_report.tex']),
    pdf: sha256Hex0(buffers['canonical_proof_report.pdf']),
    manifest: sha256Hex0(buffers['documentation-coordinate.json']),
    readme: sha256Hex0(buffers['README.md']),
    checksumLedger: sha256Hex0(buffers.SHA256SUMS),
    detached: sha256Hex0(buffers['SHA256SUMS.sha256']),
  };
  const expected = {
    tex: input.ExpectedTexSHA256,
    pdf: input.ExpectedPdfSHA256,
    manifest: input.ExpectedManifestSHA256,
    readme: input.ExpectedReadmeSHA256,
    checksumLedger: input.ExpectedChecksumLedgerSHA256,
    detached: input.ExpectedDetachedFileSHA256,
  };
  for (const key of Object.keys(expected)) {
    if (actual[key] !== expected[key]) {
      return validationReject0(
        ['hashes', key],
        'documentation revision file hash mismatch',
        { key, expected: expected[key], actual: actual[key] },
      );
    }
  }
  if (manifest.files.tex.sha256 !== actual.tex
      || manifest.files.pdf.sha256 !== actual.pdf) {
    return validationReject0(
      ['documentation-coordinate.json', 'files'],
      'documentation coordinate manifest TeX/PDF hashes do not match the files',
      {
        manifestTex: manifest.files.tex.sha256,
        actualTex: actual.tex,
        manifestPdf: manifest.files.pdf.sha256,
        actualPdf: actual.pdf,
      },
    );
  }
  return validationAccept0({
    kind: 'PNPDocumentationRevisionHashes0NF',
    actual,
  });
}

function validateChecksumLedger0(buffers, hashesNF) {
  const expectedLedger = [
    `${hashesNF.actual.tex}  canonical_proof_report.tex`,
    `${hashesNF.actual.pdf}  canonical_proof_report.pdf`,
    `${hashesNF.actual.manifest}  documentation-coordinate.json`,
    `${hashesNF.actual.readme}  README.md`,
    '',
  ].join('\n');
  const actualLedger = buffers.SHA256SUMS.toString('utf8');
  if (actualLedger !== expectedLedger) {
    return validationReject0(
      ['SHA256SUMS'],
      'documentation revision checksum ledger mismatch',
      { expectedLedger, actualLedger },
    );
  }
  const expectedDetached = `${hashesNF.actual.checksumLedger}  SHA256SUMS\n`;
  const actualDetached = buffers['SHA256SUMS.sha256'].toString('utf8');
  if (actualDetached !== expectedDetached) {
    return validationReject0(
      ['SHA256SUMS.sha256'],
      'documentation revision detached checksum mismatch',
      { expectedDetached, actualDetached },
    );
  }
  return validationAccept0({
    kind: 'PNPDocumentationRevisionChecksumLedger0NF',
    checksumLedgerDigest: digestRecord0(hashesNF.actual.checksumLedger),
    detachedChecksumDigest: digestRecord0(hashesNF.actual.detached),
  });
}

function validateRevisionContent0(buffers, manifest) {
  const tex = buffers['canonical_proof_report.tex'].toString('utf8');
  const readme = buffers['README.md'].toString('utf8');
  const pdf = buffers['canonical_proof_report.pdf'];

  const forbiddenTex = [
    'This paper proves',
    'Complete machine-checkable proof report.',
    'review@pnplabs.com.au',
    'If repository access is restricted',
    'Review, source-access, and artefact-access requests should be sent',
  ];
  for (const phrase of forbiddenTex) {
    if (tex.includes(phrase)) {
      return validationReject0(
        ['canonical_proof_report.tex'],
        'documentation revision retains forbidden publication wording or obsolete source-access instructions',
        { forbiddenPhrase: phrase },
      );
    }
  }

  const requiredTex = [
    manifest.coordinate,
    DOCUMENTATION_REVISION_REPOSITORY0,
    DOCUMENTATION_REVISION_REVIEW_LEDGER0,
    'Documentation Revision Notice',
    'does not state that \\(P=NP\\) has been independently established',
    'public theorem emission remains disabled',
    'preserves the sealed source/checker and artefact releases as immutable historical objects',
  ];
  for (const phrase of requiredTex) {
    if (!tex.includes(phrase)) {
      return validationReject0(
        ['canonical_proof_report.tex'],
        'documentation revision is missing required claim-boundary or public-access wording',
        { requiredPhrase: phrase },
      );
    }
  }

  const requiredReadme = [
    manifest.coordinate,
    DOCUMENTATION_REVISION_REPOSITORY0,
    DOCUMENTATION_REVISION_REVIEW_LEDGER0,
    'does not activate public theorem emission',
    'does not overwrite or retag either historical release',
  ];
  for (const phrase of requiredReadme) {
    if (!readme.includes(phrase)) {
      return validationReject0(
        ['README.md'],
        'documentation revision README is missing immutable-custody or public-access wording',
        { requiredPhrase: phrase },
      );
    }
  }

  if (pdf.byteLength < 8 || pdf.subarray(0, 5).toString('ascii') !== '%PDF-') {
    return validationReject0(
      ['canonical_proof_report.pdf'],
      'documentation revision PDF must be a nonempty PDF file',
      { prefix: pdf.subarray(0, 8).toString('ascii') },
    );
  }

  return validationAccept0({
    kind: 'PNPDocumentationRevisionContentBoundary0NF',
    directProofWordingRemoved: true,
    publicSourceAccessCorrected: true,
    emailAccessRequestRequired: false,
    checkerRelativeClaimBoundaryExplicit: true,
    sealedReleasePreserved: true,
    publicTheoremEmissionAllowed: false,
  });
}

function sha256Hex0(buffer) {
  return crypto.createHash('sha256').update(buffer).digest('hex');
}

function digestRecord0(hex) {
  return Object.freeze({ alg: 'SHA256', hex });
}

function isHexDigest0(value) {
  return typeof value === 'string' && /^[0-9a-f]{64}$/u.test(value);
}

function makeLedgerEntry0(phase, ok, material) {
  return {
    phase,
    status: ok ? 'pass' : 'fail',
    digest: digestCanonical0(material ?? null),
  };
}

function makeAcceptRecord0({ checker, nf, ledger }) {
  const digest = digestCanonical0(nf);
  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectFromValidation0(checker, coord, result, ledger) {
  return makeRejectRecord0({
    checker,
    coord,
    path: result.path,
    witness: result.witness,
    ledger,
  });
}

function makeRejectRecord0({ checker, coord, path: rejectPath, witness, ledger }) {
  const nf = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path: rejectPath,
    witness,
    ledger,
  };
  const digest = digestCanonical0(nf);
  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: rejectPath,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path: rejectPath,
    witness,
    digest,
    ledger,
  };
}

function validationAccept0(nf) {
  return { ok: true, nf };
}

function validationReject0(rejectPath, reason, details = {}) {
  return {
    ok: false,
    path: rejectPath,
    witness: {
      reason,
      ...(details ?? {}),
    },
  };
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
