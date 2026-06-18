import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckBounds0,
  CheckGlobalFirewalls0,
  CheckImportGraph0,
  CheckNoHiddenMin0,
  GLOBAL_FIREWALL_PHASES0,
  makeSyntheticBounds0,
  makeSyntheticGlobalFirewalls0,
  makeSyntheticImportGraph0,
  makeSyntheticNoHiddenMinScan0,
} from '../pcc-global-firewalls0.mjs';

import {
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
} from '../pcc-local-packages0.mjs';

test('CheckGlobalFirewalls0 accepts the synthetic global firewall pack', async () => {
  const out = await CheckGlobalFirewalls0(makeSyntheticGlobalFirewalls0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalFirewalls0');
  assert.equal(out.NF.kind, 'GlobalFirewalls0NF');
  assert.deepEqual(out.NF.phases, GLOBAL_FIREWALL_PHASES0);
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckImportGraph0 accepts the synthetic acyclic import graph', async () => {
  const out = await CheckImportGraph0(makeSyntheticImportGraph0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckImportGraph0');
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
});

test('CheckNoHiddenMin0 accepts the synthetic expanded occurrence scan', async () => {
  const out = await CheckNoHiddenMin0(makeSyntheticNoHiddenMinScan0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckNoHiddenMin0');
  assert.equal(out.NF.kind, 'NoHiddenMin0NF');
});

test('CheckBounds0 accepts the synthetic public schedule bounds', async () => {
  const out = await CheckBounds0(makeSyntheticBounds0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckBounds0');
  assert.equal(out.NF.kind, 'Bounds0NF');
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
});

test('CheckImportGraph0 rejects forbidden O to G import edge', async () => {
  const graph = makeSyntheticImportGraph0();

  graph.edges = [
    ...graph.edges,
    {
      from: 'O',
      to: 'G',
      kind: 'Import',
    },
  ];

  const out = await CheckImportGraph0(graph);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckImportGraph0');
  assert.equal(out.Coord, 'CheckImportGraph0.edges');
  assert.deepEqual(out.Path, ['edges', graph.edges.length - 1]);
  assert.equal(out.Witness.reason, 'ImportGraph contains a forbidden import edge');
});

test('CheckImportGraph0 rejects import cycles', async () => {
  const graph = makeSyntheticImportGraph0();

  graph.edges = [
    ...graph.edges,
    {
      from: 'E',
      to: 'N',
      kind: 'Import',
    },
  ];

  const out = await CheckImportGraph0(graph);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckImportGraph0');
  assert.equal(out.Coord, 'CheckImportGraph0.acyclic');
  assert.deepEqual(out.Path, ['edges', 'cycle']);
  assert.equal(out.Witness.reason, 'ImportGraph0 contains an import cycle');
});

test('CheckNoHiddenMin0 rejects executable minimumEquivalent occurrence', async () => {
  const scan = makeSyntheticNoHiddenMinScan0();

  scan.occurrences = [
    ...scan.occurrences,
    {
      identifier: 'minimumEquivalent',
      expandedIdentifier: 'µ*',
      occurrenceClass: 'ExecCall',
      source: 'bad generated body',
    },
  ];

  const out = await CheckNoHiddenMin0(scan);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckNoHiddenMin0');
  assert.equal(out.Coord, 'CheckNoHiddenMin0.occurrences');
  assert.deepEqual(out.Path, ['occurrences', scan.occurrences.length - 1, 'identifier']);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckNoHiddenMin0 rejects hidden minimization in expanded executable body', async () => {
  const scan = makeSyntheticNoHiddenMinScan0();

  scan.expandedArtifacts = [
    {
      kind: 'ExpandedTemplate0',
      body: [
        'argmin',
      ],
    },
  ];

  const out = await CheckNoHiddenMin0(scan);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckNoHiddenMin0');
  assert.equal(out.Coord, 'CheckNoHiddenMin0.exec');
  assert.deepEqual(out.Path, ['NoHiddenMinScan', 'expandedArtifacts', 0, 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckBounds0 rejects private schedule enlargement', async () => {
  const bounds = makeSyntheticBounds0();
  const index = bounds.families.findIndex((entry) => entry.family === 'G');

  bounds.families[index] = {
    ...bounds.families[index],
    privateSchedule: true,
  };

  const out = await CheckBounds0(bounds);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckBounds0');
  assert.equal(out.Coord, 'CheckBounds0.families');
  assert.deepEqual(out.Path, ['families', index, 'privateSchedule']);
  assert.equal(out.Witness.reason, 'Bounds0 forbids private schedule enlargement');
});

test('CheckBounds0 rejects a bad core schedule constant', async () => {
  const bounds = makeSyntheticBounds0();

  bounds.core = {
    ...bounds.core,
    K0: 513,
  };

  const out = await CheckBounds0(bounds);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckBounds0');
  assert.equal(out.Coord, 'CheckBounds0.core');
  assert.deepEqual(out.Path, ['core', 'K0']);
  assert.equal(out.Witness.reason, 'Bounds0 core constant mismatch');
});

test('CheckGlobalFirewalls0 wraps import graph rejection at the firewall phase coordinate', async () => {
  const pack = makeSyntheticGlobalFirewalls0();

  pack.ImportGraph = {
    ...pack.ImportGraph,
    edges: [
      ...pack.ImportGraph.edges,
      {
        from: 'G',
        to: 'O',
        kind: 'Import',
      },
    ],
  };

  const out = await CheckGlobalFirewalls0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckGlobalFirewalls0.imports');
  assert.deepEqual(out.Path, ['ImportGraph']);
  assert.equal(out.Witness.reason, 'CheckImportGraph0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckImportGraph0.edges');
});