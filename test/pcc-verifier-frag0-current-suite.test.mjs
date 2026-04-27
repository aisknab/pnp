import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckVerifierFrag0,
  makeAcceptCase,
  makeRejectCase,
} from '../pcc-verifier-frag0.mjs';

import {
  Parse0,
  Encode0,
  DigestObject0,
  ComputeRowKey0,
  CheckRowKey0,
  CheckDuplicateRows0,
  CheckModeUse0,
  CheckNoHiddenMin0,
} from '../pcc-core.mjs';

test('CheckVerifierFrag0 runs the current pcc-core fragment conformance suite', async () => {
  const out = await CheckVerifierFrag0({
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'frag0.current.pcc-core',
    cases: [
      makeAcceptCase({
        id: 'codec.nat.roundtrip.zero',
        target: 'Codec0',
        run: () => {
          const encoded = Encode0({
            tag: 'nat',
            value: 0,
          });

          const parsed = Parse0(encoded);
          assert.deepEqual(parsed, {
            tag: 'nat',
            value: 0,
          });

          return {
            tag: 'accept',
          };
        },
      }),

      makeRejectCase({
        id: 'codec.nat.reject.noncanonical-leading-zero',
        target: 'Codec0',
        run: () => {
          return Parse0(Uint8Array.from([
            0x00, 0x00, 0x00, 0x02,
            0x00, 0x01,
          ]));
        },
      }),

      makeRejectCase({
        id: 'codec.int.reject.negative-zero',
        target: 'Codec0',
        run: () => {
          return Parse0(Uint8Array.from([
            0x01,
            0x00, 0x00, 0x00, 0x00,
          ]));
        },
      }),

      makeRejectCase({
        id: 'codec.name.reject.trailing-byte',
        target: 'Codec0',
        run: () => {
          const encoded = Encode0({
            tag: 'name',
            value: 'x',
          });

          const bad = new Uint8Array(encoded.length + 1);
          bad.set(encoded, 0);
          bad[bad.length - 1] = 0x00;

          return Parse0(bad);
        },
      }),

      makeRejectCase({
        id: 'codec.name.reject.invalid-utf8-ff',
        target: 'Codec0',
        run: () => {
          return Parse0(Uint8Array.from([
            0x00, 0x00, 0x00, 0x01,
            0xff,
          ]));
        },
      }),

      makeAcceptCase({
        id: 'digest.object.deterministic',
        target: 'Digest0',
        run: () => {
          const a = DigestObject0({
            b: 2,
            a: 1,
          });

          const b = DigestObject0({
            a: 1,
            b: 2,
          });

          assert.deepEqual(a, b);

          return {
            tag: 'accept',
          };
        },
      }),

      makeAcceptCase({
        id: 'rowkey.well-shaped',
        target: 'RowKey0',
        run: () => {
          const row = {
            PackageID: 'B0',
            SchemaID: 'RowKeySelfTest',
            KindKey: 'infra',
            ArityKey: 0,
            ModeKey: 'full',
            FrontKey: 'front',
            SemanticKey: 'sem',
            IncidenceKey: 'inc',
            DependencyKey: 'dep',
            ProfileKey: 'prof',
            ChargeKey: 'charge',
            ObligationKey: 'obl',
            BudgetKey: 'bud',
            ActivationKey: 'act',
            RankKey: 'rank',
            PayloadKey: 'payload',
          };

          const key = ComputeRowKey0(row);
          const checked = CheckRowKey0(row, key);

          assert.equal(checked.tag ?? checked.kind ?? 'accept', 'accept');

          return {
            tag: 'accept',
          };
        },
      }),

      makeRejectCase({
        id: 'rowkey.reject.malformed-arity',
        target: 'RowKey0',
        run: () => {
          const row = {
            PackageID: 'B0',
            SchemaID: 'MalformedArity',
            KindKey: 'infra',
            ArityKey: 'not-a-number',
            ModeKey: 'full',
          };

          const key = ComputeRowKey0(row);
          return CheckRowKey0(row, key);
        },
      }),

      makeRejectCase({
        id: 'mode.reject.quotient-equality-as-replacement-equality',
        target: 'Mode0',
        run: () => {
          return CheckModeUse0({
            mode: 'quotient',
            equalityKind: 'quotient',
            consumedAs: 'replacement-equality',
          });
        },
      }),

      makeRejectCase({
        id: 'nomin.reject.minimumEquivalent.exec',
        target: 'NoHiddenMin0',
        run: () => {
          return CheckNoHiddenMin0({
            imports: [],
            aliases: {},
            executableSymbols: ['minimumEquivalent'],
          });
        },
      }),

      makeRejectCase({
        id: 'duprows.reject.conflicting-row-key',
        target: 'DuplicateRows0',
        run: () => {
          return CheckDuplicateRows0([
            {
              RowKey: 'same-key',
              SelectedRoute: 'Gain',
            },
            {
              RowKey: 'same-key',
              SelectedRoute: 'Neutral',
            },
          ]);
        },
      }),
    ],
  });

  assert.equal(out.tag, 'accept');
});