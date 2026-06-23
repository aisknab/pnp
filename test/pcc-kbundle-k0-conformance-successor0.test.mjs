import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelConformanceSuite0,
} from '../pcc-kimpl0.mjs';

import {
  CheckKBundleK0ConformanceFinalTheoremReadiness0,
  CheckKBundleK0ConformanceSuccessor0,
  makeKBundleK0ConformanceSuccessor0,
} from '../pcc-kbundle-k0-conformance-successor0.mjs';

const rules = [
  'Eq',
  'Subst',
  'Record',
  'DAGInd',
  'LedgerInd',
  'OblTopoInd',
  'TraceInd',
  'FiniteExhaust',
  'DPInd',
  'Hall',
