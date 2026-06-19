import {
  COORD,
  checkNoHiddenMin0,
  makeMinimalBootstrapContext,
} from '../../pcc-core.mjs';

import {
  expectCoreErr,
  expectCoreOk,
  printExample,
} from './lib.mjs';

function makeExampleContext() {
  const ctx = makeMinimalBootstrapContext();
  ctx.expandAll = (ast) => ast;
  ctx.collectIdentifierOccurrences = (ast) => ast.occurrences ?? [];
  ctx.resolveAlias = (identifier) => ({
    minEq: 'minimumEquivalent',
  })[identifier] ?? identifier;
  return ctx;
}

const allowedAst = {
  occurrences: [
    {
      name: 'minimumEquivalent',
      class: 'AssumeOnly',
      path: ['theorem', 'definition'],
    },
    {
      name: 'PCCMin',
      class: 'ExecCall',
      path: ['algorithm', 'body', 0],
    },
  ],
};

const passingCase = expectCoreOk(
  checkNoHiddenMin0(makeExampleContext(), allowedAst),
  () => ({
    theoremOnlyMinimumDefinitionAllowed: true,
    declaredPCCMinCallAllowed: true,
  }),
);

const forbiddenAst = {
  occurrences: [
    {
      name: 'minEq',
      class: 'ExecCall',
      path: ['algorithm', 'body', 0],
    },
  ],
};

const failingCase = expectCoreErr(
  checkNoHiddenMin0(makeExampleContext(), forbiddenAst),
  {
    coord: COORD.HIDDEN_MIN_EXEC_CALL,
    path: ['algorithm', 'body', 0],
    inspect: (result) => ({
      identifier: result.witness.identifier,
      canonicalName: result.witness.canonicalName,
    }),
  },
);

printExample({
  id: '04-no-hidden-minimization',
  concept: 'Mathematical minimum definitions may appear in assumptions, but forbidden exact-minimization aliases may not execute',
  humanInput: {
    passing: 'minimumEquivalent occurs only in a theorem definition; PCCMin is the declared residual-band procedure.',
    failing: 'The executable alias minEq resolves to forbidden minimumEquivalent.',
  },
  expectedCertificate: 'The theorem-only occurrence passes; the executable alias rejects with HiddenMin.ExecCall at its exact path.',
  passingCase,
  failingCase,
  proves: 'The core scanner uses occurrence class and alias resolution for this minimal fixture.',
  doesNotProve: 'It does not prove that all executable JavaScript, imports, generated templates, dynamic calls, or equivalent brute-force searches are covered by the repository-wide scan.',
});
