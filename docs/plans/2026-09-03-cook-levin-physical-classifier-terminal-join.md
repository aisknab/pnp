# M226: Cook-Levin physical classifier terminal join

## Selection rationale and legacy anchor

The pinned legacy manuscript's `TraceEquivalence` lemma and final SAT-decision
section require one uniform concrete Cook-Levin formula builder. The active
reconstruction records that obligation under `Formal.ConcreteSAT` and the open
`reductions-complete-cook-levin-builder` checkpoint.

M225 gives one fixed physical classifier, protected-request relay and dispatcher
composition for every coordinate in the complete clause-token body rectangle.
M223 separately executes the unique `Finish` branch. A repeated builder cannot
reuse one loop body while those two outcomes remain distinct halting states of
the complete M220 classifier. The next bounded dependency is therefore a
literal terminal join over the whole post-header domain, not another fixed
coordinate or clause prefix.

## Unbounded abstraction and bounded theorem target

Wrap M220's fixed 711-rule classifier in one finite machine that:

1. injectively embeds every classifier state into a protected namespace;
2. retains the accepting body terminal unchanged;
3. makes the rejecting `Finish` terminal nonhalting in the wrapper;
4. adds exactly one symbol-preserving redirect for each of the nine work-tape
   symbols; and
5. sends every `Finish` terminal tape to the same accepting state used by body
   coordinates.

Prove the source trace transports exactly for arbitrary protected workspace.
For every verifier-derived post-header coordinate, use M220's route agreement
to show that a body route needs no extra step and the unique `Finish` route needs
exactly one redirect step. Retain exact compiled execution, one-step-short
nonhalting, collision freedom, terminal separation and one source-input-size
polynomial bound.

## Exact theorem boundary

Add
`PNP.Concrete.CookLevin.BuilderPhysicalClassifierTerminalJoin` and the endpoint:

```text
PNP.Concrete.CookLevin.BuilderPhysicalClassifierTerminalJoin.
  cook_levin_builder_physical_classifier_terminal_join_checked_complete
```

The endpoint takes only a `VerifierTableauProblem`. It quantifies internally
over every coordinate in the complete post-header domain and every preserved
workspace. No caller supplies a coordinate, route, terminal verdict, trace,
machine, polynomial bound or success certificate.

## Claim boundary and downstream blockers

M226 normalizes only classifier control flow. It neither reads nor writes a
canonical optional-token request and therefore does not claim raw body-request
synthesis or token dispatch. M223 remains the stronger evidence that the unique
`Finish` request can be generated and dispatched; M226 does not weaken or
replace it.

The work still does not join the terminal normalizer to one all-route request
generator, connect successive schedule configurations, implement a repeated
physical builder loop, prove complete builder `FunctionProgram.RawRefinement`,
package the Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness transport, put `CNFSAT` in `P`, close a fixed checkpoint or
global gate, create the eligible root theorem, or prove `P = NP`.

The fixed risk-weighted score therefore remains 35 percent with the 20 to 40
percent uncertainty range. Formal artefact coverage is regenerated separately.

## Evidence and release gates

- Build the new module under the pinned Lean toolchain on the configured remote
  builder.
- Add exact source-state injection, redirect-table, body-zero-step,
  Finish-one-step, all-coordinate, arbitrary-workspace, work, compiled,
  one-step-short, collision and polynomial-bound regressions plus a
  declaration-complete axiom audit.
- Add hostile checks that reject coordinate-specific machines, omitted Finish
  redirects, partial request-symbol tables, tape-changing redirects, supplied
  routes or verdicts, hidden assumptions, and widened request-generation,
  dispatch, loop, refinement, reduction or complexity claims.
- Import the module through the root and theorem inventory, then regenerate the
  canonical inventory, publication map, status, progress ledger and report.
