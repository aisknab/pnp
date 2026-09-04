# Lean Cook-Levin all-body staged-request mirrored dispatch

M225 replaces M224's single first-separator coordinate with one uniform theorem
over the complete clause-token body rectangle. The source is
`lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.lean`.

## What is constructed

For every `VerifierTableauProblem`, the module defines the finite type of all
body opportunities as the product of the canonical clause count and token width.
Every member embeds into the complete post-header schedule and is proved to
decode to a genuine body coordinate. This includes populated tokens and padding.

M220's fixed 711-rule classifier runs at each such coordinate while preserving a
protected builder suffix. That suffix explicitly contains the canonical M217
optional-token request, a blank sentinel, and the existing emitted-prefix
workspace. A fixed fourteen-rule relay scans the entire blank-free classifier
prefix, crosses the sentinel, checks one of the five request symbols, and reaches
the spatial mirror of M217's dispatcher entry. M223's reflected 64-rule
dispatcher then reaches the exact appender endpoint for the next canonical
emitted prefix.

The standard total-machine bridges compose the classifier and relay into 734
rules and the full classifier, relay, and dispatcher into one 807-rule table.
Both tables have pairwise-distinct queries and distinct accepting and rejecting
states.

M227 later exposed `leftPathTape` and `relayScan_prefix_exact` for uniform
all-route reuse. The current transcript therefore audits all 82 public
declarations: 33 have empty closure, nine use only `propext`, and 40 use only
`propext` and `Quot.sound`. Neither helper adds a project axiom or
`Classical.choice`.

The module proves:

- every body opportunity decodes to a clause-token rectangle coordinate;
- the canonical request is one of padding, `F`, `T`, separator, or `Finish`;
- the complete classifier terminal prefix is blank-free;
- the fixed relay has an exact trace for every body coordinate and request value;
- the relay terminal tape is exactly the mirrored dispatcher entry tape;
- the reflected dispatcher reaches the exact next canonical emitted prefix;
- the complete 807-rule work trace and six-for-one compiled trace;
- nonhalting one work step before completion; and
- one verifier-input-size polynomial bound for the complete compiled run.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.
  BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.
  cook_levin_builder_physical_classifier_all_body_staged_request_mirrored_dispatch_checked_complete
```

Its only data argument is a `VerifierTableauProblem`. The theorem quantifies
internally over every body opportunity; callers do not supply a coordinate,
route, token, request, machine, trace, geometry, polynomial, or success
certificate.

## Claim boundary

The canonical optional-token request is still staged explicitly in protected
workspace. M225 proves that one fixed machine relays and dispatches all such
body requests; it does not synthesize the request cell from the raw classifier
terminal. The finite index excludes the unique `Finish` opportunity, so this is
not yet one combined body-and-Finish physical loop.

M225 does not join successive schedule configurations into one repeated machine
run, prove complete builder `FunctionProgram.RawRefinement`, package the
Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness, put `CNFSAT` in `P`, close a fixed risk-weighted checkpoint or
global gate, create the eligible root theorem, or prove `P = NP`.
