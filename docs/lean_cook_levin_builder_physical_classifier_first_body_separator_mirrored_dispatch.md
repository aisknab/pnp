# Lean Cook-Levin first-body separator mirrored dispatch

M224 extends the complete physical classifier beyond its distinct populated-body
terminal. The source is
`lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.lean`.

## What is constructed

The module derives the first post-header schedule index directly from a
`VerifierTableauProblem` and proves that its canonical entry is the separator
which begins the first CNF clause. At that index, M220's complete 711-rule
classifier takes the populated-body branch. Its final head is the first unary
clause-count unit and its right side contains the remaining count units followed
by the protected end marker.

A fixed two-rule scanner crosses that positive unary suffix and changes only the
end marker into M217's physical separator request. A fixed ten-rule blank-sentinel
orientation pass then reaches the spatial mirror of M217's canonical dispatcher
entry. M223's reflected 64-rule dispatcher executes the request and appends the
separator to the exact canonical header prefix.

The standard total-machine bridges compose these stages into one 814-rule table
with pairwise-distinct queries and distinct accepting and rejecting states. No
coordinate, request token, classifier result, emitted prefix, scan trace, machine,
polynomial bound, or success certificate is supplied to the public endpoint.

The module proves:

- the derived first-body index has value zero and selects `CNFToken.sep`;
- the canonical clause count is positive;
- the exact populated-body classifier terminal and protected tape geometry;
- exact execution of the fixed two-rule request writer;
- blank-free orientation across the complete retained prefix;
- exact execution of the reflected fixed dispatcher;
- the complete 814-rule work trace and six-for-one compiled trace;
- nonhalting one work step before completion;
- the exact canonical emitted prefix ending in the first clause separator; and
- one verifier-input-size polynomial bound for the complete compiled run.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.
  BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.
  cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete
```

Its only data argument is a `VerifierTableauProblem`. Its type records the
derived coordinate and separator request, the fixed writer, orientation,
dispatcher and complete-machine rule counts, collision freedom, distinct terminal
states, the exact execution contract, and the uniform polynomial compiled-step
bound.

## Claim boundary

M224 closes only the first populated body coordinate. It does not select an
arbitrary body token, derive a padding request, connect all classifier outcomes,
or join successive schedule configurations into one literal repeated machine
loop.

It does not prove complete builder `FunctionProgram.RawRefinement`, package the
Cook-Levin `PolynomialReduction`, establish concrete NP-hardness or
NP-completeness, put `CNFSAT` in `P`, close a fixed risk-weighted checkpoint or
global gate, create the eligible root theorem, or prove `P = NP`.
