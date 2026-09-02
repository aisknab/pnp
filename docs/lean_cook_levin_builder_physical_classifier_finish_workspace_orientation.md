# Lean Cook-Levin classifier Finish-workspace orientation

M222 adds a fixed physical orientation stage after M221's complete-classifier
`Finish` request. The new source is
`lean/PNP/Concrete/CookLevinBuilderPhysicalClassifierFinishWorkspaceOrientation.lean`.

## What is constructed

The M220/M221 classifier preserves an arbitrary workspace on the left of its
own derived routing prefix. M217's optional-token dispatcher expects its
builder workspace on the right of the request cell. M222 supplies M221 with a
canonical builder workspace protected by one blank sentinel, proves the
classifier prefix itself contains no blank symbol, and scans left until that
sentinel is reached.

The orienter has ten literal rules: one launch rule and one scan rule for each
of the nine work symbols. Nonblank cells are preserved while the head moves
left. At the sentinel, the machine writes the canonical `Finish` request and
halts. The full composition with M221 has 740 rules with pairwise-distinct
queries and distinct accepting and rejecting states.

The final tape has the canonical builder word on its left, the `Finish`
request under the head, and the reversed classifier prefix plus the original
request cell on its right. This is exactly the spatial mirror of M217's
canonical request entry. The classifier material is retained as exterior data;
no supplied prefix, trace, or geometry certificate appears in the endpoint.

The module proves:

- the classifier's complete left prefix and empty right exterior;
- exclusion of the blank sentinel from the derived prefix;
- a verifier-derived bound on the prefix length;
- the generic exact sentinel scan;
- the complete M221-plus-orienter work trace;
- the exact six-transitions-per-work-step compiled trace;
- nonhalting one work step before completion;
- the exact spatial mirror of M217's canonical request entry; and
- one source-input-size polynomial bound for the compiled run.

## Public theorem

The certificate-free endpoint is:

```lean
PNP.Concrete.CookLevin.BuilderPhysicalClassifierFinishWorkspaceOrientation.
  cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete
```

Its only data argument is a `VerifierTableauProblem`. Its type records the
derived `Finish` schedule entry, fixed 740-rule count, collision freedom,
distinct terminal states, complete orientation contract, and uniform
polynomial compiled-step bound.

## Claim boundary

M222 closes only the workspace-orientation edge for the unique
full-classifier `Finish` path. Equality with a spatial mirror of M217's
canonical request entry does not prove that M217's existing machine executes
on the mirrored representation.

M222 does not derive body-token or padding requests, execute a mirrored
dispatcher, connect successive schedule configurations, implement a repeated
physical builder loop, prove builder `FunctionProgram.RawRefinement`, or
package the Cook-Levin `PolynomialReduction`. It does not prove CNFSAT
NP-hardness, CNFSAT in P, any global gate, the eligible root theorem, or
`P = NP`.
