# Cook-Levin physical optional-token dispatch

M217 replaces M215's value-level selector-to-appender handoff with one fixed
literal work machine for the complete optional-token request alphabet. For
every raw input, arbitrary exterior workspace, emitted prefix, and request, the
machine reads one tape-resident symbol and either preserves the prefix for
padding or enters the existing token appender for the requested CNF token.

## What is physical

The request alphabet contains exactly five symbols: padding plus `F`, `T`,
`Sep`, and `Finish`. A request cell replaces the ordinary builder left-boundary
cell. The first transition is selected only by that physical symbol, rewrites
the canonical left marker, moves right, and therefore restores the exact
workspace expected by the existing 59-rule token appender.

The combined machine has one five-rule dispatcher and one collision-free
renamed appender, for 64 rules total. Exact work-machine and six-for-one
compiled traces cover every request. One-step-short fuel remains nonhalting,
and the unused blank request symbol fails closed as timeout for every fuel.

## Canonical all-coordinate specialization

For every in-range post-header coordinate, `canonicalRequest` is derived from
the canonical `scheduleEntry`. Padding preserves the current emitted prefix;
each populated entry reaches the exact next prefix already characterized by
M215. The combined dispatch-and-append trace fits one verifier-derived
source-size polynomial.

The publication endpoint is:

```text
PNP.Concrete.CookLevin.BuilderPhysicalOptionalTokenDispatch.cook_levin_builder_physical_optional_token_dispatch_checked_complete
```

All 49 public declarations are audited. The measured closure contains 23
declarations with no axioms, 13 using only `propext`, and 13 using only
`propext` and `Quot.sound`; no project axiom or `Classical.choice` is used.

## What remains open

The request cell is the input to this stage. M217 does not yet construct it
from M214's raw coordinate classifier, connect classifier output directly to
the dispatcher, or iterate one physical selector/dispatcher loop through the
complete schedule. It therefore does not provide the complete builder
`RawRefinement`, the packaged Cook-Levin `PolynomialReduction`, concrete
`CNFSAT` NP-hardness, deterministic `CNFSAT` in `P`, or `P = NP`.

The fixed checkpoint for the complete uniformly polynomial Cook-Levin builder
remains open. M217 leaves the risk-weighted proof estimate at 35 percent and
adds formal artefact coverage only.
