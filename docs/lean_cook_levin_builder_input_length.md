# Literal Cook--Levin builder input-length tally

`lean/PNP/Concrete/CookLevinBuilderInputLength.lean` supplies the first literal
finite-machine stage intended for the concrete Cook--Levin formula builder. It
does not build a formula. It preserves the source input while materializing its
length as a unary work-tape tally for later stages.

## Machine contract

`PNP.Concrete.CookLevin.BuilderInputLength.machine` has one fixed list of 19
`WorkRule` values. The rules do not depend on the input, a SAT answer, a
precomputed formula, a cursor result, or a caller-supplied certificate.

The stage starts from

```lean
inputTape input outsideLeft =
  PipelineTape.frameWithGarbage (Tape.ofInput input) outsideLeft []
```

where `outsideLeft` is arbitrary already-isolated exterior garbage and the
workspace beyond the right marker is fresh. It temporarily marks each source
bit, walks to the right workspace, appends one `tallySymbol`, returns to the
mark, restores the original bit, and continues. Its exact endpoint is

```lean
finalTape input outsideLeft =
  PipelineTape.frameWithGarbage (Tape.ofInput input) outsideLeft
    (List.replicate input.length tallySymbol)
```

so the represented input is unchanged and the tally length is exactly the
external bitstring length.

## Exact execution and bounds

The principal universal trace theorem is

```lean
PNP.Concrete.CookLevin.BuilderInputLength.workRunExact
  (input : BitString) (outsideLeft : List WorkSymbol) :
  workRunExact? machine (workSteps input.length)
      (workStartConfiguration machine (inputTape input outsideLeft)) =
    some (finalConfiguration input outsideLeft)
```

with

```text
workSteps(n) = 2*n*n + 4*n + 2
```

The ordinary three-symbol compiler consumes exactly six raw steps per work
step. `rawTimeBound` is the explicit external-size polynomial

```text
12*n*n + 24*n + 12
```

and `run_compile` proves equality with the encoded final configuration at that
budget. `tallySizeBound = NatPolynomial.variable` proves the tally occupies
exactly `n` cells.

The negative behavior is also explicit:

- `malformedScanSymbol_timeout` proves the unused internal scan symbol has no
  transition and returns timeout for every fuel value;
- `work_one_step_short_timeout` proves that removing exactly one work step from
  the successful budget leaves a nonhalting state, rather than acceptance or
  rejection.

`inputTape_eq_totalInputFramerFinalTape` and
`workRunExact_after_totalInputFramer` connect this stage definitionally to the
already-proved all-input framer endpoint. They do not add a bridge transition or
compose the two rule tables into a new machine.

## Audit and regression boundary

The complete public surface contains 39 declarations. The compiled axiom
transcript records:

- 31 declarations with empty axiom closure;
- one declaration using only Lean's standard `propext` axiom;
- seven declarations using only `propext` and `Quot.sound`.

No declaration reaches a project axiom or `Classical.choice`. The regression
file covers empty, one-bit, odd, even, all-zero, all-one, and mixed inputs,
arbitrary exterior garbage, exact numeric costs, malformed state, one-step-short
fuel, compiled execution, and the total-framer endpoint. The hostile JavaScript
audit mutates symbols, restoration, workspace freshness, polynomials, timeout,
assumptions, and theorem scope and requires every mutation to fail closed.

Run:

```bash
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderInputLengthAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderInputLength.lean
node --test audits/lean-concrete-cook-levin-builder-input-length0.test.mjs
```

## Exact nonclaim

This milestone does not emit even one formula bit, turn a direct cursor lookup
into constant-time raw execution, compose a complete formula builder, prove a
builder `RawRefinement`, or package a `PolynomialReduction`. Consequently it
does not establish CNFSAT NP-hardness or NP-completeness, `CNFSAT ∈ P`, or
`P = NP`. `PNP.Main.p_eq_np` remains absent and the publication gate remains
false.
