# Conditional residual-terminal HB selector-silence rank closure

`lean/PNP/ResidualTerminalHBSelectorSilenceClosure.lean` closes the finite-rank
induction step left by the checked typed-realizer and HB active-dependency
milestones. Once checked HB closure has removed every active HN and budget bot,
an accepted faithful row can contain only a verified strict gain or a faithful
selector at strictly lower finite rank. An explicit global semantic no-gain
premise removes the gain branch, so strong induction removes every faithful
canonical selector in the supplied table.

This is a conditional supplied-table theorem. It is not a construction of the
table or its semantic premises from a terminal candidate.

## Rank induction

`TerminalPacketTypedRealizerTable.noFaithful_of_noStrictEquivalentGain` is
polymorphic in the atom and payload types, circuit arities, finite rank count,
current implementation, and grouped BN6 family. It consumes:

```text
an accepted typed-realizer table
an accepted checked HB no-outcome active closure
global semantic exclusion of every StrictEquivalentGain
```

For a candidate handle at rank `r`, an accepted faithful row is interpreted by
the preceding `hbActiveClosureSound` theorem. HN and budget outcomes have
already been eliminated. A gain contradicts the global gain exclusion premise.
A lower-seed outcome supplies a faithful handle whose rank is strictly below
`r`; the strong induction hypothesis says that handle is nonfaithful. Both
remaining outcomes are impossible, so the original handle is nonfaithful.

The induction ranges over arbitrary natural rank values obtained from the
supplied finite rank table. It does not depend on a fixed numerical rank bound.

## Gain-coverage specialization

`TerminalPacketTypedRealizerTable.noFaithful_of_gainCoverageNoGain` uses the
earlier `TerminalPacketSelectorGainCoverage` interface. A supplied coverage
certificate says that every strict equivalent gain occurs as an original
payload in a canonical Packet source cell. Exact no-gain evidence for every
payload in every such cell then derives the global gain-exclusion premise used
by the rank induction.

This specialization does not infer global gain exclusion from ordinary
finite-family scan silence. The coverage certificate remains a separate,
explicit proof-bearing premise.

## Canonical contracts

`terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract`
returns four facts together:

```text
every canonical handle is nonfaithful
the checked HB no-outcome closure proposition holds
every supplied HN/BUD activity bit is false
the supplied dependency relation is well founded
```

`terminalBN6_packet_typed_realizer_hb_selector_silence_gain_coverage_contract`
provides the same interface after deriving semantic gain exclusion from the
explicit coverage certificate and source-cell evidence.

## Audit surface

The source has 4 public theorem declarations. The source-derived axiom
transcript prints all four. Every declaration reaches only Lean's standard
`propext` and `Quot.sound` principles. None reaches `Classical.choice`,
`sorryAx`, or a project-specific axiom.

Run the focused checks with:

```text
lake build PNP.ResidualTerminalHBSelectorSilenceClosure
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHBSelectorSilenceClosureAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHBSelectorSilenceClosure.lean
node --test audits/lean-residual-terminal-hb-selector-silence-closure0.test.mjs
```

## Boundary

The selector-silence rank closure is only as semantic as its inputs. The
grouped family, rank and faithfulness tables, realizer claims, blocker activity,
dependency rows, finite-to-exact rank map, and global semantic gain exclusion
remain supplied. The coverage theorem likewise consumes rather than constructs
its global certificate.

The result does not establish selector faithfulness or compatibility, derive
blocker semantics or semantic dependency completeness, construct the sidecars
from terminal data, prove that positive residual slack reaches this interface,
or establish the unconditional manuscript `HB.NegativeClosure`. It does not
prove unconditional ZeroSlack, PCCMin, encoded-size or polynomial-runtime
bounds, SAT in P, removal of a project assumption, or P = NP.
