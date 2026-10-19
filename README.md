# Moment Ambiguity and the Limits of Robust Stochastic Optimization

[![Lean verification](https://github.com/GO-EPFL/moment-ambiguity-formalization/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/GO-EPFL/moment-ambiguity-formalization/actions/workflows/lean.yml?query=branch%3Amain)

This repository formalizes all results of the paper of the same title in Lean 4. It proves
the moment-matching constructions and their applications to quantiles, newsvendor profit,
posted-price revenue, secretary success, and prophet inequalities.

The [formalization guide](docs/Formalization.md) gives the correspondence between each of the
paper's 2 definitions and 34 numbered results and its Lean declaration. It also explains the
probability model, policy representation, and supporting results. The paper and this repository
are sufficient to follow that correspondence.

## Build and verify

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.9 or later. The repository
selects Lean 4.32.2 through `lean-toolchain`; the exact mathlib revision is pinned in
`lakefile.toml` and `lake-manifest.json`.

From the repository root, prepare the dependencies and run the checks in Bash:

```sh
lake update
lake exe cache get
bash scripts/verify.sh
```

The verification script checks the source files, imports, documentation links, and dependency
pin, builds the mathematical library and verification target, then runs the regression suites
and axiom audit with warnings treated as errors. GitHub Actions uses the same script.

For a regular rebuild after setup, `lake build` builds both default targets.

## Read or use the proofs

```lean
import MomentAmbiguity
```

This imports the mathematical results. The verification suites have a separate entry point,
`MomentAmbiguityChecks.lean`. Each topic can also be imported through its main module below;
for example, `import MomentAmbiguity.Secretary`.

| Paper topic | Main module |
|---|---|
| Binary moment-matching construction | [BinarySeparator](MomentAmbiguity/BinarySeparator.lean) |
| N-way moment-matching construction | [NWaySeparator](MomentAmbiguity/NWaySeparator.lean) |
| Quantiles, risk, and capacity | [Quantile](MomentAmbiguity/Quantile.lean) |
| Newsvendor profit | [Newsvendor](MomentAmbiguity/Newsvendor.lean) |
| Deterministic and randomized pricing | [Pricing](MomentAmbiguity/Pricing.lean) |
| Independent and i.i.d. secretary success | [Secretary](MomentAmbiguity/Secretary.lean) |
| Prophet inequalities and multiple selection | [Prophet](MomentAmbiguity/Prophet.lean), [ProphetMultiSelection](MomentAmbiguity/ProphetMultiSelection.lean) |

The files directly under `MomentAmbiguity/` contain the main constructions and application
theorems, with their proofs. Supporting modules are grouped by mathematical role:

| Directory | Contents |
|---|---|
| `Foundation/` | Distributions, moments, causal policies, finite sampling, and finite hypergraph Ramsey. |
| `Construction/` | Vandermonde identities, series bounds, N-way coefficients, and total-variation consequences. |
| `Secretary/` | Model definitions, classical secretary results, Ramsey reduction, and hard-instance mixtures. |
| `Prophet/` | Model definitions, policy analysis, hard instances, and the logarithmic lower bound. |
| `Verification/` | Regression checks and the axiom audit. |

For example, `Secretary.lean` proves the main results for both secretary models using the
supporting modules in `Secretary/`, just as `Prophet.lean` uses those in `Prophet/`.

## Proof foundations

The principal results use only the standard Lean foundations `propext`, `Classical.choice`,
and `Quot.sound`. The source checks reject unfinished proofs and project-defined axioms.
The finite Ramsey theorem, classical secretary value and limit, and logarithmic prophet lower
bound are proved within the project. The `*Interface.lean` files in `Secretary/` and `Prophet/`
state the intermediate specifications; the main results use their proved implementations.

See the [formalization guide](docs/Formalization.md) for the precise translation of the paper's
decision rules into measurable causal kernels and the scope of the multiple-selection model.
