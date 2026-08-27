# Moment Ambiguity and the Limits of Robust Stochastic Optimization

[![Lean verification](https://github.com/GO-EPFL/moment-ambiguity-formalization/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/GO-EPFL/moment-ambiguity-formalization/actions/workflows/lean.yml?query=branch%3Amain)

This repository contains a Lean 4 formalization of the paper's mathematical results. It
develops moment-equivalent probability distributions and applies them to quantile optimization,
newsvendor and pricing models, secretary problems, and prophet inequalities. The project
formalizes all 37 active definition, lemma, proposition, theorem, and corollary environments,
together with the measure-theoretic, analytic, combinatorial, and online-policy arguments used
in their proofs. Remarks are outside this count.

## Results

The development includes:

- finite Vandermonde constructions and countably supported binary and N-way families of
  distributions with identical moments and disjoint supports;
- maximal total-variation separation within a single full moment class;
- quantile, VaR, LCVaR, chance-capacity, newsvendor, and posted-pricing applications;
- randomized pricing with the quantifier order
  `∀ ε > 0, ∃ N ≥ 2, ∃ (μ_h)_{h<N}, ∀ λ, ∃ h < N`;
- the exact finite-horizon secretary value and its separate limit to `1 / e`;
- logarithmic prophet bounds and the corresponding multi-selection upper bound.

The [traceability document](docs/TRACEABILITY.md) maps these 37 definitions and results to their
Lean declarations and documents the formal definitions and translation choices.

## Formalization

Distributions are probability measures on the nonnegative reals. Moment equivalence includes
integrability and equality at every natural moment order. Product measures are used for
independent observations, and randomized decisions are represented by probability measures or
measurable Markov kernels as appropriate.

Secretary and prophet policies are causal: their selection probabilities depend only on the
disclosed moment profile and the observed prefix. Prophet guarantees are stated as universal
multiplication inequalities, including instances whose benchmark is zero.

Single-choice policies use an extensional terminal-kernel model; the development does not
separately prove its standard finite-horizon equivalence with hazard-based behavioral rules.
The multi-selection upper bound is proved for the potentially broader class of terminal-set
kernels with prefix-causal membership marginals.

The finite Ramsey theorem, the exact classical secretary calculation and its asymptotic limit,
and the dyadic bucket-threshold prophet lower bound are all proved within the project.

## Build

The project uses Lean 4.32.2 and pins mathlib to commit
`905b95818eb32af7874a58b427f50c1711a5e96c`. With Lean installed through
[elan](https://github.com/leanprover/elan), run:

```sh
lake update
lake exe cache get
lake build
```

`MomentAmbiguity.lean` imports the complete development, including the regression checks and
axiom audit. The GitHub Actions workflow runs the same build on every push and pull request and
also checks that dependency resolution does not change `lake-manifest.json`.

## Verification checks

`MomentAmbiguity/Regression.lean` and `MomentAmbiguity/ClosedRegression.lean` cover boundary
cases such as horizon one, two-way separation, quantile endpoints, zero prophet benchmarks,
repeated order-statistic values, and the exact normalization constants.

`MomentAmbiguity/AxiomAudit.lean` prints the axioms of the principal results. The audited
declarations use only the standard Lean foundations `propext`, `Classical.choice`, and
`Quot.sound`. The project contains no project-defined axioms or unfinished proofs.

## Project structure

| Modules | Contents |
|---|---|
| `Basic`, `Discrete`, `Vandermonde` | Probability measures, moments, atomic laws, and finite algebra |
| `SeriesBounds`, `BinarySeparator`, `NWayCoefficients`, `NWaySeparator` | Moment-matching separator constructions |
| `TotalVariation`, `Quantile`, `Newsvendor`, `Pricing` | Static applications |
| `OnlinePolicy`, `Secretary*` | Causal policies, finite Ramsey theory, and secretary results |
| `Prophet*`, `CorreaLower` | Prophet inequalities, bucketing, hard instances, and multi-selection |
| `Regression`, `ClosedRegression`, `AxiomAudit` | Boundary checks and trust audit |
