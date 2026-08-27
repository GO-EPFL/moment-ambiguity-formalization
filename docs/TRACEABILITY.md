# Formalization traceability

This document maps the active mathematical results in *Moment Ambiguity and the Limits of Robust
Stochastic Optimization* to their Lean declarations. The project contains formalizations of all
37 active definition, lemma, proposition, theorem, and corollary environments, together with the
supporting lemmas needed for their proofs. Two separator theorem environments each carry a
second LaTeX label; all remarks are outside the count of 37.

The Lean environment is pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`: Lean 4.32.2 and mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c`.

## Formal model and translation choices

- Manuscript distributions are `ProbabilityMeasure ℝ≥0`; only the arbitrary-real-node finite
  Vandermonde lemma uses `ProbabilityMeasure ℝ`.
- `MomentEquivalent` contains integrability on both sides and equality of the full moment
  sequences for every natural order.  `momentClass` and `IsStieltjesTypeClass` reuse it.
- Countable atomic laws are PMFs pushed forward to their support nodes.  Finite product laws
  have proved coordinate marginals and mutual independence.  Uniform secretary arrival is an
  independent product with a uniform permutation.
- “Supported on” means measure one on the displayed carrier, which is the precise property used
  in the paper; no topological-support closure is introduced.
- `manuscriptTV` is exactly `sup_A |μ(A)-ν(A)|` under the paper's `[0,1]` normalization.
- The quantile is totalized by assigning `0` outside `(0,1)`.  In particular the arbitrary
  value at `u=0` is a null integration endpoint and does not change LCVaR.
- The untyped `B ≥ 3` in `cor:chance-capacity` is formalized as real `B`; the proof applies the
  integer separator at `⌈B⌉` and states the factor claim without division.
- A randomized newsvendor order is a probability law on `ℝ≥0` with finite first moment.  A
  randomized price is a probability law on the strictly-positive price subtype and has no
  irrelevant moment requirement.
- The optimal posted-price benchmark is written over all nonnegative thresholds.  Adding the
  zero threshold does not change the manuscript supremum over positive thresholds because its
  revenue is zero and every revenue is nonnegative.
- Secretary and prophet policies are measurable Markov kernels.  Selection-time masses are
  prefix-causal; `none` is explicit.  Secretary rules receive labels and cardinal observations.
  Single-selection policies are formalized directly through prefix-causal terminal selection
  masses.  The development does not separately prove the standard finite-horizon equivalence
  between these extensional kernels and hazard-based behavioral rules.
  `MultiSelectionPolicy` is a terminal-set kernel whose selection-membership marginals are
  prefix-causal.  This may be a larger class than sequentially implementable joint selection
  laws because suffix-dependent correlations are not excluded; the multi-selection upper bound
  is therefore a strengthening of the manuscript claim, and its proof uses only those marginals.
- Repeated numerical values retain multiplicity because order statistics range over subsets of
  coordinate indices.  Ranks are one-based subtypes carrying `1 ≤ r ≤ m`.
- `rhoMom` is defined solely as the supremum of nonnegative universal multiplication guarantees.
  Its feasible set is proved nonempty and bounded.  No theorem divides by a potentially zero
  prophet benchmark.
- The binary extended proposition's `j ∈ ℕ` is represented as `0 < j`; the headline structure
  uses the separately proved stronger `j=0` case.  Its finite uniqueness, limiting construction,
  and exact decay bound are split into named reusable declarations.
- Negative exponents in `C_N` and all coefficient bounds use integer powers (`zpow`), never
  truncated natural subtraction.
- The source's iid order-statistic tail expectations are represented as `n` times their
  one-coordinate integrals, with the product-law equality and integrability proved separately.

All 37 active definition and result environments are formalized using the representations
above.  The multi-selection upper bound ranges over the potentially larger marginal-causal
terminal-set class and therefore strengthens the manuscript's sequential-policy statement.

## Unlabeled source definitions and proof interfaces

| Source concept | Lean declaration(s) | Module | Translation / assumptions |
|---|---|---|---|
| Nonnegative distributions, finite moments, and full moment agreement | `Distribution`, `HasFiniteMoment`, `HasFiniteMoments`, `moment`, `momentSequence`, `MomentEquivalent` | `Basic.lean` | Probability measures on `ℝ≥0`; integrability is part of moment agreement |
| CDF, open CDF, quantile, VaR, and LCVaR | `cdf`, `openCDF`, `lowerQuantile`, `valueAtRisk`, `lowerCVaR` | `Quantile.lean` | Quantile is totalized outside `(0,1)`; the `u=0` LCVaR endpoint is null |
| Normalized total variation and exact support carriers | `manuscriptTV`, `SupportedOn` | `Basic.lean` | `sup_A |μ(A)-ν(A)|` in `[0,1]`; support means mass one on the carrier |
| Independent coordinates and multiplicity-preserving order statistics | `independentValues`, `independentValues_marginal`, `independentValues_iIndep`, `ValidRank`, `descendingOrderStatistic`, `orderStatisticBenchmark` | `OnlinePolicy.lean`, `ProphetDefs.lean` | Finite product law; order statistics range over coordinate subsets, so ties retain multiplicity |
| Newsvendor profit and randomized orders | `newsvendorProfit`, `RandomizedOrderingRule`, `meanOrder`, `randomizedNewsvendorProfit` | `Newsvendor.lean` | The rule packages a probability law on `ℝ≥0` with a finite-first-moment proof |
| Posted-price revenue, price lotteries, localization intervals, and `C_N` | `PositivePrice`, `postedRevenue`, `optimalPostedRevenue`, `PricingRule`, `randomizedPostedRevenue`, `pricingSpecialIndex`, `pricingGoodInterval`, `pricingCN` | `Pricing.lean` | Lotteries live on strictly positive prices; `pricingCN` uses integer powers and a proved summable series |
| Secretary arrival, policies, success, finite value, and robust value | `uniformPermutation`, `SecretaryPolicy`, `secretarySuccessProbability`, `secretaryS`, `SecretaryUniversalGuarantee`, `robustSecretaryValue` | `OnlinePolicy.lean`, `SecretaryDefs.lean` | Uniform permutation is independent of the product value law; policies are measurable kernels with prefix-causal stopping masses |
| Prophet policies and guarantee-defined robust constant | `ProphetPolicy`, `prophetExpectedReward`, `ProphetUniversalGuarantee`, `prophetFeasibleSet`, `rhoMom` | `OnlinePolicy.lean`, `ProphetDefs.lean` | `rhoMom` is an `sSup` of multiplication-form universal guarantees; the feasible set is nonempty and bounded |
| At-most-`r` selection policies and total reward | `MultiSelectionPolicy`, `multiExpectedReward` | `OnlinePolicy.lean`, `ProphetMultiSelection.lean` | Potentially broader terminal-set class with prefix-causal membership marginals |
| Binary nodes, finite weights, limits, normalizer, and laws | `BinarySeparator.node`, `BinarySeparator.finiteWeight`, `BinarySeparator.limitWeight`, `BinarySeparator.normalizer`, `BinarySeparator.muLaw`, `BinarySeparator.nuLaw` | `BinarySeparator.lean` | Countable atomic probability laws obtained from the normalized signed limit |
| `N`-way product, coefficients, residue sums, normalizer, exponent, and laws | `nwayInfiniteProduct`, `nwayCoeff`, `nwayResidueMoment`, `nwayNormalizer`, `nwayExponent`, `nwayDistribution` | `NWayCoefficients.lean`, `NWaySeparator.lean` | Analytic Taylor coefficients are identified with the finitely-supported digit `tsum` |
| Provenance interfaces not supplied by mathlib | `FiniteRamseyPrinciple`, `ClassicalSecretaryUpperBound`, `ClassicalSecretaryAttainment`, `ClassicalSecretaryLimit`, `CorreaLogLowerBound` | `External/*.lean`; internally inhabited by `SecretaryRamsey.lean`, `ClassicalSecretary.lean`, `SecretaryLimit.lean`, `CorreaLower.lean` | Named `Prop` specifications retained for traceability; all have proved inhabitants and are not assumptions of canonical results |

## Dependency graph

```text
Basic
├── Discrete
│   ├── Vandermonde
│   ├── BinarySeparator
│   ├── OnlinePolicy ── SecretaryDefs ── External/FiniteRamsey
│   │                                  └─ External/Secretary
│   └── ProphetDefs
├── SeriesBounds ── NWayCoefficients ── NWaySeparator ── TotalVariation
├── BinarySeparator ── Quantile ── Newsvendor
├── BinarySeparator + NWaySeparator ── Pricing
├── FiniteHypergraphRamsey ── SecretaryRamsey
├── SecretaryDefs ── ClassicalSecretaryLP ── ClassicalSecretary
│                └─ SecretaryLimit
├── SecretaryDefs + NWaySeparator + proved secretary interfaces
│   └── SecretaryUpper ── Secretary
└── ProphetDefs + BinarySeparator
    ├── ProphetBucketing ── CorreaLower
    └── ProphetSeparator ── Prophet block/embedding/policy layers
        └── Prophet ── ProphetMultiSelection

Regression + ClosedRegression + AxiomAudit ── top-level MomentAmbiguity
```

## Traceability: 37 active definition and result environments

“Fully verified” means definitions are implemented and result declarations are proved from
Lean/mathlib foundations and the manuscript hypotheses.  The provenance specifications in
`External/` remain available, while the declarations listed here use their internal inhabitants
and have no literature-result parameters.

| # | LaTeX label | Lean declaration(s) | Source file | Status | Assumptions / dependency |
|---:|---|---|---|---|---|
| 1 | `def:stieltjes-type-class` | `momentClass`, `IsStieltjesTypeClass` | `MomentAmbiguity/Basic.lean` | Fully verified | Definition; finite moments are explicit |
| 2 | `def:moment-based-policy` | `IsMomentBased`; concrete `SecretaryPolicy`, `ProphetPolicy`, `MultiSelectionPolicy` | `Basic.lean`, `OnlinePolicy.lean` | Fully verified | Measurability explicit; single-choice terminal masses and multi-selection membership marginals are prefix-causal |
| 3 | `lem:finite-binary-vandermonde` | `finite_binary_vandermonde`, `finite_binary_vandermonde_with_integrability` | `MomentAmbiguity/Vandermonde.lean` | Fully verified | `k ≥ 2`, strictly increasing real nodes; all polynomial moments explicitly integrable |
| 4 | `prop:key-prop-1`; `thm:binary-separator` | `BinarySeparator.binary_separator` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Integers `n,B ≥ 3` |
| 5 | `prop:key-prop-2`; `thm:nway-separator` | `nway_separator`, `hasSum_nwayCoeff`, `nwayDistribution_singleton`, `nwayMass_toReal_of_modEq`, `nwayNormalizer_eq_residue` | `NWayCoefficients.lean`, `NWaySeparator.lean` | Fully verified | Integers `B,N ≥ 2`; exact generating series, atom formula, common normalization, supports, moments, and coefficient bounds |
| 6 | `cor:maximal-total-variation` | `BinarySeparator.Data.manuscriptTV_eq_one`, `nwayDistribution_manuscriptTV_eq_one`, `exists_full_momentClass_pairwise_maximalTV`, `exists_full_momentClass_injective_pairwise_maximalTV` | `BinarySeparator.lean`, `NWaySeparator.lean`, `TotalVariation.lean` | Fully verified | Pairwise distinct residue indices; injective `N`-law family in one full moment class for every `N ≥ 2` |
| 7 | `cor:quantile-separation` | `quantile_separation` | `MomentAmbiguity/Quantile.lean` | Fully verified | `β ∈ [1/2,1)`, integer `B ≥ 3` |
| 8 | `cor:risk-quantile-separation` | `risk_quantile_separation_var`, `risk_quantile_separation_lcvar` | `MomentAmbiguity/Quantile.lean` | Fully verified | Exact source ranges for `u`, `n ≥ 4`, `B ≥ 3` |
| 9 | `cor:chance-capacity` | `chance_capacity_measurable`; stronger helper `chance_capacity` | `MomentAmbiguity/Quantile.lean` | Fully verified | Real `B ≥ 3`; measurable moment rule and uniform moment-class feasibility |
| 10 | `lem:newsvendor-critical-fractile` | `newsvendor_critical_fractile` plus one-sided derivative helpers | `MomentAmbiguity/Newsvendor.lean` | Fully verified | `β ∈ [0,1]`, finite first demand moment |
| 11 | `lem:newsvendor-randomization` | `newsvendor_randomization`, `randomizedProfitIntegrable` | `MomentAmbiguity/Newsvendor.lean` | Fully verified | Explicit `β`; demand/order first moments |
| 12 | `lem:newsvendor-optima` | `newsvendor_optima` | `MomentAmbiguity/Newsvendor.lean` | Fully verified | Source `β,ε,B,n` inequalities |
| 13 | `thm:newsvendor` | `newsvendor_universal_guarantee`, `newsvendor_impossibility` | `MomentAmbiguity/Newsvendor.lean` | Fully verified | Source hypotheses; ratio only after positive optima |
| 14 | `thm:revenue-deterministic` | `revenue_deterministic_universal`, `revenue_deterministic` | `MomentAmbiguity/Pricing.lean` | Fully verified | `ε ∈ (0,1)`; positive prices |
| 15 | `lem:N-class-revenue-localization` | `N_class_revenue_localization`; `summable_pricingSeriesTerm` | `MomentAmbiguity/Pricing.lean` | Fully verified | `B,N ≥ 2`; integer-power `C_N` |
| 16 | `thm:randomized-pricing-all-moments` | `randomized_pricing_all_moments_universal`, `randomized_pricing_all_moments` | `MomentAmbiguity/Pricing.lean` | Fully verified | Exact `∀ε ∃N ∃μ_h ∀λ ∃h` order |
| 17 | `cor:first-atom-concentration` | `first_atom_concentration`, `first_atom_concentration_exists` | `MomentAmbiguity/NWaySeparator.lean` | Fully verified | Eventual integer-base limit, uniform over `h < N` |
| 18 | `lem:ramsey-erasure` | `ramsey_erasure`; compatibility form `ramsey_erasure_of_external` | `MomentAmbiguity/SecretaryUpper.lean` | Fully verified | Internal `finiteRamseyPrinciple` and `classicalSecretaryUpperBound`; no attainment needed |
| 19 | `thm:full-secretary-success` | `full_secretary_success`; compatibility form `full_secretary_success_of_external` | `MomentAmbiguity/Secretary.lean` | Fully verified | Internal finite Ramsey, classical upper bound, and explicit attaining rule, bundled as `classicalSecretaryFinite` |
| 20 | `cor:secretary-asymptotic` | `secretary_asymptotic`; compatibility form `secretary_asymptotic_of_external` | `MomentAmbiguity/Secretary.lean` | Fully verified | Internal finite equality plus the separately proved `classicalSecretaryLimit` |
| 21 | `cor:order-stat-separator` | `order_stat_separator`, `prophetKappa` | `ProphetSeparator.lean`, `Prophet.lean` | Fully verified | `r ≥ 1`; exact `κ_r`, size conditions, both `6/n` tails |
| 22 | `thm:prophet` | `prophet_upper_bound`, `prophet`; compatibility form `prophet_of_external` | `MomentAmbiguity/Prophet.lean` | Fully verified | Upper direction internal; lower direction uses the internally proved bucket-threshold witness |
| 23 | `prop:log-lowerbound` | `prophet_log_lower_bound`, `correaLogLowerBound`; compatibility form `prophet_log_lower_bound_of_external` | `Prophet.lean`, `CorreaLower.lean` | Fully verified | Measurable causal dyadic bucket policy; explicit `a = log 2 / 8`, `m_lb = 2` |
| 24 | `cor:prophet-r-selection` | `prophet_r_selection_of_upper_witness`, `prophet_r_selection` | `MomentAmbiguity/ProphetMultiSelection.lean` | Fully verified | Depends only on the proved prophet upper construction; applies to the potentially larger marginal-causal terminal-set policy class |
| 25 | `prop:key-prop-1_extended` | `BinarySeparator.finiteWeight_existsUnique`, `BinarySeparator.key_prop_1_extended` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | `n,B ≥ 3`; positive-index source convention |
| 26 | `lem:limit-weights-exist` | `BinarySeparator.finiteWeight_tendsto_limitWeight` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Every fixed index, correct eventual `K` domain |
| 27 | `lem:all-moment-weight-decay` | `BinarySeparator.all_moment_weight_decay` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Every `M ≥ 1`; exact `L_M,C_M` |
| 28 | `lem:all-moment-weight-decay-uniform-K` | `BinarySeparator.all_moment_weight_decay_uniform_K` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Uniform in `K`, source domain `j ≤ K+2` |
| 29 | `lem:all-moments-signed-identity` | `BinarySeparator.limitWeight_signed_moment_identity` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Every natural moment order |
| 30 | `cor:limit-probabilities-well-defined` | `summable_abs_limitWeight`, `normalizer_eq_odd`, `normalizer_pos`, atom/support laws, `limit_probabilities_atom_sum_and_decay` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Absolute summability, common positive normalization, and exact normalized all-order atom bound |
| 31 | `lem:all-moments-limit` | `hasFiniteMoments_muLaw`, `hasFiniteMoments_nuLaw`, `momentEquivalent_muLaw_nuLaw` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Integrability and equality for every order |
| 32 | `lem:explicit-support-bounds` | `BinarySeparator.Data.explicit_support_bounds` | `MomentAmbiguity/BinarySeparator.lean` | Fully verified | Exact four simultaneous bounds |
| 33 | `prop:key-prop-2-ext` | `key_prop_2_ext`, `nwayDistribution_singleton`, `nwayMass_toReal_of_modEq`, `nwayNormalizer_eq_residue` | `NWayCoefficients.lean`, `NWaySeparator.lean` | Fully verified | `B,N ≥ 2`; exact normalized atom formula, common normalizer, supports, moments, and coefficients |
| 34 | `lem:N-class-coeff-formula` | `nway_hasProdLocallyUniformly`, `differentiable_nwayInfiniteProduct`, `nwayFiniteCoeff_formula`, `nwayFiniteCoeff_mono_succ`, `monotone_nwayFiniteCoeff`, `tendsto_nwayFiniteCoeff`, `tendsto_nwayFiniteCoeff_real`, `nwayCoeff_eq_infiniteDigitConfig_tsum` | `MomentAmbiguity/NWayCoefficients.lean` | Fully verified | `B,N ≥ 2`; the displayed infinite digit sum is a `tsum` over finitely supported configurations |
| 35 | `lem:N-class-moment-matching` | `nwayResidueMoment_eq_common`, `nwayNormalizer_eq_product`, exact dyadic-product bounds | `NWayCoefficients.lean`, `SeriesBounds.lean` | Fully verified | Fourier residue cancellation; `9/32`, `32/9 < 4` exact |
| 36 | `lem:N-class-all-moments` | `nwayDistribution_hasFiniteMoments`, `nwayDistribution_momentEquivalent` | `MomentAmbiguity/NWaySeparator.lean` | Fully verified | Every residue and natural order |
| 37 | `lem:N-class-coeff-bounds` | `nwayCoeff_lower_bound`, `nwayCoeff_upper_bound`, `nway_index_sub_exponent_le`, `nway_index_sub_exponent_eq_iff` | `MomentAmbiguity/NWayCoefficients.lean` | Fully verified | Exact `e(j)` and equality range |

Final classification: **37 fully verified, 0 conditionally verified, 0 unresolved**.

## Internally proved source results

The source-facing propositions in `MomentAmbiguity/External/` provide named interfaces for
results that are not available in mathlib. Their implementations are:

- `finiteRamseyPrinciple`: finite ordered hypergraph Ramsey;
- `classicalSecretaryUpperBound` and `classicalSecretaryAttainment`: the exact finite classical
  secretary value;
- `classicalSecretaryLimit`: convergence of the finite secretary value to `1/e`;
- `correaLogLowerBound`: the logarithmic prophet guarantee from a dyadic bucket-threshold
  policy.

The canonical manuscript results use these proved implementations. The `_of_external` variants
retain the proposition interfaces for reuse and comparison.

## Regression coverage

`MomentAmbiguity/Regression.lean` and `MomentAmbiguity/ClosedRegression.lean` check the requested edge cases:

- secretary horizon `m=1` and the explicit `r=1` branch;
- the `N=2` residue separator;
- quantile endpoint conventions at `u=0,1`;
- newsvendor `β=0,1`;
- repeated order-statistic values;
- an all-zero prophet benchmark with multiplication-form guarantees;
- a concrete negative `C_N` exponent;
- the exact `9/32`, `32/9`, and `<4` normalization constants;
- finite Ramsey at zero uniformity/target size, one colour, and larger ambient horizons;
- the exact finite secretary LP at `m=1`, the `1/e` limit witness, and its floor-ratio core;
- prophet bucket counts at `m=2` and powers of two, equality at the stopping threshold,
  repeated maxima, a zero-benchmark multiplication guarantee, and positivity of
  `log 2 / 8`.

`MomentAmbiguity/AxiomAudit.lean` runs `#print axioms` on the principal separator, quantile,
newsvendor, pricing, secretary, prophet-upper, two-sided prophet, and multi-selection results.
Every audited declaration has exactly the standard Lean foundations `propext`,
`Classical.choice`, and `Quot.sound`, and no others.  The file audits all internal interface
inhabitants and the five formerly conditional canonical manuscript results.

## Verification summary

`lake build` checks the complete development. A source scan rejects proof holes and
project-defined trust escapes, while `MomentAmbiguity/AxiomAudit.lean` reports the standard Lean
foundations used by the principal results. The traceability count is 37 fully verified,
0 conditional, and 0 unresolved.
