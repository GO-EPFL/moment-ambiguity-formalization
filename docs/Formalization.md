# Paper statements and Lean proofs

This project accompanies *Moment Ambiguity and the Limits of Robust Stochastic Optimization*.
The paper explains the mathematics; this guide helps you find the corresponding Lean statements,
understand their formal models, and check the proofs.
For installation and the build command, start with the [README](../README.md).

The current paper has **36 numbered definitions and results**: two definitions and 34 theorems,
lemmas, propositions, and corollaries. All are represented below. Each listed result is proved
in Lean under the model and hypotheses described here.
Remarks, equations, and background prose are not part of this count.

## Reading the project

The shortest route to an application is its main result file:

| Paper topic | Start here |
|---|---|
| Moment classes and disclosed information | [Basic.lean](../MomentAmbiguity/Foundation/Basic.lean) |
| Binary and N-way constructions | [BinarySeparator.lean](../MomentAmbiguity/BinarySeparator.lean), [NWaySeparator.lean](../MomentAmbiguity/NWaySeparator.lean) |
| Quantiles, risk measures, and chance constraints | [Quantile.lean](../MomentAmbiguity/Quantile.lean) |
| Newsvendor and posted pricing | [Newsvendor.lean](../MomentAmbiguity/Newsvendor.lean), [Pricing.lean](../MomentAmbiguity/Pricing.lean) |
| Secretary success, independent and i.i.d. inputs | [Secretary.lean](../MomentAmbiguity/Secretary.lean) |
| Prophet and multiple-selection bounds | [Prophet.lean](../MomentAmbiguity/Prophet.lean), [ProphetMultiSelection.lean](../MomentAmbiguity/ProphetMultiSelection.lean) |

All declaration names below are in the `MomentAmbiguity` namespace; for example,
`full_secretary_success_both` means `MomentAmbiguity.full_secretary_success_both`.
A link opens the file containing that declaration. Search the displayed name within the file
to read its exact type and proof. Paper numbers and LaTeX labels are both provided because
numbers can change when the manuscript is edited.

## From the paper to Lean

The table follows the order of the paper. A definition row identifies its implementation;
all other rows identify proved declarations. The two separator theorems each have two LaTeX
labels, which refer to the same numbered statement.

| Paper statement | LaTeX label(s) | Lean declaration(s) | Scope and assumptions |
|---|---|---|---|
| Definition 2.1 | `def:stieltjes-type-class` | [momentClass](../MomentAmbiguity/Foundation/Basic.lean)<br>[IsStieltjesTypeClass](../MomentAmbiguity/Foundation/Basic.lean) | All moments must be finite; the common sequence is an explicit parameter. |
| Definition 2.2 | `def:moment-based-policy` | [IsMomentBased](../MomentAmbiguity/Foundation/Basic.lean)<br>[SecretaryPolicy](../MomentAmbiguity/Foundation/OnlinePolicy.lean)<br>[ProphetPolicy](../MomentAmbiguity/Foundation/OnlinePolicy.lean)<br>[MultiSelectionPolicy](../MomentAmbiguity/Foundation/OnlinePolicy.lean) | Measurable dependence on disclosed moments and causal observations; see the policy representation below. |
| Lemma 3.1 | `lem:finite-binary-vandermonde` | [finite_binary_vandermonde](../MomentAmbiguity/Construction/Vandermonde.lean)<br>[finite_binary_vandermonde_with_integrability](../MomentAmbiguity/Construction/Vandermonde.lean) | Strictly increasing real nodes; k ≥ 2; explicit moment integrability. |
| Theorem 3.1 | `prop:key-prop-1`<br>`thm:binary-separator` | [BinarySeparator.binary_separator](../MomentAmbiguity/BinarySeparator.lean) | Integer n,B ≥ 3; includes the stronger index-zero decay bound. |
| Theorem 3.2 | `prop:key-prop-2`<br>`thm:nway-separator` | [nway_separator](../MomentAmbiguity/NWaySeparator.lean)<br>[nwayDistribution_singleton](../MomentAmbiguity/NWaySeparator.lean)<br>[hasSum_nwayCoeff](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayNormalizer_eq_residue](../MomentAmbiguity/Construction/NWayCoefficients.lean) | Integer B,N ≥ 2; exact coefficients, normalized atoms, supports, moments, and bounds. |
| Corollary 4.1 | `cor:quantile-separation` | [quantile_separation](../MomentAmbiguity/Quantile.lean) | β ∈ [1/2,1), integer B ≥ 3. |
| Corollary 4.2 | `cor:risk-quantile-separation` | [BinarySeparator.Data.risk_quantile_separation_var](../MomentAmbiguity/Quantile.lean)<br>[BinarySeparator.Data.risk_quantile_separation_lcvar](../MomentAmbiguity/Quantile.lean) | Exact VaR and lower-CVaR claims on the paper's stated ranges. |
| Corollary 4.3 | `cor:chance-capacity` | [chance_capacity_measurable](../MomentAmbiguity/Quantile.lean) | Real B ≥ 3; measurable moment-based rule with uniform feasibility over its moment class. |
| Lemma 4.1 | `lem:newsvendor-critical-fractile` | [newsvendor_critical_fractile](../MomentAmbiguity/Newsvendor.lean) | β ∈ [0,1]; finite first demand moment. |
| Lemma 4.2 | `lem:newsvendor-randomization` | [newsvendor_randomization](../MomentAmbiguity/Newsvendor.lean)<br>[randomizedProfitIntegrable](../MomentAmbiguity/Newsvendor.lean) | Demand and randomized order both have finite first moments. |
| Lemma 4.3 | `lem:newsvendor-optima` | [newsvendor_optima](../MomentAmbiguity/Newsvendor.lean) | The paper's β, ε, B, and n inequalities; includes positivity of the optima. |
| Theorem 4.1 | `thm:newsvendor` | [newsvendor_universal_guarantee](../MomentAmbiguity/Newsvendor.lean)<br>[newsvendor_impossibility](../MomentAmbiguity/Newsvendor.lean) | Fixed and randomized orders; ratios are used only with positive optimal profit. |
| Theorem 5.1 | `thm:revenue-deterministic` | [revenue_deterministic_universal](../MomentAmbiguity/Pricing.lean)<br>[revenue_deterministic](../MomentAmbiguity/Pricing.lean) | ε ∈ (0,1); positive posted prices. |
| Lemma 5.1 | `lem:N-class-revenue-localization` | [N_class_revenue_localization](../MomentAmbiguity/Pricing.lean)<br>[summable_pricingSeriesTerm](../MomentAmbiguity/Pricing.lean) | Integer B,N ≥ 2; the series defining C_N uses integer powers. |
| Theorem 5.2 | `thm:randomized-pricing-all-moments` | [randomized_pricing_all_moments_universal](../MomentAmbiguity/Pricing.lean)<br>[randomized_pricing_all_moments](../MomentAmbiguity/Pricing.lean) | Preserves the order: choose the family before the randomized price, then choose a hard family member. |
| Corollary 6.1 | `cor:first-atom-concentration` | [first_atom_concentration](../MomentAmbiguity/NWaySeparator.lean)<br>[first_atom_concentration_exists](../MomentAmbiguity/NWaySeparator.lean) | Convergence as the integer base grows, uniform over all N residue classes. |
| Lemma 6.1 | `lem:ramsey-erasure` | [ramsey_erasure_iid](../MomentAmbiguity/Secretary.lean)<br>[ramsey_erasure_iid_grid](../MomentAmbiguity/Secretary/IIDRamsey.lean) | Any k ≥ m ≥ 1; uniform independent grid draws; exact error ε + choose(m,2)/k. |
| Theorem 6.1 | `thm:full-secretary-success` | [full_secretary_success_both](../MomentAmbiguity/Secretary.lean)<br>[secretaryIID_fixedMomentClass_upper](../MomentAmbiguity/Secretary.lean) | Both independent and i.i.d. robust values equal s_m for every m ≥ 1; the common disclosure precedes policy choice. |
| Corollary 6.2 | `cor:secretary-asymptotic` | [secretary_asymptotic](../MomentAmbiguity/Secretary.lean)<br>[secretary_iid_asymptotic](../MomentAmbiguity/Secretary.lean) | Both robust values converge to 1/e. |
| Corollary 7.1 | `cor:order-stat-separator` | [order_stat_separator](../MomentAmbiguity/Prophet/Separator.lean)<br>[prophetKappa](../MomentAmbiguity/Prophet.lean) | Fixed r ≥ 1; exact κ_r and both 6/n tail bounds, under the paper's size conditions. |
| Theorem 7.1 | `thm:prophet` | [prophet_upper_bound](../MomentAmbiguity/Prophet.lean)<br>[prophet](../MomentAmbiguity/Prophet.lean) | For each fixed r ≥ 1; constants and the minimum horizon may depend on r. |
| Proposition 7.1 | `prop:log-lowerbound` | [prophet_log_lower_bound](../MomentAmbiguity/Prophet.lean)<br>[correaLogLowerBound](../MomentAmbiguity/Prophet/LogLowerBound.lean) | Explicit dyadic bucket policy, with a = log(2)/8 and minimum horizon 2. |
| Corollary 7.2 | `cor:prophet-r-selection` | [prophet_r_selection](../MomentAmbiguity/ProphetMultiSelection.lean) | Upper bound for the broader class with causal selection-membership marginals described below. |
| Proposition 8.1 | `prop:key-prop-1_extended` | [BinarySeparator.finiteWeight_existsUnique](../MomentAmbiguity/BinarySeparator.lean)<br>[BinarySeparator.key_prop_1_extended](../MomentAmbiguity/BinarySeparator.lean) | Integer n,B ≥ 3; finite uniqueness and the limiting construction; positive-index convention for this statement. |
| Lemma 8.1 | `lem:limit-weights-exist` | [BinarySeparator.finiteWeight_tendsto_limitWeight](../MomentAmbiguity/BinarySeparator.lean) | Each fixed coefficient converges as the truncation grows. |
| Lemma 8.2 | `lem:all-moment-weight-decay` | [BinarySeparator.all_moment_weight_decay](../MomentAmbiguity/BinarySeparator.lean) | Every M ≥ 1, with the displayed cutoff and decay constant. |
| Lemma 8.3 | `lem:all-moment-weight-decay-uniform-K` | [BinarySeparator.all_moment_weight_decay_uniform_K](../MomentAmbiguity/BinarySeparator.lean) | Uniform in the truncation K for j ≤ K+2. |
| Lemma 8.4 | `lem:all-moments-signed-identity` | [BinarySeparator.limitWeight_signed_moment_identity](../MomentAmbiguity/BinarySeparator.lean) | Signed cancellation for every nonnegative integer moment order. |
| Corollary 8.1 | `cor:limit-probabilities-well-defined` | [BinarySeparator.summable_abs_limitWeight](../MomentAmbiguity/BinarySeparator.lean)<br>[BinarySeparator.normalizer_eq_odd](../MomentAmbiguity/BinarySeparator.lean)<br>[BinarySeparator.normalizer_pos](../MomentAmbiguity/BinarySeparator.lean)<br>[BinarySeparator.limit_probabilities_atom_sum_and_decay](../MomentAmbiguity/BinarySeparator.lean) | Absolute summability, common positive normalization, and the normalized all-order atom bound. |
| Lemma 8.5 | `lem:all-moments-limit` | [BinarySeparator.hasFiniteMoments_muLaw](../MomentAmbiguity/BinarySeparator.lean)<br>[BinarySeparator.hasFiniteMoments_nuLaw](../MomentAmbiguity/BinarySeparator.lean)<br>[BinarySeparator.momentEquivalent_muLaw_nuLaw](../MomentAmbiguity/BinarySeparator.lean) | Integrability and moment equality for every nonnegative integer order. |
| Lemma 8.6 | `lem:explicit-support-bounds` | [BinarySeparator.Data.explicit_support_bounds](../MomentAmbiguity/BinarySeparator.lean) | The four simultaneous bounds, with the paper's constants. |
| Proposition 8.2 | `prop:key-prop-2-ext` | [key_prop_2_ext](../MomentAmbiguity/NWaySeparator.lean)<br>[nwayDistribution_singleton](../MomentAmbiguity/NWaySeparator.lean)<br>[nwayNormalizer_eq_residue](../MomentAmbiguity/Construction/NWayCoefficients.lean) | Integer B,N ≥ 2; common normalization, atom formula, support, moment, and coefficient claims. |
| Lemma 8.7 | `lem:N-class-coeff-formula` | [nway_hasProdLocallyUniformly](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[differentiable_nwayInfiniteProduct](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayFiniteCoeff_formula](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[monotone_nwayFiniteCoeff](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[tendsto_nwayFiniteCoeff](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayCoeff_eq_infiniteDigitConfig_tsum](../MomentAmbiguity/Construction/NWayCoefficients.lean) | Local uniform convergence and the entire product; finite and infinite digit formulas; monotone coefficient limits. |
| Lemma 8.8 | `lem:N-class-moment-matching` | [nwayResidueMoment_eq_common](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayNormalizer_eq_product](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayNormalizer_ge_one](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayNormalizer_lt_four](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[dyadic_infinite_product_ge_nine_thirty_two](../MomentAmbiguity/Construction/SeriesBounds.lean)<br>[dyadic_reciprocal_infinite_product_le_thirty_two_nine](../MomentAmbiguity/Construction/SeriesBounds.lean) | Fourier residue cancellation and the exact normalization bounds, including 9/32 and 32/9. |
| Lemma 8.9 | `lem:N-class-all-moments` | [nwayDistribution_hasFiniteMoments](../MomentAmbiguity/NWaySeparator.lean)<br>[nwayDistribution_momentEquivalent](../MomentAmbiguity/NWaySeparator.lean) | All residues and all nonnegative integer moment orders. |
| Lemma 8.10 | `lem:N-class-coeff-bounds` | [nwayCoeff_lower_bound](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nwayCoeff_upper_bound](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nway_index_sub_exponent_le](../MomentAmbiguity/Construction/NWayCoefficients.lean)<br>[nway_index_sub_exponent_eq_iff](../MomentAmbiguity/Construction/NWayCoefficients.lean) | Exact exponent e(j), both coefficient bounds, and the equality range. |

## How the mathematical model is represented

**Laws and moments.** `Distribution` is a Borel probability measure on the nonnegative reals
(`ProbabilityMeasure ℝ≥0`). The finite Vandermonde lemma also allows arbitrary real nodes.
`MomentEquivalent` requires integrability of every moment on both sides as well as equality
of their full sequences. Thus equality of totalized integrals cannot disguise an infinite
moment. `SupportedOn` means that a set has probability one, exactly as in the paper; it does
not mean topological support.

**Disclosed information and policies.** A `MomentProfile m` supplies one full moment sequence
for each labeled coordinate. In [OnlinePolicy.lean](../MomentAmbiguity/Foundation/OnlinePolicy.lean),
secretary and prophet policies are measurable Markov kernels from that disclosure and a
realized path to a selection time, with `none` for no selection. The probability of selecting
at time `t` must depend only on the observations through `t`. Secretary observations contain
both labels and cardinal values, and the uniformly random arrival permutation is independent
of the product value law.

These are *causal terminal selection masses*. The project does not separately define
hazard-based behavioral stopping rules or prove their finite-horizon representation
equivalence with these kernels. The formal theorems should be read with this precise policy
representation in mind.

For `MultiSelectionPolicy`, causality is imposed on each selection-membership marginal and
at most `r` times are selected almost surely. Suffix-dependent correlations in the terminal
set are not excluded, so this class may be larger than sequentially implementable joint
selection laws. The upper bound in Corollary 7.2 holds for this larger class and uses only
its causal marginals.

**Robust values.** `robustSecretaryValue`, `robustSecretaryIIDValue`, and the prophet quantity
`rhoMom` are suprema of nonnegative universal guarantees. The i.i.d. value allows a policy
chosen for the i.i.d. model; its guarantee is tested only on products of one common law.
Prophet guarantees use multiplication by the benchmark, so an all-zero benchmark does not
cause division by zero. The feasible sets needed for these suprema are proved nonempty
and bounded. The prophet statements fix `r` before choosing constants and the minimum horizon;
they do not assert bounds uniform in a growing `r`.

For the secretary upper bound, `secretaryIID_fixedMomentClass_upper` chooses a common moment
sequence before the policy: `∀ m ≥ 1, ∀ ε > 0, ∃ seq, ∀ policy, ∃ law ∈ momentClass seq`.
Its hard instance uses a product of the common mixture law. The component indices are sampled
independently for each coordinate, as proved by `independentValues_uniformMixture`.

**Risk measures, decisions, and indices.** The quantile is set to zero outside `(0,1)`.
Its value at the null endpoint `u=0` therefore does not change the LCVaR integral. A randomized
newsvendor order is a law on nonnegative quantities with a finite first moment; a randomized
price is a law on strictly positive prices and needs no moment condition. The optimal price
benchmark permits a zero threshold, whose zero revenue leaves the supremum unchanged.
Corollary 4.3 permits real `B ≥ 3`, using the integer separator at `⌈B⌉`.

Order statistics range over coordinate indices, so equal numerical values retain their
multiplicity; a valid rank packages `1 ≤ r ≤ m`. Integer powers are used wherever the paper
allows negative exponents, including `C_N`. In Proposition 8.1, positive indices are encoded
as `0 < j`; the headline binary theorem also proves the index-zero bound. Tail expectations
for i.i.d. samples are expressed as `n` times a one-coordinate integral, with the product-law
equality and integrability proved separately.

## Supporting results

These reusable results support the paper or make consequences of its constructions explicit;
they are separate from the 36 numbered statements above.

| Result | Lean declaration(s) | What is proved |
|---|---|---|
| Maximal total variation | [exists_full_momentClass_injective_pairwise_maximalTV](../MomentAmbiguity/Construction/TotalVariation.lean) | An injective N-law family in one full moment class, pairwise at distance one, for N ≥ 2. |
| Large homogeneous sets | [finiteRamsey_largeHomogeneousSet](../MomentAmbiguity/Secretary/LargeRamsey.lean) | The finite Ramsey theorem with any requested homogeneous-set size k ≥ m. |
| Exact collision correction | [finiteIIDAverage_le_of_permutation_average_choose](../MomentAmbiguity/Foundation/FiniteIID.lean) | Label-sensitive permutation averaging for independent samples, with choose(m,2)/k error. |
| Mixtures and independent sampling | [uniformMixture_mem_momentClass](../MomentAmbiguity/Secretary/Mixture.lean)<br>[independentValues_uniformMixture](../MomentAmbiguity/Secretary/Mixture.lean)<br>[secretarySuccessProbabilityAtProfile_uniformMixture_le_grid](../MomentAmbiguity/Secretary/Mixture.lean) | Full moments are preserved; the product law samples component indices independently; designated-atom transfer costs at most mδ. |
| Finite Ramsey | [finiteRamseyPrinciple](../MomentAmbiguity/Secretary/Ramsey.lean) | Proved from the ordered finite hypergraph development. |
| Classical finite secretary value | [classicalSecretaryUpperBound](../MomentAmbiguity/Secretary/Classical.lean)<br>[classicalSecretaryAttainment](../MomentAmbiguity/Secretary/Classical.lean) | A proved upper bound and an explicit attaining policy. |
| Classical secretary limit | [classicalSecretaryLimit](../MomentAmbiguity/Secretary/Limit.lean) | A proof that s_m tends to 1/e. |

The [Ramsey interface](../MomentAmbiguity/Secretary/RamseyInterface.lean),
[classical secretary interface](../MomentAmbiguity/Secretary/ClassicalInterface.lean), and
[prophet lower-bound interface](../MomentAmbiguity/Prophet/LogLowerBoundInterface.lean)
state the intermediate specifications used in those proofs. They use the namespace
`MomentAmbiguity.External`. Each specification has a proved implementation in this project.
The main application results use those implementations; variants ending in `_of_external`
expose the specifications as parameters for reuse.

## Checking the development

The toolchain and mathlib revision are pinned in [lean-toolchain](../lean-toolchain),
[lakefile.toml](../lakefile.toml), and [lake-manifest.json](../lake-manifest.json).
The [README](../README.md) gives the reproducible build and verification commands.

[Verification/Regression.lean](../MomentAmbiguity/Verification/Regression.lean) checks
application edge cases, including quantile endpoints, newsvendor boundary parameters,
repeated order-statistic values, zero prophet benchmarks, negative pricing exponents, and
separator normalization constants.
[Verification/FoundationRegression.lean](../MomentAmbiguity/Verification/FoundationRegression.lean)
checks Ramsey edge cases, the finite secretary value and its limit, and the dyadic prophet policy.
[Verification/IIDRegression.lean](../MomentAmbiguity/Verification/IIDRegression.lean) checks
horizon one, the exact two-draw binary collision probability, singleton mixtures, equality of
the independent and i.i.d. values, and a common disclosure against two arbitrary policies.

[Verification/AxiomAudit.lean](../MomentAmbiguity/Verification/AxiomAudit.lean) prints the logical
dependencies of the principal results. The only allowed foundations
are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; the project introduces no
additional axioms or unfinished proofs. A successful build checks proof terms; the model
notes above state the separate interpretation choices needed when comparing them to the paper.
