import MomentAmbiguity.Prophet.PolicyAnalysis
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Exponential bucketing for the moment-disclosure prophet inequality

This file formalizes the positive argument in the cited STOC manuscript:
`lem:baseline`, `alg:bucket`, and `thm:random-bucket-threshold`.  The policy uses only the
disclosed first moments.  It samples one of `ceil (log_2 m)` dyadic thresholds and accepts the
first value weakly above that threshold.
-/

open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-! ## The measurable bucket policy -/

/-- Rank one at a positive horizon, kept internal to the closed proof. -/
def prophetFirstRank (m : ℕ) (hm : 1 ≤ m) : ValidRank m := ⟨1, le_rfl, hm⟩

/-- For `m >= 2`, this is exactly `ceil (log_2 m)`.  The formula is convenient over naturals. -/
def prophetBucketCount (m : ℕ) : ℕ := Nat.log 2 (m - 1) + 1

theorem prophetBucketCount_pos (m : ℕ) : 0 < prophetBucketCount m := by
  simp [prophetBucketCount]

/-- Largest disclosed first moment, truncated at zero on arbitrary (possibly invalid) profiles.
On profiles arising from probability laws, the truncation is inactive. -/
def profileMaxFirstMoment {m : ℕ} (profile : MomentProfile m) : ℝ≥0 :=
  Finset.univ.sup fun i ↦ Real.toNNReal (profile i 1)

theorem measurable_profileMaxFirstMoment {m : ℕ} :
    Measurable (profileMaxFirstMoment : MomentProfile m → ℝ≥0) := by
  classical
  unfold profileMaxFirstMoment
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simpa only [Finset.sup_insert] using
        ((measurable_pi_apply 1).comp (measurable_pi_apply a)).real_toNNReal.max ih

/-- Dyadic threshold `2^j mu^star / 2` used by the bucketing algorithm. -/
def prophetBucketThreshold {m : ℕ} (profile : MomentProfile m) (j : ℕ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ j * profileMaxFirstMoment profile / 2

theorem measurable_prophetBucketThreshold {m : ℕ} (j : ℕ) :
    Measurable (fun profile : MomentProfile m ↦ prophetBucketThreshold profile j) := by
  unfold prophetBucketThreshold
  exact (measurable_const.mul (measurable_profileMaxFirstMoment (m := m))).div_const 2

/-- Indices whose values meet a closed threshold. -/
def prophetHitSet {m : ℕ} (threshold : ℝ≥0) (x : ProphetPath m) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ threshold ≤ x i

/-- First index weakly above a threshold, with `none` when the threshold is never reached. -/
def prophetFirstAbove {m : ℕ} (threshold : ℝ≥0) (x : ProphetPath m) : Option (Fin m) :=
  if h : (prophetHitSet threshold x).Nonempty then
    some ((prophetHitSet threshold x).min' h)
  else none

theorem prophetFirstAbove_eq_some_iff {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) (t : Fin m) :
    prophetFirstAbove threshold x = some t ↔
      threshold ≤ x t ∧ ∀ i : Fin m, i < t → x i < threshold := by
  classical
  unfold prophetFirstAbove
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · intro hmin
      have htmem : t ∈ prophetHitSet threshold x := by
        rw [← hmin]
        exact Finset.min'_mem _ _
      refine ⟨(Finset.mem_filter.1 htmem).2, ?_⟩
      intro i hit
      by_contra hnot
      have himem : i ∈ prophetHitSet threshold x := by
        simp only [prophetHitSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_of_not_gt hnot
      have hle := Finset.min'_le (prophetHitSet threshold x) i himem
      rw [hmin] at hle
      exact (not_le_of_gt hit) hle
    · rintro ⟨htt, hprev⟩
      apply le_antisymm
      · exact Finset.min'_le _ _ (by simp [prophetHitSet, htt])
      · by_contra hnot
        have hlt : (prophetHitSet threshold x).min' h < t := lt_of_not_ge hnot
        have hmem := Finset.min'_mem (prophetHitSet threshold x) h
        have hthreshold : threshold ≤ x ((prophetHitSet threshold x).min' h) :=
          (Finset.mem_filter.1 hmem).2
        exact (not_le_of_gt (hprev _ hlt)) hthreshold
  · constructor
    · intro heq
      cases heq
    · rintro ⟨htt, _⟩
      exact (h ⟨t, by simp [prophetHitSet, htt]⟩).elim

theorem prophetFirstAbove_eq_none_iff {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) :
    prophetFirstAbove threshold x = none ↔ ∀ i : Fin m, x i < threshold := by
  classical
  unfold prophetFirstAbove
  split_ifs with h
  · simp only [false_iff]
    intro hall
    obtain ⟨i, hi⟩ := h
    exact (not_le_of_gt (hall i)) (Finset.mem_filter.1 hi).2
  · simp only [true_iff]
    intro i
    by_contra hnot
    apply h
    exact ⟨i, by simp [prophetHitSet, le_of_not_gt hnot]⟩

theorem measurable_prophetFirstAbove {m : ℕ} :
    Measurable (fun z : ℝ≥0 × ProphetPath m ↦ prophetFirstAbove z.1 z.2) := by
  apply measurable_to_countable'
  intro choice
  cases choice with
  | none =>
      have hset :
          (fun z : ℝ≥0 × ProphetPath m ↦ prophetFirstAbove z.1 z.2) ⁻¹' {none} =
            ⋂ i : Fin m, {z | z.2 i < z.1} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
        exact prophetFirstAbove_eq_none_iff z.1 z.2
      rw [hset]
      exact MeasurableSet.iInter fun i ↦
        measurableSet_lt ((measurable_pi_apply i).comp measurable_snd) measurable_fst
  | some t =>
      have hset :
          (fun z : ℝ≥0 × ProphetPath m ↦ prophetFirstAbove z.1 z.2) ⁻¹' {some t} =
            {z | z.1 ≤ z.2 t} ∩ ⋂ i : {i : Fin m // i < t}, {z | z.2 i.1 < z.1} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_setOf_eq, Set.mem_iInter]
        rw [prophetFirstAbove_eq_some_iff]
        constructor
        · rintro ⟨ht, hp⟩
          exact ⟨ht, fun i ↦ hp i.1 i.2⟩
        · rintro ⟨ht, hp⟩
          exact ⟨ht, fun i hi ↦ hp ⟨i, hi⟩⟩
      rw [hset]
      exact (measurableSet_le measurable_fst
        ((measurable_pi_apply t).comp measurable_snd)).inter
          (MeasurableSet.iInter fun (i : {i : Fin m // i < t}) ↦
            measurableSet_lt ((measurable_pi_apply i.1).comp measurable_snd) measurable_fst)

/-- Uniform bucket seed. -/
def prophetBucketSeedLaw (m : ℕ) : ProbabilityMeasure (Fin (prophetBucketCount m)) :=
  letI : Nonempty (Fin (prophetBucketCount m)) :=
    ⟨⟨0, prophetBucketCount_pos m⟩⟩
  pmfProbabilityMeasure (PMF.uniformOfFintype (Fin (prophetBucketCount m)))

/-- Decision made from a profile/path pair and a sampled bucket. -/
def prophetBucketDecision {m : ℕ}
    (z : (MomentProfile m × ProphetPath m) × Fin (prophetBucketCount m)) :
    Option (Fin m) :=
  prophetFirstAbove (prophetBucketThreshold z.1.1 z.2.1) z.1.2

theorem measurable_prophetBucketDecision {m : ℕ} :
    Measurable (prophetBucketDecision :
      (MomentProfile m × ProphetPath m) × Fin (prophetBucketCount m) → Option (Fin m)) := by
  apply measurable_from_prod_countable_left
  intro j
  have hpair : Measurable
      (fun z : MomentProfile m × ProphetPath m ↦
        (prophetBucketThreshold z.1 j.1, z.2)) :=
    ((measurable_prophetBucketThreshold (m := m) j.1).comp measurable_fst).prodMk
      measurable_snd
  change Measurable
    ((fun z : ℝ≥0 × ProphetPath m ↦ prophetFirstAbove z.1 z.2) ∘
      fun z : MomentProfile m × ProphetPath m ↦
        (prophetBucketThreshold z.1 j.1, z.2))
  exact (measurable_prophetFirstAbove (m := m)).comp hpair

/-- The uniform-random-bucket kernel.  It first retains its input, independently samples the
bucket, and then maps the pair to the first threshold crossing. -/
def prophetBucketKernel (m : ℕ) :
    Kernel (MomentProfile m × ProphetPath m) (Option (Fin m)) :=
  (((Kernel.id : Kernel (MomentProfile m × ProphetPath m)
      (MomentProfile m × ProphetPath m)) ×ₖ
      Kernel.const (MomentProfile m × ProphetPath m)
        (prophetBucketSeedLaw m : Measure (Fin (prophetBucketCount m)))).map
    prophetBucketDecision)

instance prophetBucketKernel_isMarkov (m : ℕ) : IsMarkovKernel (prophetBucketKernel m) := by
  unfold prophetBucketKernel
  exact Kernel.IsMarkovKernel.map _ measurable_prophetBucketDecision

theorem prophetBucketKernel_apply (m : ℕ)
    (input : MomentProfile m × ProphetPath m) :
    prophetBucketKernel m input =
      (prophetBucketSeedLaw m : Measure (Fin (prophetBucketCount m))).map
        (fun j ↦ prophetBucketDecision (input, j)) := by
  rw [prophetBucketKernel, Kernel.map_apply _ measurable_prophetBucketDecision,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map]
  · rfl
  · exact measurable_prophetBucketDecision
  · exact measurable_const.prodMk measurable_id

theorem prophetBucketKernel_singleton (m : ℕ)
    (input : MomentProfile m × ProphetPath m) (t : Fin m) :
    prophetBucketKernel m input {some t} =
      (prophetBucketSeedLaw m : Measure (Fin (prophetBucketCount m)))
        {j | prophetBucketDecision (input, j) = some t} := by
  rw [prophetBucketKernel_apply]
  exact Measure.map_apply
    (measurable_prophetBucketDecision.comp (measurable_const.prodMk measurable_id))
    (measurableSet_singleton (some t))

/-- `alg:bucket`: a measurable causal policy based only on the disclosed first moments. -/
def prophetBucketPolicy (m : ℕ) : ProphetPolicy m where
  kernel := prophetBucketKernel m
  isMarkov := inferInstance
  causal := by
    intro profile x y t hxy
    rw [prophetBucketKernel_singleton, prophetBucketKernel_singleton]
    congr 1
    ext j
    simp only [Set.mem_setOf_eq, prophetBucketDecision]
    rw [prophetFirstAbove_eq_some_iff, prophetFirstAbove_eq_some_iff]
    constructor
    · rintro ⟨ht, hp⟩
      refine ⟨?_, ?_⟩
      · simpa [hxy t le_rfl] using ht
      · intro i hi
        simpa [hxy i (le_of_lt hi)] using hp i hi
    · rintro ⟨ht, hp⟩
      refine ⟨?_, ?_⟩
      · simpa [hxy t le_rfl] using ht
      · intro i hi
        simpa [hxy i (le_of_lt hi)] using hp i hi

/-- Uniform bucket integration is finite averaging. -/
theorem prophetBucketSeedLaw_integral_eq_average (m : ℕ)
    (f : Fin (prophetBucketCount m) → ℝ) :
    (∫ j, f j ∂(prophetBucketSeedLaw m : Measure _)) =
      ((prophetBucketCount m : ℝ)⁻¹) * ∑ j, f j := by
  unfold prophetBucketSeedLaw
  letI : Nonempty (Fin (prophetBucketCount m)) :=
    ⟨⟨0, prophetBucketCount_pos m⟩⟩
  rw [coe_pmfProbabilityMeasure, PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Fintype.card_fin]

/-! ## Fixed-threshold reward analysis -/

/-- Indicator of being strictly below the closed stopping threshold. -/
def prophetBelowIndicator (threshold x : ℝ≥0) : ℝ :=
  if x < threshold then 1 else 0

theorem measurable_prophetBelowIndicator (threshold : ℝ≥0) :
    Measurable (prophetBelowIndicator threshold) := by
  unfold prophetBelowIndicator
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const

theorem prophetBelowIndicator_nonneg (threshold x : ℝ≥0) :
    0 ≤ prophetBelowIndicator threshold x := by
  by_cases h : x < threshold <;> simp [prophetBelowIndicator, h]

theorem prophetBelowIndicator_le_one (threshold x : ℝ≥0) :
    prophetBelowIndicator threshold x ≤ 1 := by
  by_cases h : x < threshold <;> simp [prophetBelowIndicator, h]

/-- Excess above a threshold.  It is zero at the threshold itself; the base threshold payment
is accounted for separately, so atoms exactly at the threshold are handled correctly. -/
def prophetThresholdSurplus (threshold x : ℝ≥0) : ℝ :=
  max ((x : ℝ) - (threshold : ℝ)) 0

theorem measurable_prophetThresholdSurplus (threshold : ℝ≥0) :
    Measurable (prophetThresholdSurplus threshold) := by
  unfold prophetThresholdSurplus
  exact (measurable_coe_nnreal_real.sub_const _).max measurable_const

theorem prophetThresholdSurplus_nonneg (threshold x : ℝ≥0) :
    0 ≤ prophetThresholdSurplus threshold x := le_max_right _ _

theorem prophetThresholdSurplus_le_cast (threshold x : ℝ≥0) :
    prophetThresholdSurplus threshold x ≤ (x : ℝ) := by
  unfold prophetThresholdSurplus
  rw [max_le_iff]
  exact ⟨sub_le_self _ (by positivity), by positivity⟩

theorem integrable_prophetThresholdSurplus {mu : Distribution} (threshold : ℝ≥0)
    (hfirst : HasFiniteMoment mu 1) :
    Integrable (prophetThresholdSurplus threshold) (mu : Measure ℝ≥0) := by
  have hid : Integrable (fun x : ℝ≥0 ↦ (x : ℝ)) (mu : Measure ℝ≥0) := by
    change Integrable (fun x : ℝ≥0 ↦ (x : ℝ) ^ 1) (mu : Measure ℝ≥0) at hfirst
    simpa only [pow_one] using hfirst
  apply hid.mono
  · exact (measurable_prophetThresholdSurplus threshold).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (prophetThresholdSurplus_nonneg threshold x),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x : ℝ))]
    exact prophetThresholdSurplus_le_cast threshold x

/-- Realized reward of the deterministic first-above-threshold rule. -/
def prophetThresholdReward {m : ℕ} (threshold : ℝ≥0) (x : ProphetPath m) : ℝ :=
  match prophetFirstAbove threshold x with
  | none => 0
  | some i => (x i : ℝ)

theorem prophetThresholdReward_eq_sum {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) :
    prophetThresholdReward threshold x =
      ∑ i : Fin m, if prophetFirstAbove threshold x = some i then (x i : ℝ) else 0 := by
  classical
  cases h : prophetFirstAbove threshold x with
  | none => simp [prophetThresholdReward, h]
  | some t => simp [prophetThresholdReward, h]

theorem measurable_prophetThresholdReward {m : ℕ} (threshold : ℝ≥0) :
    Measurable (prophetThresholdReward threshold : ProphetPath m → ℝ) := by
  rw [show (prophetThresholdReward threshold : ProphetPath m → ℝ) =
      fun x ↦ ∑ i : Fin m,
        if prophetFirstAbove threshold x = some i then (x i : ℝ) else 0 by
    funext x
    exact prophetThresholdReward_eq_sum threshold x]
  apply Finset.measurable_sum Finset.univ
  intro i hi
  have hchoice : Measurable (fun x : ProphetPath m ↦ prophetFirstAbove threshold x) :=
    measurable_prophetFirstAbove.comp (measurable_const.prodMk measurable_id)
  exact ((measurable_pi_apply i).coe_nnreal_real).ite
    (hchoice (measurableSet_singleton (some i))) measurable_const

theorem prophetThresholdReward_nonneg {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) : 0 ≤ prophetThresholdReward threshold x := by
  unfold prophetThresholdReward
  split <;> positivity

theorem prophetThresholdReward_le_sum {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) :
    prophetThresholdReward threshold x ≤ ∑ i, (x i : ℝ) := by
  cases h : prophetFirstAbove threshold x with
  | none =>
      simp only [prophetThresholdReward, h]
      exact Finset.sum_nonneg fun _ _ ↦ by positivity
  | some i =>
      simp only [prophetThresholdReward, h]
      exact Finset.single_le_sum (f := fun j : Fin m ↦ (x j : ℝ))
        (fun _ _ ↦ by positivity) (Finset.mem_univ i)

theorem integrable_prophetThresholdReward {m : ℕ} (threshold : ℝ≥0)
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws) :
    Integrable (prophetThresholdReward threshold)
      (independentValues laws : Measure (ProphetPath m)) := by
  apply (integrable_coordinate_sum laws hfirst).mono_nonneg
    (measurable_prophetThresholdReward threshold).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (prophetThresholdReward_nonneg threshold)
  · exact Filter.Eventually.of_forall (prophetThresholdReward_le_sum threshold)

@[simp]
theorem prophetBelowIndicator_of_lt {threshold x : ℝ≥0} (h : x < threshold) :
    prophetBelowIndicator threshold x = 1 := by
  simp [prophetBelowIndicator, h]

@[simp]
theorem prophetBelowIndicator_of_le {threshold x : ℝ≥0} (h : threshold ≤ x) :
    prophetBelowIndicator threshold x = 0 := by
  simp [prophetBelowIndicator, not_lt_of_ge h]

@[simp]
theorem prophetThresholdSurplus_of_le {threshold x : ℝ≥0} (h : x ≤ threshold) :
    prophetThresholdSurplus threshold x = 0 := by
  unfold prophetThresholdSurplus
  rw [max_eq_right]
  exact sub_nonpos.mpr (by exact_mod_cast h)

theorem prophetThresholdSurplus_of_threshold_le {threshold x : ℝ≥0}
    (h : threshold ≤ x) :
    prophetThresholdSurplus threshold x = (x : ℝ) - (threshold : ℝ) := by
  unfold prophetThresholdSurplus
  rw [max_eq_left]
  exact sub_nonneg.mpr (by exact_mod_cast h)

/-- Product of strict-below indicators before time `i`. -/
def prophetPrefixBelowIndicator {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) (x : ProphetPath m) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin m ↦ j < i), prophetBelowIndicator threshold (x j)

/-- Indicator that every coordinate is strictly below the threshold. -/
def prophetAllBelowIndicator {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) : ℝ :=
  ∏ j : Fin m, prophetBelowIndicator threshold (x j)

theorem measurable_prophetPrefixBelowIndicator {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) : Measurable (prophetPrefixBelowIndicator threshold i) := by
  unfold prophetPrefixBelowIndicator
  apply Finset.measurable_prod
  intro j hj
  exact (measurable_prophetBelowIndicator threshold).comp (measurable_pi_apply j)

theorem measurable_prophetAllBelowIndicator {m : ℕ} (threshold : ℝ≥0) :
    Measurable (prophetAllBelowIndicator threshold : ProphetPath m → ℝ) := by
  unfold prophetAllBelowIndicator
  apply Finset.measurable_prod
  intro j hj
  exact (measurable_prophetBelowIndicator threshold).comp (measurable_pi_apply j)

theorem prophetPrefixBelowIndicator_nonneg {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) (x : ProphetPath m) :
    0 ≤ prophetPrefixBelowIndicator threshold i x := by
  exact Finset.prod_nonneg fun j hj ↦ prophetBelowIndicator_nonneg threshold (x j)

theorem prophetPrefixBelowIndicator_le_one {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) (x : ProphetPath m) :
    prophetPrefixBelowIndicator threshold i x ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    exact prophetBelowIndicator_nonneg threshold (x j)
  · intro j hj
    exact prophetBelowIndicator_le_one threshold (x j)

theorem prophetAllBelowIndicator_nonneg {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) : 0 ≤ prophetAllBelowIndicator threshold x := by
  exact Finset.prod_nonneg fun j hj ↦ prophetBelowIndicator_nonneg threshold (x j)

theorem prophetAllBelowIndicator_le_one {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) : prophetAllBelowIndicator threshold x ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    exact prophetBelowIndicator_nonneg threshold (x j)
  · intro j hj
    exact prophetBelowIndicator_le_one threshold (x j)

/-- Exact pathwise decomposition into a threshold payment and the surplus at the first hit. -/
theorem prophetThresholdReward_decomposition {m : ℕ} (threshold : ℝ≥0)
    (x : ProphetPath m) :
    prophetThresholdReward threshold x =
      (threshold : ℝ) * (1 - prophetAllBelowIndicator threshold x) +
        ∑ i : Fin m, prophetPrefixBelowIndicator threshold i x *
          prophetThresholdSurplus threshold (x i) := by
  classical
  cases hfirst : prophetFirstAbove threshold x with
  | none =>
      have hall : ∀ i : Fin m, x i < threshold :=
        (prophetFirstAbove_eq_none_iff threshold x).1 hfirst
      have hallprod : prophetAllBelowIndicator threshold x = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        exact prophetBelowIndicator_of_lt (hall i)
      have hsum : (∑ i : Fin m, prophetPrefixBelowIndicator threshold i x *
          prophetThresholdSurplus threshold (x i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [prophetThresholdSurplus_of_le (le_of_lt (hall i)), mul_zero]
      simp [prophetThresholdReward, hfirst, hallprod, hsum]
  | some t =>
      have hcharacter := (prophetFirstAbove_eq_some_iff threshold x t).1 hfirst
      have htt : threshold ≤ x t := hcharacter.1
      have hprev : ∀ i : Fin m, i < t → x i < threshold := hcharacter.2
      have hallprod : prophetAllBelowIndicator threshold x = 0 := by
        unfold prophetAllBelowIndicator
        apply Finset.prod_eq_zero (Finset.mem_univ t)
        exact prophetBelowIndicator_of_le htt
      have hprefix_t : prophetPrefixBelowIndicator threshold t x = 1 := by
        unfold prophetPrefixBelowIndicator
        apply Finset.prod_eq_one
        intro i hi
        exact prophetBelowIndicator_of_lt (hprev i (Finset.mem_filter.1 hi).2)
      have hother : ∀ i : Fin m, i ≠ t →
          prophetPrefixBelowIndicator threshold i x *
            prophetThresholdSurplus threshold (x i) = 0 := by
        intro i hit
        rcases lt_or_gt_of_ne hit with hit' | hti
        · rw [prophetThresholdSurplus_of_le (le_of_lt (hprev i hit')), mul_zero]
        · have hprefix_zero : prophetPrefixBelowIndicator threshold i x = 0 := by
            unfold prophetPrefixBelowIndicator
            apply Finset.prod_eq_zero (i := t)
            · simp [hti]
            · exact prophetBelowIndicator_of_le htt
          rw [hprefix_zero, zero_mul]
      have hsum : (∑ i : Fin m, prophetPrefixBelowIndicator threshold i x *
          prophetThresholdSurplus threshold (x i)) =
          prophetPrefixBelowIndicator threshold t x *
            prophetThresholdSurplus threshold (x t) := by
        apply Finset.sum_eq_single t
        · intro i hi hit
          exact hother i hit
        · simp
      rw [prophetThresholdReward, hfirst, hallprod, hsum, hprefix_t,
        one_mul, prophetThresholdSurplus_of_threshold_le htt]
      ring

theorem integrable_prophetPrefixBelowIndicator {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) (mu : Measure (ProphetPath m)) [IsFiniteMeasure mu] :
    Integrable (prophetPrefixBelowIndicator threshold i) mu := by
  apply Integrable.of_bound
    (measurable_prophetPrefixBelowIndicator threshold i).aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (prophetPrefixBelowIndicator_nonneg threshold i x)]
  exact prophetPrefixBelowIndicator_le_one threshold i x

theorem integrable_prophetAllBelowIndicator {m : ℕ} (threshold : ℝ≥0)
    (mu : Measure (ProphetPath m)) [IsFiniteMeasure mu] :
    Integrable (prophetAllBelowIndicator threshold) mu := by
  apply Integrable.of_bound
    (measurable_prophetAllBelowIndicator threshold).aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (prophetAllBelowIndicator_nonneg threshold x)]
  exact prophetAllBelowIndicator_le_one threshold x

theorem integrable_coordinate_prophetThresholdSurplus {m : ℕ}
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws)
    (threshold : ℝ≥0) (i : Fin m) :
    Integrable (fun x : ProphetPath m ↦ prophetThresholdSurplus threshold (x i))
      (independentValues laws : Measure _) := by
  exact (MeasureTheory.measurePreserving_eval
    (fun i ↦ (laws i : Measure ℝ≥0)) i).integrable_comp_of_integrable
      (integrable_prophetThresholdSurplus threshold (hfirst i))

theorem integrable_prefix_mul_surplus {m : ℕ}
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws)
    (threshold : ℝ≥0) (i : Fin m) :
    Integrable (fun x : ProphetPath m ↦
      prophetPrefixBelowIndicator threshold i x *
        prophetThresholdSurplus threshold (x i))
      (independentValues laws : Measure _) := by
  apply (integrable_coordinate_prophetThresholdSurplus laws hfirst threshold i).mono
  · exact ((measurable_prophetPrefixBelowIndicator threshold i).mul
      ((measurable_prophetThresholdSurplus threshold).comp
        (measurable_pi_apply i))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (prophetPrefixBelowIndicator_nonneg threshold i x),
      abs_of_nonneg (prophetThresholdSurplus_nonneg threshold (x i)),
      Real.norm_eq_abs,
      abs_of_nonneg (prophetThresholdSurplus_nonneg threshold (x i))]
    exact mul_le_of_le_one_left (prophetThresholdSurplus_nonneg threshold (x i))
      (prophetPrefixBelowIndicator_le_one threshold i x)

/-- The all-below indicator is pointwise at most every prefix-below indicator. -/
theorem prophetAllBelowIndicator_le_prefix {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) (x : ProphetPath m) :
    prophetAllBelowIndicator threshold x ≤ prophetPrefixBelowIndicator threshold i x := by
  unfold prophetAllBelowIndicator prophetPrefixBelowIndicator
  apply Finset.prod_le_prod_of_subset_of_le_one (Finset.filter_subset _ _)
  · intro j hj
    exact prophetBelowIndicator_nonneg threshold (x j)
  · intro j hj hjnot
    exact prophetBelowIndicator_le_one threshold (x j)

theorem integral_allBelow_le_prefix {m : ℕ} (threshold : ℝ≥0)
    (i : Fin m) (mu : Measure (ProphetPath m)) [IsFiniteMeasure mu] :
    (∫ x, prophetAllBelowIndicator threshold x ∂mu) ≤
      ∫ x, prophetPrefixBelowIndicator threshold i x ∂mu := by
  exact integral_mono
    (integrable_prophetAllBelowIndicator threshold mu)
    (integrable_prophetPrefixBelowIndicator threshold i mu)
    (prophetAllBelowIndicator_le_prefix threshold i)

theorem integral_prophetAllBelow_nonneg {m : ℕ} (threshold : ℝ≥0)
    (mu : Measure (ProphetPath m)) :
    0 ≤ ∫ x, prophetAllBelowIndicator threshold x ∂mu :=
  integral_nonneg fun x ↦ prophetAllBelowIndicator_nonneg threshold x

theorem integral_prophetAllBelow_le_one {m : ℕ} (threshold : ℝ≥0)
    (mu : Measure (ProphetPath m)) [IsProbabilityMeasure mu] :
    (∫ x, prophetAllBelowIndicator threshold x ∂mu) ≤ 1 := by
  calc
    (∫ x, prophetAllBelowIndicator threshold x ∂mu) ≤
        ∫ _x : ProphetPath m, (1 : ℝ) ∂mu := by
      exact integral_mono
        (integrable_prophetAllBelowIndicator threshold mu)
        (integrable_const 1) (prophetAllBelowIndicator_le_one threshold)
    _ = 1 := by simp

/-- Independence factors the expected first-hit surplus into prefix survival probability and
the one-coordinate surplus expectation. -/
theorem integral_prefix_mul_surplus_eq_mul {m : ℕ}
    (laws : Fin m → Distribution) (threshold : ℝ≥0) (i : Fin m) :
    (∫ x : ProphetPath m, prophetPrefixBelowIndicator threshold i x *
        prophetThresholdSurplus threshold (x i)
      ∂(independentValues laws : Measure _)) =
      (∫ x : ProphetPath m, prophetPrefixBelowIndicator threshold i x
        ∂(independentValues laws : Measure _)) *
      ∫ x : ProphetPath m, prophetThresholdSurplus threshold (x i)
        ∂(independentValues laws : Measure _) := by
  classical
  let transform : Fin m → ℝ≥0 → ℝ := fun j y ↦
    if j = i then prophetThresholdSurplus threshold y else prophetBelowIndicator threshold y
  have htransform_meas : ∀ j, Measurable (transform j) := by
    intro j
    by_cases hji : j = i
    · simpa [transform, hji] using measurable_prophetThresholdSurplus threshold
    · simpa [transform, hji] using measurable_prophetBelowIndicator threshold
  have hind : iIndepFun
      (fun j ↦ transform j ∘ fun x : ProphetPath m ↦ x j)
      (independentValues laws : Measure _) :=
    (independentValues_iIndep laws).comp transform htransform_meas
  let s : Finset (Fin m) := Finset.univ.filter fun j ↦ j < i
  have hi : i ∉ s := by simp [s]
  have hfamily_meas : ∀ j, Measurable
      ((transform j) ∘ fun x : ProphetPath m ↦ x j) := by
    intro j
    exact (htransform_meas j).comp (measurable_pi_apply j)
  have hIndep := hind.indepFun_finsetProd_of_notMem hfamily_meas hi
  have hleft :
      (∏ j ∈ s, (transform j) ∘ fun x : ProphetPath m ↦ x j) =
        prophetPrefixBelowIndicator threshold i := by
    funext x
    unfold prophetPrefixBelowIndicator s
    simp only [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := ne_of_lt (Finset.mem_filter.1 hj).2
    simp [transform, hji]
  have hright :
      (transform i) ∘ (fun x : ProphetPath m ↦ x i) =
        fun x ↦ prophetThresholdSurplus threshold (x i) := by
    funext x
    simp [transform]
  rw [hleft, hright] at hIndep
  exact hIndep.integral_fun_mul_eq_mul_integral
    (measurable_prophetPrefixBelowIndicator threshold i).aestronglyMeasurable
    (((measurable_prophetThresholdSurplus threshold).comp
      (measurable_pi_apply i)).aestronglyMeasurable)

/-- Expected reward of a deterministic first-above-threshold rule. -/
def prophetThresholdExpectedReward {m : ℕ} (threshold : ℝ≥0)
    (laws : Fin m → Distribution) : ℝ :=
  ∫ x : ProphetPath m, prophetThresholdReward threshold x
    ∂(independentValues laws : Measure (ProphetPath m))

theorem prophetThresholdExpectedReward_decomposition {m : ℕ}
    (threshold : ℝ≥0) (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws) :
    prophetThresholdExpectedReward threshold laws =
      (threshold : ℝ) *
          (1 - ∫ x : ProphetPath m, prophetAllBelowIndicator threshold x
            ∂(independentValues laws : Measure (ProphetPath m))) +
        ∑ i : Fin m,
          (∫ x : ProphetPath m, prophetPrefixBelowIndicator threshold i x
            ∂(independentValues laws : Measure (ProphetPath m))) *
          ∫ x : ProphetPath m, prophetThresholdSurplus threshold (x i)
            ∂(independentValues laws : Measure (ProphetPath m)) := by
  let mu : Measure (ProphetPath m) := independentValues laws
  have hall : Integrable (prophetAllBelowIndicator threshold) mu :=
    integrable_prophetAllBelowIndicator threshold mu
  have hbase : Integrable
      (fun x : ProphetPath m ↦ (threshold : ℝ) *
        (1 - prophetAllBelowIndicator threshold x)) mu :=
    (integrable_const 1 |>.sub hall).const_mul _
  have hterm : ∀ i : Fin m, Integrable
      (fun x : ProphetPath m ↦ prophetPrefixBelowIndicator threshold i x *
        prophetThresholdSurplus threshold (x i)) mu :=
    fun i ↦ integrable_prefix_mul_surplus laws hfirst threshold i
  calc
    prophetThresholdExpectedReward threshold laws =
        ∫ x, ((threshold : ℝ) * (1 - prophetAllBelowIndicator threshold x) +
          ∑ i : Fin m, prophetPrefixBelowIndicator threshold i x *
            prophetThresholdSurplus threshold (x i)) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ prophetThresholdReward_decomposition threshold x
    _ = (∫ x, (threshold : ℝ) * (1 - prophetAllBelowIndicator threshold x) ∂mu) +
        ∑ i : Fin m, ∫ x, prophetPrefixBelowIndicator threshold i x *
          prophetThresholdSurplus threshold (x i) ∂mu := by
      rw [integral_add hbase (integrable_finset_sum _ fun i _ ↦ hterm i),
        integral_finset_sum Finset.univ (fun i _ ↦ hterm i)]
    _ = (threshold : ℝ) *
          (1 - ∫ x, prophetAllBelowIndicator threshold x ∂mu) +
        ∑ i : Fin m,
          (∫ x, prophetPrefixBelowIndicator threshold i x ∂mu) *
          ∫ x, prophetThresholdSurplus threshold (x i) ∂mu := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hall]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_prefix_mul_surplus_eq_mul laws threshold i

/-- The maximum is bounded pointwise by one threshold payment plus all coordinate surpluses. -/
theorem firstOrderStatistic_le_threshold_add_surplus {m : ℕ} (hm : 1 ≤ m)
    (threshold : ℝ≥0) (x : ProphetPath m) :
    (descendingOrderStatistic (prophetFirstRank m hm) x : ℝ) ≤
      (threshold : ℝ) + ∑ i : Fin m, prophetThresholdSurplus threshold (x i) := by
  obtain ⟨s, hs, hmax⟩ := Finset.exists_mem_eq_sup'
    (rankSubsets_nonempty (prophetFirstRank m hm)) (subsetMinimum x)
  have hcard : s.card = 1 := by
    simpa [rankSubsets, prophetFirstRank] using (Finset.mem_powersetCard.1 hs).2
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  have hsurplus : prophetThresholdSurplus threshold (x i) ≤
      ∑ j : Fin m, prophetThresholdSurplus threshold (x j) :=
    Finset.single_le_sum
      (fun j hj ↦ prophetThresholdSurplus_nonneg threshold (x j)) (Finset.mem_univ i)
  have hcoordinate : (x i : ℝ) ≤
      (threshold : ℝ) + prophetThresholdSurplus threshold (x i) := by
    unfold prophetThresholdSurplus
    have hmaxle : (x i : ℝ) - (threshold : ℝ) ≤
        max ((x i : ℝ) - (threshold : ℝ)) 0 := le_max_left _ _
    linarith
  rw [descendingOrderStatistic, hmax]
  simp only [subsetMinimum, Finset.singleton_nonempty, dite_true, Finset.inf'_singleton]
  linarith

/-- `lem:baseline` plus the positive-part inequality in the threshold proof. -/
theorem orderStatisticBenchmark_le_threshold_add_surplus {m : ℕ} (hm : 1 ≤ m)
    (threshold : ℝ≥0) (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws) :
    orderStatisticBenchmark (prophetFirstRank m hm) laws ≤
      (threshold : ℝ) + ∑ i : Fin m,
        ∫ x : ProphetPath m, prophetThresholdSurplus threshold (x i)
          ∂(independentValues laws : Measure _) := by
  let mu : Measure (ProphetPath m) := independentValues laws
  have hM : Integrable
      (fun x : ProphetPath m ↦
        (descendingOrderStatistic (prophetFirstRank m hm) x : ℝ)) mu :=
    integrable_descendingOrderStatistic (prophetFirstRank m hm) laws hfirst
  have hsurplus : ∀ i : Fin m, Integrable
      (fun x : ProphetPath m ↦ prophetThresholdSurplus threshold (x i)) mu :=
    fun i ↦ integrable_coordinate_prophetThresholdSurplus laws hfirst threshold i
  have hrhs : Integrable
      (fun x : ProphetPath m ↦ (threshold : ℝ) +
        ∑ i : Fin m, prophetThresholdSurplus threshold (x i)) mu :=
    (integrable_const (threshold : ℝ)).add
      (integrable_finset_sum _ fun i _ ↦ hsurplus i)
  have hmono := integral_mono hM hrhs
    (firstOrderStatistic_le_threshold_add_surplus hm threshold)
  unfold orderStatisticBenchmark
  calc
    (∫ x, (descendingOrderStatistic (prophetFirstRank m hm) x : ℝ) ∂mu) ≤
        ∫ x, ((threshold : ℝ) +
          ∑ i : Fin m, prophetThresholdSurplus threshold (x i)) ∂mu := hmono
    _ = (threshold : ℝ) + ∑ i : Fin m,
        ∫ x, prophetThresholdSurplus threshold (x i) ∂mu := by
      rw [integral_add (integrable_const _) (integrable_finset_sum _ fun i _ ↦ hsurplus i),
        integral_finset_sum Finset.univ (fun i _ ↦ hsurplus i)]
      simp

/-- `thm:random-bucket-threshold`, fixed-threshold core: whenever the threshold lies between
one quarter and one half of the expected maximum, first-above-threshold earns at least one
quarter of that benchmark. -/
theorem prophetThresholdExpectedReward_quarter {m : ℕ} (hm : 1 ≤ m)
    (threshold : ℝ≥0) (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws)
    (hlower : 2 * (threshold : ℝ) ≤
      orderStatisticBenchmark (prophetFirstRank m hm) laws)
    (hupper : orderStatisticBenchmark (prophetFirstRank m hm) laws ≤
      4 * (threshold : ℝ)) :
    orderStatisticBenchmark (prophetFirstRank m hm) laws / 4 ≤
      prophetThresholdExpectedReward threshold laws := by
  let mu : Measure (ProphetPath m) := independentValues laws
  let q : ℝ := ∫ x, prophetAllBelowIndicator threshold x ∂mu
  let qi : Fin m → ℝ := fun i ↦
    ∫ x, prophetPrefixBelowIndicator threshold i x ∂mu
  let surplus : Fin m → ℝ := fun i ↦
    ∫ x, prophetThresholdSurplus threshold (x i) ∂mu
  let V : ℝ := orderStatisticBenchmark (prophetFirstRank m hm) laws
  have hq0 : 0 ≤ q := integral_prophetAllBelow_nonneg threshold mu
  have hsurplus0 : ∀ i, 0 ≤ surplus i := by
    intro i
    exact integral_nonneg fun x ↦ prophetThresholdSurplus_nonneg threshold (x i)
  have hq_le_qi : ∀ i, q ≤ qi i := by
    intro i
    exact integral_allBelow_le_prefix threshold i mu
  have hsum : q * ∑ i, surplus i ≤ ∑ i, qi i * surplus i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_right (hq_le_qi i) (hsurplus0 i)
  have hbenchmark : V - (threshold : ℝ) ≤ ∑ i, surplus i := by
    have h := orderStatisticBenchmark_le_threshold_add_surplus hm threshold laws hfirst
    change V ≤ (threshold : ℝ) + ∑ i, surplus i at h
    linarith
  have hqbenchmark : q * (V - (threshold : ℝ)) ≤ q * ∑ i, surplus i :=
    mul_le_mul_of_nonneg_left hbenchmark hq0
  have hquarter : V / 4 ≤ (threshold : ℝ) := by
    change V ≤ 4 * (threshold : ℝ) at hupper
    linarith
  have hthreshold : (threshold : ℝ) ≤
      (threshold : ℝ) * (1 - q) + q * (V - (threshold : ℝ)) := by
    have hgap : 0 ≤ V - 2 * (threshold : ℝ) := by
      change 2 * (threshold : ℝ) ≤ V at hlower
      linarith
    have hnonneg := mul_nonneg hq0 hgap
    nlinarith
  calc
    V / 4 ≤ (threshold : ℝ) := hquarter
    _ ≤ (threshold : ℝ) * (1 - q) + q * (V - (threshold : ℝ)) := hthreshold
    _ ≤ (threshold : ℝ) * (1 - q) + q * ∑ i, surplus i := by
      linarith
    _ ≤ (threshold : ℝ) * (1 - q) + ∑ i, qi i * surplus i := by
      linarith
    _ = prophetThresholdExpectedReward threshold laws := by
      rw [prophetThresholdExpectedReward_decomposition threshold laws hfirst]

/-! ## The STOC baseline and a good dyadic bucket -/

theorem moment_one_eq_integral (mu : Distribution) :
    moment mu 1 = ∫ x : ℝ≥0, (x : ℝ) ∂(mu : Measure ℝ≥0) := by
  simp [moment, momentIntegrand]

theorem moment_one_nonneg (mu : Distribution) : 0 ≤ moment mu 1 := by
  rw [moment_one_eq_integral]
  exact integral_nonneg fun x ↦ by positivity

theorem integral_coordinate_eq_moment_one {m : ℕ} (laws : Fin m → Distribution)
    (i : Fin m) :
    (∫ x : ProphetPath m, (x i : ℝ) ∂(independentValues laws : Measure _)) =
      moment (laws i) 1 := by
  rw [moment_one_eq_integral, independentValues, ProbabilityMeasure.toMeasure_pi]
  exact MeasureTheory.integral_comp_eval
    (measurable_coe_nnreal_real.aestronglyMeasurable)

theorem moment_one_le_profileMax {m : ℕ} (laws : Fin m → Distribution) (i : Fin m) :
    moment (laws i) 1 ≤ (profileMaxFirstMoment (disclosedProfile laws) : ℝ) := by
  have hle : Real.toNNReal (moment (laws i) 1) ≤
      profileMaxFirstMoment (disclosedProfile laws) := by
    unfold profileMaxFirstMoment disclosedProfile momentSequence
    exact Finset.le_sup (s := Finset.univ) (f := fun i ↦ Real.toNNReal (moment (laws i) 1))
      (Finset.mem_univ i)
  calc
    moment (laws i) 1 = (Real.toNNReal (moment (laws i) 1) : ℝ) := by
      simp [moment_one_nonneg]
    _ ≤ (profileMaxFirstMoment (disclosedProfile laws) : ℝ) := by exact_mod_cast hle

theorem exists_moment_one_eq_profileMax {m : ℕ} (hm : 1 ≤ m)
    (laws : Fin m → Distribution) :
    ∃ i : Fin m,
      moment (laws i) 1 = (profileMaxFirstMoment (disclosedProfile laws) : ℝ) := by
  let i0 : Fin m := ⟨0, hm⟩
  letI : Nonempty (Fin m) := ⟨i0⟩
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup Finset.univ huniv
    (fun i ↦ Real.toNNReal (moment (laws i) 1))
  refine ⟨i, ?_⟩
  unfold profileMaxFirstMoment disclosedProfile momentSequence
  rw [hsup]
  simp [moment_one_nonneg]

theorem coordinate_le_firstOrderStatistic {m : ℕ} (hm : 1 ≤ m)
    (x : ProphetPath m) (i : Fin m) :
    x i ≤ descendingOrderStatistic (prophetFirstRank m hm) x := by
  have hsingleton : ({i} : Finset (Fin m)) ∈ rankSubsets (prophetFirstRank m hm) := by
    simp [rankSubsets, prophetFirstRank]
  calc
    x i = subsetMinimum x {i} := by simp [subsetMinimum]
    _ ≤ (rankSubsets (prophetFirstRank m hm)).sup'
        (rankSubsets_nonempty (prophetFirstRank m hm)) (subsetMinimum x) :=
      Finset.le_sup' _ hsingleton

/-- `lem:baseline`: first moments locate the expected maximum within a factor `m`. -/
theorem prophet_baseline {m : ℕ} (hm : 1 ≤ m) (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws) :
    (profileMaxFirstMoment (disclosedProfile laws) : ℝ) ≤
        orderStatisticBenchmark (prophetFirstRank m hm) laws ∧
      orderStatisticBenchmark (prophetFirstRank m hm) laws ≤
        (m : ℝ) * (profileMaxFirstMoment (disclosedProfile laws) : ℝ) := by
  let mu : Measure (ProphetPath m) := independentValues laws
  have hmaxInt : Integrable
      (fun x : ProphetPath m ↦
        (descendingOrderStatistic (prophetFirstRank m hm) x : ℝ)) mu :=
    integrable_descendingOrderStatistic (prophetFirstRank m hm) laws hfirst
  constructor
  · obtain ⟨i, hi⟩ := exists_moment_one_eq_profileMax hm laws
    rw [← hi, ← integral_coordinate_eq_moment_one laws i]
    unfold orderStatisticBenchmark
    exact integral_mono
      (integrable_coordinate_cast laws hfirst i) hmaxInt
      (fun x ↦ by exact_mod_cast coordinate_le_firstOrderStatistic hm x i)
  · unfold orderStatisticBenchmark
    have hpoint : ∀ x : ProphetPath m,
        (descendingOrderStatistic (prophetFirstRank m hm) x : ℝ) ≤
          ∑ i : Fin m, (x i : ℝ) := by
      intro x
      exact_mod_cast (descendingOrderStatistic_le_sum
        (r := prophetFirstRank m hm) x)
    calc
      (∫ x, (descendingOrderStatistic (prophetFirstRank m hm) x : ℝ) ∂mu) ≤
          ∫ x, ∑ i : Fin m, (x i : ℝ) ∂mu := by
        exact integral_mono hmaxInt (integrable_coordinate_sum laws hfirst)
          hpoint
      _ = ∑ i : Fin m, moment (laws i) 1 := by
        rw [integral_finset_sum Finset.univ (fun i _ ↦
          integrable_coordinate_cast laws hfirst i)]
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_coordinate_eq_moment_one laws i
      _ ≤ ∑ _i : Fin m,
          (profileMaxFirstMoment (disclosedProfile laws) : ℝ) :=
        Finset.sum_le_sum fun i hi ↦ moment_one_le_profileMax laws i
      _ = (m : ℝ) * (profileMaxFirstMoment (disclosedProfile laws) : ℝ) := by
        simp [mul_comm]

theorem horizon_le_two_pow_bucketCount {m : ℕ} (hm : 2 ≤ m) :
    m ≤ 2 ^ prophetBucketCount m := by
  have hpow := Nat.lt_pow_succ_log_self (b := 2) (by omega) (m - 1)
  unfold prophetBucketCount
  omega

/-- Finite dyadic bracketing, with weak inequalities so boundary values belong to either
adjacent bucket. -/
theorem exists_dyadic_bracket {K : ℕ} (hK : 1 ≤ K) {mu V : ℝ}
    (_hmu0 : 0 ≤ mu) (hmuV : mu ≤ V) (hVK : V ≤ (2 : ℝ) ^ K * mu) :
    ∃ j : Fin K, (2 : ℝ) ^ j.1 * mu ≤ V ∧
      V ≤ (2 : ℝ) ^ (j.1 + 1) * mu := by
  induction K with
  | zero => omega
  | succ K ih =>
      by_cases hKzero : K = 0
      · subst K
        refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · simpa using hmuV
        · simpa using hVK
      · by_cases hsmall : V ≤ (2 : ℝ) ^ K * mu
        · obtain ⟨j, hjlow, hjhigh⟩ := ih (Nat.one_le_iff_ne_zero.2 hKzero) hsmall
          refine ⟨⟨j.1, by omega⟩, hjlow, hjhigh⟩
        · refine ⟨⟨K, by omega⟩, le_of_not_ge hsmall, ?_⟩
          simpa [Nat.succ_eq_add_one] using hVK

/-! ## Averaging the bucket thresholds -/

/-- On a fixed path, integrating the bucket policy's action is exactly averaging the
deterministic threshold rewards. -/
theorem prophetBucketKernel_reward_eq_average {m : ℕ}
    (profile : MomentProfile m) (x : ProphetPath m) :
    (∫ choice, (match choice with | none => 0 | some i => (x i : ℝ))
        ∂(prophetBucketPolicy m).kernel (profile, x)) =
      ((prophetBucketCount m : ℝ)⁻¹) *
        ∑ j : Fin (prophetBucketCount m),
          prophetThresholdReward (prophetBucketThreshold profile j.1) x := by
  rw [show (prophetBucketPolicy m).kernel = prophetBucketKernel m by rfl,
    prophetBucketKernel_apply]
  let reward : Option (Fin m) → ℝ := fun choice ↦
    match choice with | none => 0 | some i => (x i : ℝ)
  have hdecision : Measurable
      (fun j : Fin (prophetBucketCount m) ↦
        prophetBucketDecision ((profile, x), j)) :=
    measurable_prophetBucketDecision.comp (measurable_const.prodMk measurable_id)
  have hreward : Measurable reward := measurable_of_finite _
  rw [integral_map hdecision.aemeasurable hreward.aestronglyMeasurable,
    prophetBucketSeedLaw_integral_eq_average]
  congr 1

/-- Taking expectation over the independent values commutes with the finite uniform bucket
average. -/
theorem prophetBucketExpectedReward_eq_average {m : ℕ}
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws) :
    prophetExpectedReward (prophetBucketPolicy m) laws =
      ((prophetBucketCount m : ℝ)⁻¹) *
        ∑ j : Fin (prophetBucketCount m),
          prophetThresholdExpectedReward
            (prophetBucketThreshold (disclosedProfile laws) j.1) laws := by
  rw [prophetExpectedReward]
  have hterm : ∀ j : Fin (prophetBucketCount m), Integrable
      (prophetThresholdReward
        (prophetBucketThreshold (disclosedProfile laws) j.1))
      (independentValues laws : Measure (ProphetPath m)) :=
    fun j ↦ integrable_prophetThresholdReward
      (prophetBucketThreshold (disclosedProfile laws) j.1) laws hfirst
  calc
    (∫ x : ProphetPath m, ∫ choice,
        (match choice with | none => 0 | some i => (x i : ℝ))
          ∂(prophetBucketPolicy m).kernel (disclosedProfile laws, x)
        ∂(independentValues laws : Measure (ProphetPath m))) =
        ∫ x : ProphetPath m, ((prophetBucketCount m : ℝ)⁻¹) *
          ∑ j : Fin (prophetBucketCount m),
            prophetThresholdReward
              (prophetBucketThreshold (disclosedProfile laws) j.1) x
          ∂(independentValues laws : Measure (ProphetPath m)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        prophetBucketKernel_reward_eq_average (disclosedProfile laws) x
    _ = ((prophetBucketCount m : ℝ)⁻¹) *
        ∫ x : ProphetPath m, ∑ j : Fin (prophetBucketCount m),
          prophetThresholdReward
            (prophetBucketThreshold (disclosedProfile laws) j.1) x
          ∂(independentValues laws : Measure (ProphetPath m)) := by
      rw [integral_const_mul]
    _ = ((prophetBucketCount m : ℝ)⁻¹) *
        ∑ j : Fin (prophetBucketCount m),
          ∫ x : ProphetPath m, prophetThresholdReward
            (prophetBucketThreshold (disclosedProfile laws) j.1) x
            ∂(independentValues laws : Measure (ProphetPath m)) := by
      rw [integral_finset_sum Finset.univ (fun j _ ↦ hterm j)]
    _ = ((prophetBucketCount m : ℝ)⁻¹) *
        ∑ j : Fin (prophetBucketCount m),
          prophetThresholdExpectedReward
            (prophetBucketThreshold (disclosedProfile laws) j.1) laws := by
      simp only [prophetThresholdExpectedReward]

@[simp]
theorem coe_prophetBucketThreshold {m : ℕ} (profile : MomentProfile m) (j : ℕ) :
    (prophetBucketThreshold profile j : ℝ) =
      (2 : ℝ) ^ j * (profileMaxFirstMoment profile : ℝ) / 2 := by
  simp [prophetBucketThreshold]

/-- The baseline places the expected maximum in one of the sampled dyadic buckets.  The weak
endpoints cover atoms and also make the zero-benchmark case literal rather than exceptional. -/
theorem exists_good_prophetBucket {m : ℕ} (hm : 2 ≤ m)
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws) :
    ∃ j : Fin (prophetBucketCount m),
      2 * (prophetBucketThreshold (disclosedProfile laws) j.1 : ℝ) ≤
          orderStatisticBenchmark (prophetFirstRank m (by omega)) laws ∧
        orderStatisticBenchmark (prophetFirstRank m (by omega)) laws ≤
          4 * (prophetBucketThreshold (disclosedProfile laws) j.1 : ℝ) := by
  let mu : ℝ := (profileMaxFirstMoment (disclosedProfile laws) : ℝ)
  let V : ℝ := orderStatisticBenchmark (prophetFirstRank m (by omega)) laws
  have hbase := prophet_baseline (m := m) (by omega) laws hfirst
  have hmuV : mu ≤ V := hbase.1
  have hVm : V ≤ (m : ℝ) * mu := hbase.2
  have hmpow_nat : m ≤ 2 ^ prophetBucketCount m := horizon_le_two_pow_bucketCount hm
  have hmpow_real : (m : ℝ) ≤ (2 : ℝ) ^ prophetBucketCount m := by
    exact_mod_cast hmpow_nat
  have hVpow : V ≤ (2 : ℝ) ^ prophetBucketCount m * mu := by
    exact hVm.trans (mul_le_mul_of_nonneg_right hmpow_real (by positivity))
  obtain ⟨j, hjlow, hjhigh⟩ := exists_dyadic_bracket
    (prophetBucketCount_pos m) (show 0 ≤ mu by positivity) hmuV hVpow
  refine ⟨j, ?_, ?_⟩
  · change 2 * ((2 : ℝ) ^ j.1 * mu / 2) ≤ V
    convert hjlow using 1 <;> ring
  · change V ≤ 4 * ((2 : ℝ) ^ j.1 * mu / 2)
    calc
      V ≤ (2 : ℝ) ^ (j.1 + 1) * mu := hjhigh
      _ = 4 * ((2 : ℝ) ^ j.1 * mu / 2) := by
        rw [pow_succ]
        ring

theorem prophetThresholdExpectedReward_nonneg {m : ℕ} (threshold : ℝ≥0)
    (laws : Fin m → Distribution) :
    0 ≤ prophetThresholdExpectedReward threshold laws := by
  exact integral_nonneg (prophetThresholdReward_nonneg threshold)

/-- Universal factor delivered by uniform exponential bucketing. -/
def prophetBucketAlpha (m : ℕ) : ℝ :=
  1 / (4 * (prophetBucketCount m : ℝ))

theorem prophetBucketAlpha_pos (m : ℕ) : 0 < prophetBucketAlpha m := by
  unfold prophetBucketAlpha
  have hK : (0 : ℝ) < prophetBucketCount m := by
    exact_mod_cast prophetBucketCount_pos m
  exact one_div_pos.mpr (mul_pos (by norm_num) hK)

/-- `thm:random-bucket-threshold`: the bucket policy earns the explicit universal factor
`1 / (4 ceil(log_2 m))` against the expected maximum. -/
theorem prophetBucket_expectedReward_lower {m : ℕ} (hm : 2 ≤ m)
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws) :
    prophetBucketAlpha m *
        orderStatisticBenchmark (prophetFirstRank m (by omega)) laws ≤
      prophetExpectedReward (prophetBucketPolicy m) laws := by
  let V : ℝ := orderStatisticBenchmark (prophetFirstRank m (by omega)) laws
  let K : ℝ := prophetBucketCount m
  obtain ⟨j, hjlow, hjhigh⟩ := exists_good_prophetBucket hm laws hfirst
  have hjreward : V / 4 ≤
      prophetThresholdExpectedReward
        (prophetBucketThreshold (disclosedProfile laws) j.1) laws := by
    exact prophetThresholdExpectedReward_quarter (m := m) (by omega)
      (prophetBucketThreshold (disclosedProfile laws) j.1) laws hfirst hjlow hjhigh
  have hsum : V / 4 ≤
      ∑ k : Fin (prophetBucketCount m),
        prophetThresholdExpectedReward
          (prophetBucketThreshold (disclosedProfile laws) k.1) laws := by
    exact hjreward.trans (Finset.single_le_sum
      (fun k hk ↦ prophetThresholdExpectedReward_nonneg
        (prophetBucketThreshold (disclosedProfile laws) k.1) laws)
      (Finset.mem_univ j))
  have hK0 : 0 < K := by
    have hK0' : (0 : ℝ) < prophetBucketCount m := by
      exact_mod_cast prophetBucketCount_pos m
    simpa [K] using hK0'
  rw [prophetBucketExpectedReward_eq_average laws hfirst]
  calc
    prophetBucketAlpha m * V = K⁻¹ * (V / 4) := by
      unfold prophetBucketAlpha K
      field_simp
    _ ≤ K⁻¹ * ∑ k : Fin (prophetBucketCount m),
        prophetThresholdExpectedReward
          (prophetBucketThreshold (disclosedProfile laws) k.1) laws :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hK0.le)
    _ = ((prophetBucketCount m : ℝ)⁻¹) *
        ∑ k : Fin (prophetBucketCount m),
          prophetThresholdExpectedReward
            (prophetBucketThreshold (disclosedProfile laws) k.1) laws := by rfl

theorem prophetBucket_universalGuarantee {m : ℕ} (hm : 2 ≤ m) :
    ProphetUniversalGuarantee (prophetFirstRank m (by omega))
      (prophetBucketAlpha m) (prophetBucketPolicy m) := by
  intro laws hfinite
  exact prophetBucket_expectedReward_lower hm laws (fun i ↦ hfinite i 1)

theorem prophetBucketAlpha_mem_feasible {m : ℕ} (hm : 2 ≤ m) :
    prophetBucketAlpha m ∈
      prophetFeasibleSet (prophetFirstRank m (by omega)) := by
  exact ⟨(prophetBucketAlpha_pos m).le, prophetBucketPolicy m,
    prophetBucket_universalGuarantee hm⟩

theorem prophetBucketAlpha_le_rhoMom {m : ℕ} (hm : 2 ≤ m) :
    prophetBucketAlpha m ≤ rhoMom (prophetFirstRank m (by omega)) := by
  apply le_csSup (prophetFeasibleSet_bddAbove (prophetFirstRank m (by omega)))
  exact prophetBucketAlpha_mem_feasible hm

/-! ## Conversion from bucket count to the natural logarithm -/

/-- The exact natural bucket count is at most `2 log(m) / log(2)`. -/
theorem bucketCount_mul_log_two_le {m : ℕ} (hm : 2 ≤ m) :
    (prophetBucketCount m : ℝ) * Real.log 2 ≤ 2 * Real.log m := by
  let n : ℕ := Nat.log 2 (m - 1)
  have hm1ne : m - 1 ≠ 0 := by omega
  have hpownat : 2 ^ n ≤ m - 1 := by
    exact Nat.pow_log_le_self 2 hm1ne
  have hpowreal : (2 : ℝ) ^ n ≤ (m : ℝ) := by
    have hnat : 2 ^ n ≤ m := hpownat.trans (by omega)
    exact_mod_cast hnat
  have hlogpow : Real.log ((2 : ℝ) ^ n) ≤ Real.log (m : ℝ) :=
    (Real.log_le_log_iff (by positivity) (by positivity)).2 hpowreal
  rw [Real.log_pow] at hlogpow
  have htwom : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogtwo : Real.log 2 ≤ Real.log (m : ℝ) :=
    (Real.log_le_log_iff (by norm_num) (by positivity)).2 htwom
  change ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log (m : ℝ)
  push_cast
  nlinarith

/-- The explicit factor `log(2)/(8 log(m))` is no larger than the bucket guarantee. -/
theorem log_factor_le_prophetBucketAlpha {m : ℕ} (hm : 2 ≤ m) :
    (Real.log 2 / 8) / Real.log m ≤ prophetBucketAlpha m := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmreal
  have hK : (0 : ℝ) < prophetBucketCount m := by
    exact_mod_cast prophetBucketCount_pos m
  have hcount := bucketCount_mul_log_two_le hm
  unfold prophetBucketAlpha
  rw [div_le_div_iff₀ hlogm (mul_pos (by norm_num) hK)]
  nlinarith

end

end MomentAmbiguity
