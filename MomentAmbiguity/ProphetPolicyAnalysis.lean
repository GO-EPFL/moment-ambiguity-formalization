import MomentAmbiguity.ProphetDefs

/-!
# Prefix analysis for causal prophet policies

This file proves the measure-theoretic fact used by the block-switch construction: the
probability of stopping at time `t` depends only on the marginal laws through `t`.  The proof
uses the causal-kernel field of `ProphetPolicy`; no independence or stopping-time fact is
assumed through an auxiliary interface.
-/

open scoped ENNReal NNReal BigOperators

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Replace all coordinates strictly after `t` by zero. -/
def truncateProphetPath {m : ℕ} (t : Fin m) (x : ProphetPath m) : ProphetPath m :=
  fun i ↦ if i ≤ t then x i else 0

theorem measurable_truncateProphetPath {m : ℕ} (t : Fin m) :
    Measurable (truncateProphetPath t) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ≤ t
  · simpa [truncateProphetPath, hi] using (measurable_pi_apply i :
      Measurable (fun x : ProphetPath m ↦ x i))
  · simp [truncateProphetPath, hi]

theorem truncateProphetPath_agree {m : ℕ} (t : Fin m) (x : ProphetPath m) :
    AgreeThrough t x (truncateProphetPath t x) := by
  intro i hi
  simp [truncateProphetPath, hi]

/-- Probability that the policy selects exactly coordinate `t`, conditional on a full path.
It is real-valued only to make subsequent expectations ordinary Bochner integrals. -/
def prophetSelectProbability {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) (x : ProphetPath m) : ℝ :=
  (policy.kernel (profile, x) {some t}).toReal

theorem measurable_prophetSelectProbability {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) :
    Measurable (prophetSelectProbability policy profile t) := by
  unfold prophetSelectProbability
  exact (policy.kernel.measurable_coe (measurableSet_singleton (some t))).ennreal_toReal.comp
    (measurable_const.prodMk measurable_id)

theorem prophetSelectProbability_nonneg {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) (x : ProphetPath m) :
    0 ≤ prophetSelectProbability policy profile t x := by
  exact ENNReal.toReal_nonneg

theorem prophetSelectProbability_le_one {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) (x : ProphetPath m) :
    prophetSelectProbability policy profile t x ≤ 1 := by
  unfold prophetSelectProbability
  have hle : policy.kernel (profile, x) {some t} ≤
      policy.kernel (profile, x) Set.univ :=
    measure_mono (Set.subset_univ _)
  have hle_one : policy.kernel (profile, x) {some t} ≤ 1 := by simpa using hle
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle_one

theorem integrable_prophetSelectProbability {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) (μ : Measure (ProphetPath m))
    [IsFiniteMeasure μ] :
    Integrable (prophetSelectProbability policy profile t) μ := by
  apply Integrable.of_bound
    (measurable_prophetSelectProbability policy profile t).aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (prophetSelectProbability_nonneg policy profile t x)]
  exact prophetSelectProbability_le_one policy profile t x

/-- Causality makes the conditional selection probability invariant under tail truncation. -/
theorem prophetSelectProbability_truncate {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) (x : ProphetPath m) :
    prophetSelectProbability policy profile t x =
      prophetSelectProbability policy profile t (truncateProphetPath t x) := by
  unfold prophetSelectProbability
  rw [policy.causal profile x (truncateProphetPath t x) t
    (truncateProphetPath_agree t x)]

/-- Product laws have the same truncated-path distribution when all marginals through `t`
agree. -/
theorem map_truncate_independentValues_eq {m : ℕ} (t : Fin m)
    (laws laws' : Fin m → Distribution)
    (hprefix : ∀ i, i ≤ t → laws i = laws' i) :
    Measure.map (truncateProphetPath t) (independentValues laws : Measure _) =
      Measure.map (truncateProphetPath t) (independentValues laws' : Measure _) := by
  rw [independentValues, independentValues,
    ProbabilityMeasure.toMeasure_pi, ProbabilityMeasure.toMeasure_pi]
  unfold truncateProphetPath
  let f : Fin m → ℝ≥0 → ℝ≥0 := fun i y ↦ if i ≤ t then y else 0
  change Measure.map (fun x i ↦ f i (x i)) (Measure.pi fun i ↦ (laws i : Measure ℝ≥0)) =
    Measure.map (fun x i ↦ f i (x i)) (Measure.pi fun i ↦ (laws' i : Measure ℝ≥0))
  rw [Measure.pi_map_pi (f := f) (fun i ↦ by
      by_cases hi : i ≤ t
      · simp only [f, hi, ↓reduceIte]
        exact (measurable_id : Measurable (id : ℝ≥0 → ℝ≥0)).aemeasurable
      · simpa [f, hi] using
          (measurable_const.aemeasurable :
            AEMeasurable (fun _ : ℝ≥0 ↦ (0 : ℝ≥0)) (laws i : Measure ℝ≥0))),
    Measure.pi_map_pi (f := f) (fun i ↦ by
      by_cases hi : i ≤ t
      · simp only [f, hi, ↓reduceIte]
        exact (measurable_id : Measurable (id : ℝ≥0 → ℝ≥0)).aemeasurable
      · simpa [f, hi] using
          (measurable_const.aemeasurable :
            AEMeasurable (fun _ : ℝ≥0 ↦ (0 : ℝ≥0)) (laws' i : Measure ℝ≥0)))]
  congr 1
  funext i
  by_cases hi : i ≤ t
  · simp [f, hi, hprefix i hi]
  · simp [f, hi, Measure.map_const]

/-- The expected probability of selecting at `t` is determined entirely by the disclosed
profile and by the coordinate laws through `t`. -/
theorem integral_selectProbability_eq_of_prefix {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (t : Fin m) (laws laws' : Fin m → Distribution)
    (hprefix : ∀ i, i ≤ t → laws i = laws' i) :
    (∫ x, prophetSelectProbability policy profile t x
        ∂(independentValues laws : Measure _)) =
      ∫ x, prophetSelectProbability policy profile t x
        ∂(independentValues laws' : Measure _) := by
  let f := prophetSelectProbability policy profile t
  let T := truncateProphetPath t
  have hf : Measurable f := measurable_prophetSelectProbability policy profile t
  have hT : Measurable T := measurable_truncateProphetPath t
  have hcomp : ∀ x, f x = f (T x) :=
    prophetSelectProbability_truncate policy profile t
  calc
    (∫ x, f x ∂(independentValues laws : Measure _)) =
        ∫ x, f (T x) ∂(independentValues laws : Measure _) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hcomp
    _ = ∫ y, f y ∂Measure.map T (independentValues laws : Measure _) := by
          symm
          exact integral_map hT.aemeasurable
            hf.aestronglyMeasurable
    _ = ∫ y, f y ∂Measure.map T (independentValues laws' : Measure _) := by
          rw [map_truncate_independentValues_eq t laws laws' hprefix]
    _ = ∫ x, f (T x) ∂(independentValues laws' : Measure _) := by
          exact integral_map hT.aemeasurable hf.aestronglyMeasurable
    _ = ∫ x, f x ∂(independentValues laws' : Measure _) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ (hcomp x).symm

/-- Expanding the finite action-space integral exposes one summand per possible stopping
time; the `none` action contributes zero. -/
theorem kernel_reward_eq_sum_selectProbability {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (x : ProphetPath m) :
    (∫ choice, (match choice with | none => 0 | some i => (x i : ℝ))
        ∂policy.kernel (profile, x)) =
      ∑ i : Fin m, (x i : ℝ) * prophetSelectProbability policy profile i x := by
  rw [integral_fintype (MeasureTheory.Integrable.of_finite)]
  simp [Measure.real_def, prophetSelectProbability, mul_comm]

theorem integrable_coordinate_mul_selectProbability {m : ℕ}
    (policy : ProphetPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws) (i : Fin m) :
    Integrable (fun x : ProphetPath m ↦
      (x i : ℝ) * prophetSelectProbability policy profile i x)
      (independentValues laws : Measure _) := by
  apply (integrable_coordinate_cast laws hfirst i).mono
  · exact ((measurable_pi_apply i).coe_nnreal_real.mul
      (measurable_prophetSelectProbability policy profile i)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (x i : ℝ) by positivity),
      abs_of_nonneg (prophetSelectProbability_nonneg policy profile i x)]
    simpa using mul_le_of_le_one_right (show (0 : ℝ) ≤ (x i : ℝ) by positivity)
      (prophetSelectProbability_le_one policy profile i x)

/-- Expected reward is the finite sum of value-weighted stopping probabilities. -/
theorem prophetExpectedReward_eq_sum_selectProbability {m : ℕ}
    (policy : ProphetPolicy m) (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws) :
    prophetExpectedReward policy laws =
      ∑ i : Fin m, ∫ x, (x i : ℝ) *
          prophetSelectProbability policy (disclosedProfile laws) i x
        ∂(independentValues laws : Measure _) := by
  rw [prophetExpectedReward]
  calc
    (∫ x, ∫ choice,
        (match choice with | none => 0 | some i => (x i : ℝ))
        ∂policy.kernel (disclosedProfile laws, x)
      ∂(independentValues laws : Measure _)) =
        ∫ x, ∑ i : Fin m, (x i : ℝ) *
            prophetSelectProbability policy (disclosedProfile laws) i x
          ∂(independentValues laws : Measure _) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        kernel_reward_eq_sum_selectProbability policy (disclosedProfile laws) x
    _ = _ := integral_finset_sum Finset.univ (fun i _ ↦
      integrable_coordinate_mul_selectProbability policy (disclosedProfile laws) laws hfirst i)

/-- Conditional probabilities of selecting the different times have total mass at most one. -/
theorem sum_prophetSelectProbability_le_one {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (x : ProphetPath m) :
    (∑ i : Fin m, prophetSelectProbability policy profile i x) ≤ 1 := by
  have hall : (∑ c : Option (Fin m),
      (policy.kernel (profile, x) {c}).toReal) = 1 := by
    have h := integral_fintype
      (μ := policy.kernel (profile, x))
      (f := fun _ : Option (Fin m) ↦ (1 : ℝ))
      (MeasureTheory.Integrable.of_finite)
    simpa [Measure.real_def] using h.symm
  have hpnone : 0 ≤ (policy.kernel (profile, x) {none}).toReal := ENNReal.toReal_nonneg
  have hdecomp : (policy.kernel (profile, x) {none}).toReal +
      ∑ i : Fin m, prophetSelectProbability policy profile i x = 1 := by
    simpa [prophetSelectProbability] using hall
  linarith

/-- Hence the unconditional stopping probabilities also sum to at most one. -/
theorem sum_integral_prophetSelectProbability_le_one {m : ℕ}
    (policy : ProphetPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) :
    (∑ i : Fin m, ∫ x, prophetSelectProbability policy profile i x
      ∂(independentValues laws : Measure _)) ≤ 1 := by
  rw [← integral_finset_sum Finset.univ (fun i _ ↦
    integrable_prophetSelectProbability policy profile i
      (independentValues laws : Measure _))]
  calc
    (∫ x, ∑ i : Fin m, prophetSelectProbability policy profile i x
        ∂(independentValues laws : Measure _)) ≤
        ∫ _x : ProphetPath m, (1 : ℝ) ∂(independentValues laws : Measure _) := by
      apply integral_mono
      · exact integrable_finset_sum _ fun i _ ↦
          integrable_prophetSelectProbability policy profile i
            (independentValues laws : Measure _)
      · exact integrable_const 1
      · exact sum_prophetSelectProbability_le_one policy profile
    _ = 1 := by simp

/-! ## Coordinate reward truncation -/

/-- Value retained above a closed tail threshold. -/
def upperTailValue (threshold x : ℝ≥0) : ℝ :=
  if threshold ≤ x then (x : ℝ) else 0

theorem measurable_upperTailValue (threshold : ℝ≥0) :
    Measurable (upperTailValue threshold) := by
  unfold upperTailValue
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_coe_nnreal_real measurable_const

theorem upperTailValue_nonneg (threshold x : ℝ≥0) :
    0 ≤ upperTailValue threshold x := by
  simp only [upperTailValue]
  split <;> positivity

theorem upperTailValue_le_cast (threshold x : ℝ≥0) :
    upperTailValue threshold x ≤ (x : ℝ) := by
  by_cases h : threshold ≤ x
  · simp [upperTailValue, h]
  · simp [upperTailValue, h]

theorem integrable_upperTailValue {mu : Distribution} (threshold : ℝ≥0)
    (hfirst : HasFiniteMoment mu 1) :
    Integrable (upperTailValue threshold) (mu : Measure ℝ≥0) := by
  have hcast : Integrable (fun x : ℝ≥0 ↦ (x : ℝ)) (mu : Measure ℝ≥0) := by
    change Integrable (fun x : ℝ≥0 ↦ (x : ℝ) ^ 1) (mu : Measure ℝ≥0) at hfirst
    simpa only [pow_one] using hfirst
  apply hcast.mono
  · exact (measurable_upperTailValue threshold).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (upperTailValue_nonneg threshold x),
      Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (x : ℝ) by positivity)]
    exact upperTailValue_le_cast threshold x

/-- Pulling a tail expectation through the corresponding product coordinate. -/
theorem integral_coordinate_upperTailValue {m : ℕ} (laws : Fin m → Distribution)
    (i : Fin m) (threshold : ℝ≥0) :
    (∫ x : ProphetPath m, upperTailValue threshold (x i)
        ∂(independentValues laws : Measure _)) =
      ∫ y : ℝ≥0, upperTailValue threshold y ∂(laws i : Measure ℝ≥0) := by
  rw [independentValues, ProbabilityMeasure.toMeasure_pi]
  exact MeasureTheory.integral_comp_eval
    (measurable_upperTailValue threshold).aestronglyMeasurable

/-- A support gap below `threshold` gives the standard cap-plus-tail reward bound for one
coordinate, even though the policy's stopping probability may depend on the whole path. -/
theorem coordinate_reward_le_cap_mul_stop_add_tail {m : ℕ}
    (policy : ProphetPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws)
    (i : Fin m) (cap threshold : ℝ≥0)
    (hgap : ∀ᵐ y ∂(laws i : Measure ℝ≥0), y < threshold → y ≤ cap) :
    (∫ x, (x i : ℝ) * prophetSelectProbability policy profile i x
        ∂(independentValues laws : Measure _)) ≤
      (cap : ℝ) *
          (∫ x, prophetSelectProbability policy profile i x
            ∂(independentValues laws : Measure _)) +
        ∫ y, upperTailValue threshold y ∂(laws i : Measure ℝ≥0) := by
  let μprod : Measure (ProphetPath m) := independentValues laws
  let p : ProphetPath m → ℝ := prophetSelectProbability policy profile i
  have hgap_map : ∀ᵐ y ∂Measure.map (Function.eval i) μprod,
      y < threshold → y ≤ cap := by
    have hmap := (MeasureTheory.measurePreserving_eval
      (fun i ↦ (laws i : Measure ℝ≥0)) i).map_eq
    dsimp only [μprod]
    rw [independentValues, ProbabilityMeasure.toMeasure_pi, hmap]
    exact hgap
  have hgap_prod : ∀ᵐ x ∂μprod, x i < threshold → x i ≤ cap :=
    ae_of_ae_map (measurable_pi_apply i).aemeasurable hgap_map
  have hpint : Integrable p μprod :=
    integrable_prophetSelectProbability policy profile i μprod
  have hleft : Integrable (fun x : ProphetPath m ↦ (x i : ℝ) * p x) μprod :=
    integrable_coordinate_mul_selectProbability policy profile laws hfirst i
  have htailLaw : Integrable (upperTailValue threshold) (laws i : Measure ℝ≥0) :=
    integrable_upperTailValue threshold (hfirst i)
  have htailProd : Integrable (fun x : ProphetPath m ↦ upperTailValue threshold (x i)) μprod := by
    dsimp only [μprod]
    rw [independentValues, ProbabilityMeasure.toMeasure_pi]
    exact MeasureTheory.integrable_comp_eval htailLaw
  have hright : Integrable (fun x : ProphetPath m ↦
      (cap : ℝ) * p x + upperTailValue threshold (x i)) μprod :=
    (hpint.const_mul _).add htailProd
  calc
    (∫ x, (x i : ℝ) * p x ∂μprod) ≤
        ∫ x, ((cap : ℝ) * p x + upperTailValue threshold (x i)) ∂μprod := by
      apply integral_mono_ae hleft hright
      filter_upwards [hgap_prod] with x hx
      by_cases htail : threshold ≤ x i
      · rw [upperTailValue, if_pos htail]
        have hp := prophetSelectProbability_le_one policy profile i x
        have hp0 := prophetSelectProbability_nonneg policy profile i x
        have hy : (0 : ℝ) ≤ (x i : ℝ) := by positivity
        have hcap : (0 : ℝ) ≤ (cap : ℝ) := by positivity
        calc
          (x i : ℝ) * p x ≤ (x i : ℝ) :=
            mul_le_of_le_one_right hy hp
          _ ≤ (cap : ℝ) * p x + (x i : ℝ) := by
            exact le_add_of_nonneg_left (mul_nonneg hcap hp0)
      · have hbelow : x i < threshold := lt_of_not_ge htail
        have hcap := hx hbelow
        rw [upperTailValue, if_neg htail, add_zero]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcap)
          (prophetSelectProbability_nonneg policy profile i x)
    _ = (cap : ℝ) * (∫ x, p x ∂μprod) +
        ∫ x, upperTailValue threshold (x i) ∂μprod := by
      rw [integral_add (hpint.const_mul _) htailProd, integral_const_mul]
    _ = _ := by
      rw [integral_coordinate_upperTailValue laws i threshold]

end

end MomentAmbiguity
