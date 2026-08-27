import MomentAmbiguity.Quantile
import MomentAmbiguity.BinarySeparator
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The newsvendor problem

This file formalizes the active newsvendor definitions and the four labelled results in
`sections/quantile.tex`.  Order quantities are real numbers restricted to `Set.Ici 0`; demand and
randomized order laws are probability measures on `ℝ≥0`.  This lets the one-sided derivative
statements use Lean's standard real calculus while retaining the manuscript's nonnegative domain.
-/

open scoped ENNReal NNReal Interval Topology Convex

namespace MomentAmbiguity

open Filter MeasureTheory Set

noncomputable section

/-! ## Definitions from `sections/preliminaries.tex`, lines 47--55 -/

/-- Expected sales `E[min{D,q}]`.  The real order variable is later restricted to `q ≥ 0`. -/
def newsvendorSales (mu : Distribution) (q : ℝ) : ℝ :=
  ∫ d : ℝ≥0, min (d : ℝ) q ∂(mu : Measure ℝ≥0)

/-- The manuscript's normalized newsvendor profit. -/
def newsvendorProfit (mu : Distribution) (beta q : ℝ) : ℝ :=
  newsvendorSales mu q - (1 - beta) * q

/-- A randomized ordering rule is, exactly as in the manuscript, a probability law on
`[0,∞)` together with its finite-first-moment witness. -/
structure RandomizedOrderingRule where
  law : Distribution
  finiteFirstMoment : HasFiniteMoment law 1

instance : Coe RandomizedOrderingRule Distribution := ⟨RandomizedOrderingRule.law⟩

/-- The finite mean order quantity of a randomized ordering rule. -/
def meanOrder (lambda : RandomizedOrderingRule) : ℝ :=
  ∫ q : ℝ≥0, (q : ℝ) ∂(lambda.law : Measure ℝ≥0)

/-- Expected profit of a randomized ordering rule. -/
def randomizedNewsvendorProfit (mu : Distribution) (beta : ℝ)
    (lambda : RandomizedOrderingRule) : ℝ :=
  ∫ q : ℝ≥0, newsvendorProfit mu beta (q : ℝ)
    ∂(lambda.law : Measure ℝ≥0)

/-- The set-valued argmax over the manuscript's feasible set `[0,∞)`. -/
def newsvendorArgmax (mu : Distribution) (beta : ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ ∀ r, 0 ≤ r → newsvendorProfit mu beta r ≤ newsvendorProfit mu beta q}

/-- Push a nonnegative demand law to the real line for use of mathlib's real CDF API. -/
def realDemandMeasure (mu : Distribution) : Measure ℝ :=
  (mu : Measure ℝ≥0).map ((↑) : ℝ≥0 → ℝ)

instance realDemandMeasure.instIsProbabilityMeasure (mu : Distribution) :
    IsProbabilityMeasure (realDemandMeasure mu) := by
  unfold realDemandMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The real CDF of a nonnegative demand law. -/
def realCDF (mu : Distribution) : StieltjesFunction ℝ :=
  ProbabilityTheory.cdf (realDemandMeasure mu)

/-- The left limit `F(q⁻)` of the real CDF. -/
def realOpenCDF (mu : Distribution) (q : ℝ) : ℝ :=
  Function.leftLim (realCDF mu) q

/-- The closed-tail integrand `P[D ≥ t]`, represented as `1-F(t⁻)`.

The representation is chosen because its left and right limits are already exposed by the
`StieltjesFunction` API.  `survivalGE_eq_measureReal` below proves it equals the probability event
used in the manuscript. -/
def survivalGE (mu : Distribution) (t : ℝ) : ℝ :=
  1 - realOpenCDF mu t

theorem realCDF_nonneg (mu : Distribution) (q : ℝ) : 0 ≤ realCDF mu q :=
  ProbabilityTheory.cdf_nonneg _ _

theorem realCDF_le_one (mu : Distribution) (q : ℝ) : realCDF mu q ≤ 1 :=
  ProbabilityTheory.cdf_le_one _ _

theorem realOpenCDF_nonneg (mu : Distribution) (q : ℝ) : 0 ≤ realOpenCDF mu q := by
  have h := (realCDF mu).mono.le_leftLim (show q - 1 < q by linarith)
  exact (realCDF_nonneg mu (q - 1)).trans h

theorem realOpenCDF_le_one (mu : Distribution) (q : ℝ) : realOpenCDF mu q ≤ 1 := by
  exact (realCDF mu).mono.leftLim_le le_rfl |>.trans (realCDF_le_one mu q)

theorem survivalGE_nonneg (mu : Distribution) (q : ℝ) : 0 ≤ survivalGE mu q := by
  simp only [survivalGE]
  linarith [realOpenCDF_le_one mu q]

theorem survivalGE_le_one (mu : Distribution) (q : ℝ) : survivalGE mu q ≤ 1 := by
  simp only [survivalGE]
  linarith [realOpenCDF_nonneg mu q]

theorem realCDF_coe (mu : Distribution) (q : ℝ≥0) :
    realCDF mu (q : ℝ) = (cdf mu q : ℝ) := by
  rw [realCDF, ProbabilityTheory.cdf_eq_real, realDemandMeasure, measureReal_def,
    Measure.map_apply_of_aemeasurable (by fun_prop) measurableSet_Iic]
  simp only [Set.preimage, cdf]
  congr 1

theorem realOpenCDF_coe (mu : Distribution) (q : ℝ≥0) :
    realOpenCDF mu (q : ℝ) = (openCDF mu q : ℝ) := by
  have hmeasure := (realCDF mu).measure_Iio
    (ProbabilityTheory.tendsto_cdf_atBot (realDemandMeasure mu)) (q : ℝ)
  unfold realCDF at hmeasure
  rw [ProbabilityTheory.measure_cdf] at hmeasure
  have hmap : realDemandMeasure mu (Iio (q : ℝ)) =
      (mu : Measure ℝ≥0) (Iio q) := by
    rw [realDemandMeasure, Measure.map_apply_of_aemeasurable (by fun_prop) measurableSet_Iio]
    congr 1
  rw [hmap] at hmeasure
  have hfinite : (mu : Measure ℝ≥0) (Iio q) ≠ ∞ := measure_ne_top _ _
  have hopen : (openCDF mu q : ℝ) = ((mu : Measure ℝ≥0) (Iio q)).toReal := by
    rw [openCDF, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rfl
  calc
    realOpenCDF mu (q : ℝ) = ((mu : Measure ℝ≥0) (Iio q)).toReal := by
      have h := congrArg ENNReal.toReal hmeasure
      rw [ENNReal.toReal_ofReal] at h
      · simpa [realOpenCDF, realCDF] using h.symm
      · simpa [realOpenCDF, realCDF] using realOpenCDF_nonneg mu (q : ℝ)
    _ = (openCDF mu q : ℝ) := hopen.symm

/-- The tail representation really is the probability of the closed tail event. -/
theorem survivalGE_eq_measureReal (mu : Distribution) (q : ℝ) :
    survivalGE mu q = (realDemandMeasure mu).real (Ici q) := by
  have hmeasure := (realCDF mu).measure_Ici
    (ProbabilityTheory.tendsto_cdf_atTop (realDemandMeasure mu)) q
  unfold realCDF at hmeasure
  rw [ProbabilityTheory.measure_cdf] at hmeasure
  rw [Measure.real, hmeasure, ENNReal.toReal_ofReal]
  · rfl
  · exact sub_nonneg.mpr (realOpenCDF_le_one mu q)

theorem survivalGE_eq_original_measureReal (mu : Distribution) (q : ℝ) :
    survivalGE mu q =
      (mu : Measure ℝ≥0).real {d : ℝ≥0 | q ≤ (d : ℝ)} := by
  rw [survivalGE_eq_measureReal, Measure.real, Measure.real, realDemandMeasure,
    Measure.map_apply_of_aemeasurable (by fun_prop) measurableSet_Ici]
  rfl

theorem finiteFirstMoment_integrable_coe {mu : Distribution} (hmu : HasFiniteMoment mu 1) :
    Integrable (fun d : ℝ≥0 ↦ (d : ℝ)) (mu : Measure ℝ≥0) := by
  change Integrable (fun d : ℝ≥0 ↦ (d : ℝ) ^ 1) (mu : Measure ℝ≥0) at hmu
  simpa only [pow_one] using hmu

theorem salesIntegrable {mu : Distribution} {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun d : ℝ≥0 ↦ min (d : ℝ) q) (mu : Measure ℝ≥0) := by
  refine Integrable.mono' (integrable_const q) (by fun_prop) ?_
  filter_upwards [] with d
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min d.coe_nonneg hq)]
  exact min_le_right _ _

/-- Layer-cake identity used in `lem:newsvendor-critical-fractile`. -/
theorem newsvendorSales_eq_tailIntegral (mu : Distribution) {q : ℝ} (hq : 0 ≤ q) :
    newsvendorSales mu q = ∫ t in (0 : ℝ)..q, survivalGE mu t := by
  have hint := (salesIntegrable (mu := mu) hq).integral_eq_integral_Ioc_meas_le
    (Eventually.of_forall fun d ↦ le_min d.coe_nonneg hq)
    (Eventually.of_forall fun d ↦ min_le_right (d : ℝ) q)
  rw [newsvendorSales, intervalIntegral.integral_of_le hq]
  rw [hint]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  rw [survivalGE_eq_original_measureReal]
  apply congrArg (fun s : Set ℝ≥0 ↦ (mu : Measure ℝ≥0).real s)
  ext d
  simp only [mem_setOf_eq]
  constructor
  · intro h
    exact h.trans (min_le_left _ _)
  · intro hd
    exact le_min hd ht.2

/-- An everywhere-defined primitive agreeing with manuscript profit on feasible orders. -/
def tailNewsvendorProfit (mu : Distribution) (beta q : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..q, survivalGE mu t) - (1 - beta) * q

theorem newsvendorProfit_eq_tailProfit (mu : Distribution) (beta : ℝ) {q : ℝ}
    (hq : 0 ≤ q) :
    newsvendorProfit mu beta q = tailNewsvendorProfit mu beta q := by
  rw [newsvendorProfit, tailNewsvendorProfit, newsvendorSales_eq_tailIntegral mu hq]

theorem realOpenCDF_mono (mu : Distribution) : Monotone (realOpenCDF mu) := by
  exact (realCDF mu).mono.leftLim

theorem survivalGE_antitone (mu : Distribution) : Antitone (survivalGE mu) := by
  intro x y hxy
  simp only [survivalGE]
  linarith [realOpenCDF_mono mu hxy]

theorem survivalGE_stronglyMeasurable (mu : Distribution) :
    StronglyMeasurable (survivalGE mu) := by
  exact (survivalGE_antitone mu).measurable.stronglyMeasurable

theorem survivalGE_intervalIntegrable (mu : Distribution) (a b : ℝ) :
    IntervalIntegrable (survivalGE mu) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ ↦ (1 : ℝ)) (by simp)
    (survivalGE_stronglyMeasurable mu).aestronglyMeasurable ?_
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_of_nonneg (survivalGE_nonneg mu q)]
  exact survivalGE_le_one mu q

theorem survivalGE_continuousWithinAt_left (mu : Distribution) (q : ℝ) :
    ContinuousWithinAt (survivalGE mu) (Iic q) q := by
  have hleft : ContinuousWithinAt (fun t ↦ Function.leftLim (realCDF mu) t) (Iic q) q :=
    continuousWithinAt_leftLim_Iic ((realCDF mu).mono.tendsto_leftLim q)
  change ContinuousWithinAt (fun t ↦ 1 - Function.leftLim (realCDF mu) t) (Iic q) q
  exact continuousWithinAt_const.sub hleft

theorem survivalGE_tendsto_right (mu : Distribution) (q : ℝ) :
    Tendsto (survivalGE mu) (𝓝[>] q) (𝓝 (1 - realCDF mu q)) := by
  have hcdf : Tendsto (realCDF mu) (𝓝[>] q) (𝓝 (Function.rightLim (realCDF mu) q)) :=
    (realCDF mu).mono.tendsto_rightLim q
  have hlim : Tendsto (fun t ↦ Function.leftLim (realCDF mu) t) (𝓝[>] q)
      (𝓝 (Function.rightLim (Function.leftLim (realCDF mu)) q)) :=
    (realCDF mu).mono.leftLim.tendsto_rightLim q
  have hrightLim : Function.rightLim (Function.leftLim (realCDF mu)) q =
      Function.rightLim (realCDF mu) q :=
    rightLim_leftLim hcdf
  have hcdfValue : Function.rightLim (realCDF mu) q = realCDF mu q :=
    (realCDF mu).rightLim_eq q
  rw [hrightLim, hcdfValue] at hlim
  change Tendsto (fun t ↦ 1 - Function.leftLim (realCDF mu) t) (𝓝[>] q)
    (𝓝 (1 - realCDF mu q))
  exact tendsto_const_nhds.sub hlim

theorem tailNewsvendorProfit_continuous (mu : Distribution) (beta : ℝ) :
    Continuous (tailNewsvendorProfit mu beta) := by
  have hprimitive : Continuous (fun q ↦ ∫ t in (0 : ℝ)..q, survivalGE mu t) :=
    intervalIntegral.continuous_primitive (fun a b ↦ survivalGE_intervalIntegrable mu a b) 0
  have hcost : Continuous (fun q : ℝ ↦ (1 - beta) * q) :=
    continuous_const.mul continuous_id
  change Continuous
    ((fun q ↦ ∫ t in (0 : ℝ)..q, survivalGE mu t) - fun q ↦ (1 - beta) * q)
  exact hprimitive.sub hcost

theorem newsvendorProfit_continuousOn (mu : Distribution) (beta : ℝ) :
    ContinuousOn (newsvendorProfit mu beta) (Ici 0) := by
  apply (tailNewsvendorProfit_continuous mu beta).continuousOn.congr
  intro q hq
  exact newsvendorProfit_eq_tailProfit mu beta hq

theorem newsvendorSales_concaveOn (mu : Distribution) :
    ConcaveOn ℝ (Ici 0) (newsvendorSales mu) := by
  refine integral_concaveOn_of_integrand_ae (convex_Ici 0) ?_ ?_
  · filter_upwards [] with d
    change ConcaveOn ℝ (Ici 0) ((fun _ : ℝ ↦ (d : ℝ)) ⊓ fun q : ℝ ↦ q)
    exact (concaveOn_const (d : ℝ) (convex_Ici (0 : ℝ))).inf
      (concaveOn_id (convex_Ici (0 : ℝ)))
  · intro q hq
    exact salesIntegrable hq

/-- `lem:newsvendor-critical-fractile` (concavity component),
`sections/quantile.tex`, lines 53--67. -/
theorem newsvendorProfit_concaveOn (mu : Distribution) (beta : ℝ) :
    ConcaveOn ℝ (Ici 0) (newsvendorProfit mu beta) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hs := (newsvendorSales_concaveOn mu).2 hx hy ha hb hab
  simp only [newsvendorProfit, smul_eq_mul] at hs ⊢
  nlinarith

theorem tailNewsvendorProfit_hasLeftDeriv (mu : Distribution) (beta q : ℝ) :
    HasDerivWithinAt (tailNewsvendorProfit mu beta)
      (beta - realOpenCDF mu q) (Iic q) q := by
  have hint : HasDerivWithinAt (fun u ↦ ∫ t in (0 : ℝ)..u, survivalGE mu t)
      (survivalGE mu q) (Iic q) q :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (survivalGE_intervalIntegrable mu 0 q)
      (survivalGE_stronglyMeasurable mu).stronglyMeasurableAtFilter
      (survivalGE_continuousWithinAt_left mu q)
  have hcost : HasDerivWithinAt (fun u : ℝ ↦ (1 - beta) * u) (1 - beta) (Iic q) q :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id q).const_mul (1 - beta)).hasDerivWithinAt :
        HasDerivWithinAt (fun u : ℝ ↦ (1 - beta) * u) ((1 - beta) * 1) (Iic q) q)
  change HasDerivWithinAt
    ((fun u ↦ ∫ t in (0 : ℝ)..u, survivalGE mu t) - fun u ↦ (1 - beta) * u)
    (beta - realOpenCDF mu q) (Iic q) q
  simpa [survivalGE] using hint.sub hcost

theorem tailNewsvendorProfit_hasRightDeriv (mu : Distribution) (beta q : ℝ) :
    HasDerivWithinAt (tailNewsvendorProfit mu beta)
      (beta - realCDF mu q) (Ici q) q := by
  have hint : HasDerivWithinAt (fun u ↦ ∫ t in (0 : ℝ)..u, survivalGE mu t)
      (1 - realCDF mu q) (Ici q) q :=
    intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
      (survivalGE_intervalIntegrable mu 0 q)
      (survivalGE_stronglyMeasurable mu).stronglyMeasurableAtFilter
      ((survivalGE_tendsto_right mu q).mono_left inf_le_left)
  have hcost : HasDerivWithinAt (fun u : ℝ ↦ (1 - beta) * u) (1 - beta) (Ici q) q :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id q).const_mul (1 - beta)).hasDerivWithinAt :
        HasDerivWithinAt (fun u : ℝ ↦ (1 - beta) * u) ((1 - beta) * 1) (Ici q) q)
  change HasDerivWithinAt
    ((fun u ↦ ∫ t in (0 : ℝ)..u, survivalGE mu t) - fun u ↦ (1 - beta) * u)
    (beta - realCDF mu q) (Ici q) q
  simpa using hint.sub hcost

/-- `lem:newsvendor-critical-fractile` (left derivative),
`sections/quantile.tex`, lines 55--57. -/
theorem newsvendorProfit_hasLeftDeriv (mu : Distribution) (beta : ℝ) {q : ℝ}
    (hq : 0 < q) :
    HasDerivWithinAt (newsvendorProfit mu beta)
      (beta - realOpenCDF mu q) (Iic q) q := by
  have heq : newsvendorProfit mu beta =ᶠ[𝓝[Iic q] q] tailNewsvendorProfit mu beta := by
    have hpositive' : ∀ᶠ x : ℝ in 𝓝[Iic q] q, x ∈ Ioi (0 : ℝ) :=
      Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds hq)
    have hpositive : ∀ᶠ x : ℝ in 𝓝[Iic q] q, 0 ≤ x :=
      hpositive'.mono fun _ hx ↦ hx.le
    filter_upwards [hpositive] with x hx
    exact newsvendorProfit_eq_tailProfit mu beta hx
  exact (tailNewsvendorProfit_hasLeftDeriv mu beta q).congr_of_eventuallyEq heq
    (newsvendorProfit_eq_tailProfit mu beta hq.le)

/-- `lem:newsvendor-critical-fractile` (right derivative, including `q=0`),
`sections/quantile.tex`, lines 55--60. -/
theorem newsvendorProfit_hasRightDeriv (mu : Distribution) (beta : ℝ) {q : ℝ}
    (hq : 0 ≤ q) :
    HasDerivWithinAt (newsvendorProfit mu beta)
      (beta - realCDF mu q) (Ici q) q := by
  have heq : newsvendorProfit mu beta =ᶠ[𝓝[Ici q] q] tailNewsvendorProfit mu beta := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact newsvendorProfit_eq_tailProfit mu beta (hq.trans hx)
  exact (tailNewsvendorProfit_hasRightDeriv mu beta q).congr_of_eventuallyEq heq
    (newsvendorProfit_eq_tailProfit mu beta hq)

theorem newsvendorProfit_hasLeftDeriv_cdf (mu : Distribution) (beta : ℝ) {q : ℝ≥0}
    (hq : 0 < q) :
    HasDerivWithinAt (newsvendorProfit mu beta)
      (beta - (openCDF mu q : ℝ)) (Iic (q : ℝ)) (q : ℝ) := by
  simpa [realOpenCDF_coe] using
    newsvendorProfit_hasLeftDeriv mu beta (show (0 : ℝ) < (q : ℝ) by exact_mod_cast hq)

theorem newsvendorProfit_hasRightDeriv_cdf (mu : Distribution) (beta : ℝ) (q : ℝ≥0) :
    HasDerivWithinAt (newsvendorProfit mu beta)
      (beta - (cdf mu q : ℝ)) (Ici (q : ℝ)) (q : ℝ) := by
  simpa [realCDF_coe] using
    newsvendorProfit_hasRightDeriv mu beta (show (0 : ℝ) ≤ (q : ℝ) by positivity)

/-- The critical-fractile crossing set, with `realOpenCDF` spelling `F(q⁻)`. -/
def criticalFractileSet (mu : Distribution) (beta : ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ realOpenCDF mu q ≤ beta ∧ beta ≤ realCDF mu q}

@[simp]
theorem realOpenCDF_zero (mu : Distribution) : realOpenCDF mu 0 = 0 := by
  rw [show (0 : ℝ) = ((0 : ℝ≥0) : ℝ) by rfl, realOpenCDF_coe]
  simp [openCDF]

theorem mem_newsvendorArgmax_of_mem_criticalFractile {mu : Distribution} {beta q : ℝ}
    (hq : q ∈ criticalFractileSet mu beta) : q ∈ newsvendorArgmax mu beta := by
  refine ⟨hq.1, fun r hr ↦ ?_⟩
  rcases lt_trichotomy r q with hrq | rfl | hqr
  · have hleft := (newsvendorProfit_hasLeftDeriv mu beta (lt_of_le_of_lt hr hrq)).mono
      Iio_subset_Iic_self
    have hslope := (newsvendorProfit_concaveOn mu beta).le_slope_of_hasDerivWithinAt_Iio
      hr hq.1 hrq hleft
    apply (slope_nonneg_iff_of_le hrq.le).mp
    exact (sub_nonneg.mpr hq.2.1).trans hslope
  · exact le_rfl
  · have hright := (newsvendorProfit_hasRightDeriv mu beta hq.1).mono Ioi_subset_Ici_self
    have hslope := (newsvendorProfit_concaveOn mu beta).slope_le_of_hasDerivWithinAt_Ioi
      hq.1 hr hqr hright
    rw [slope_def_field] at hslope
    have hnum : newsvendorProfit mu beta r - newsvendorProfit mu beta q ≤ 0 := by
      have hdiv := hslope.trans (sub_nonpos.mpr hq.2.2)
      have hmul := (div_le_iff₀ (sub_pos.mpr hqr)).mp hdiv
      simpa using hmul
    linarith

theorem mem_criticalFractile_of_mem_newsvendorArgmax {mu : Distribution} {beta q : ℝ}
    (hbeta0 : 0 ≤ beta) (hq : q ∈ newsvendorArgmax mu beta) :
    q ∈ criticalFractileSet mu beta := by
  refine ⟨hq.1, ?_, ?_⟩
  · by_cases hq0 : q = 0
    · subst q
      simpa using hbeta0
    · have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
      have hmax : IsMaxOn (newsvendorProfit mu beta) (Icc 0 q) q := by
        intro r hr
        exact hq.2 r hr.1
      have hseg : [q -[ℝ] (0 : ℝ)] ⊆ Icc 0 q := by
        rw [segment_symm]
        exact segment_subset_Icc hq.1
      have htangent : -q ∈ posTangentConeAt (Icc 0 q) q := by
        simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
      have hderiv := (newsvendorProfit_hasLeftDeriv mu beta hqpos).mono
        (show Icc (0 : ℝ) q ⊆ Iic q from Icc_subset_Iic_self)
      have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt htangent
      have : 0 ≤ q * (beta - realOpenCDF mu q) := by simpa using hnonpos
      nlinarith
  · have hmax : IsMaxOn (newsvendorProfit mu beta) (Ici q) q := by
      intro r hr
      exact hq.2 r (hq.1.trans hr)
    have hseg : [q -[ℝ] q + 1] ⊆ Ici q :=
      (segment_subset_Icc (show q ≤ q + 1 by linarith)).trans Icc_subset_Ici_self
    have htangent : (1 : ℝ) ∈ posTangentConeAt (Ici q) q := by
      simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
    have hderiv := newsvendorProfit_hasRightDeriv mu beta hq.1
    have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt htangent
    have : beta - realCDF mu q ≤ 0 := by simpa using hnonpos
    linarith

/-- `lem:newsvendor-critical-fractile` (complete statement),
`sections/quantile.tex`, lines 53--67.

The finite-first-moment assumption is retained exactly as stated in the manuscript, even though
bounded sales at each fixed order make the concavity and derivative calculation valid without it.
-/
theorem newsvendor_critical_fractile (mu : Distribution) (beta : ℝ)
    (_hmu : HasFiniteMoment mu 1) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    ConcaveOn ℝ (Ici 0) (newsvendorProfit mu beta) ∧
      (∀ q : ℝ≥0, 0 < q →
        HasDerivWithinAt (newsvendorProfit mu beta)
          (beta - (openCDF mu q : ℝ)) (Iic (q : ℝ)) (q : ℝ)) ∧
      (∀ q : ℝ≥0,
        HasDerivWithinAt (newsvendorProfit mu beta)
          (beta - (cdf mu q : ℝ)) (Ici (q : ℝ)) (q : ℝ)) ∧
      newsvendorArgmax mu beta = criticalFractileSet mu beta := by
  refine ⟨newsvendorProfit_concaveOn mu beta, ?_, newsvendorProfit_hasRightDeriv_cdf mu beta, ?_⟩
  · intro q hq
    exact newsvendorProfit_hasLeftDeriv_cdf mu beta hq
  · ext q
    constructor
    · exact mem_criticalFractile_of_mem_newsvendorArgmax hbeta0
    · exact mem_newsvendorArgmax_of_mem_criticalFractile

/-! ## Randomized orders (`lem:newsvendor-randomization`) -/

/-- Mean demand, used only in explicit finite-integrability estimates. -/
def meanDemand (mu : Distribution) : ℝ :=
  ∫ d : ℝ≥0, (d : ℝ) ∂(mu : Measure ℝ≥0)

theorem meanDemand_nonneg (mu : Distribution) : 0 ≤ meanDemand mu := by
  exact integral_nonneg fun d ↦ d.coe_nonneg

theorem newsvendorSales_nonneg (mu : Distribution) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ newsvendorSales mu q := by
  exact integral_nonneg fun d ↦ le_min d.coe_nonneg hq

theorem newsvendorSales_le_order (mu : Distribution) {q : ℝ} (hq : 0 ≤ q) :
    newsvendorSales mu q ≤ q := by
  rw [newsvendorSales]
  calc
    (∫ d : ℝ≥0, min (d : ℝ) q ∂(mu : Measure ℝ≥0)) ≤
        ∫ _d : ℝ≥0, q ∂(mu : Measure ℝ≥0) :=
      integral_mono (salesIntegrable hq) (integrable_const q) fun d ↦ min_le_right _ _
    _ = q := by simp

theorem newsvendorSales_le_meanDemand (mu : Distribution) (hmu : HasFiniteMoment mu 1)
    {q : ℝ} (hq : 0 ≤ q) :
    newsvendorSales mu q ≤ meanDemand mu := by
  exact integral_mono (salesIntegrable hq) (finiteFirstMoment_integrable_coe hmu)
    fun d ↦ min_le_left _ _

/-- The explicit bound used by the manuscript to justify integrability under a randomized rule. -/
theorem abs_newsvendorProfit_le (mu : Distribution) (hmu : HasFiniteMoment mu 1)
    {beta q : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) (hq : 0 ≤ q) :
    |newsvendorProfit mu beta q| ≤ meanDemand mu + q := by
  have hs0 := newsvendorSales_nonneg mu hq
  have hsD := newsvendorSales_le_meanDemand mu hmu hq
  have hcost0 : 0 ≤ (1 - beta) * q := mul_nonneg (sub_nonneg.mpr hbeta1) hq
  have hcostq : (1 - beta) * q ≤ q := by nlinarith
  rw [abs_le]
  constructor <;> simp only [newsvendorProfit] <;> nlinarith [meanDemand_nonneg mu]

theorem meanOrder_nonneg (lambda : RandomizedOrderingRule) : 0 ≤ meanOrder lambda := by
  exact integral_nonneg fun q ↦ q.coe_nonneg

theorem randomizedProfitIntegrable (mu : Distribution) (hmu : HasFiniteMoment mu 1)
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (lambda : RandomizedOrderingRule) :
    Integrable (fun q : ℝ≥0 ↦ newsvendorProfit mu beta (q : ℝ))
      (lambda.law : Measure ℝ≥0) := by
  have hcontinuous : Continuous (fun q : ℝ≥0 ↦ newsvendorProfit mu beta (q : ℝ)) :=
    (newsvendorProfit_continuousOn mu beta).comp_continuous continuous_subtype_val
      (fun q ↦ q.coe_nonneg)
  have hbound : Integrable (fun q : ℝ≥0 ↦ meanDemand mu + (q : ℝ))
      (lambda.law : Measure ℝ≥0) :=
    (integrable_const (meanDemand mu)).add
      (finiteFirstMoment_integrable_coe lambda.finiteFirstMoment)
  refine Integrable.mono' hbound hcontinuous.stronglyMeasurable.aestronglyMeasurable ?_
  filter_upwards [] with q
  exact abs_newsvendorProfit_le mu hmu hbeta0 hbeta1 q.coe_nonneg

/-- `lem:newsvendor-randomization`, `sections/quantile.tex`, lines 80--105.

There is no infinite-mean branch: `lambda.finiteFirstMoment` supplies the integrability of the
identity, and `randomizedProfitIntegrable` proves profit integrability before Jensen is applied.
-/
theorem newsvendor_randomization (mu : Distribution) (beta : ℝ)
    (hmu : HasFiniteMoment mu 1) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (lambda : RandomizedOrderingRule) :
    randomizedNewsvendorProfit mu beta lambda ≤
      newsvendorProfit mu beta (meanOrder lambda) := by
  have hJensen := (newsvendorProfit_concaveOn mu beta).le_map_integral
    (μ := (lambda.law : Measure ℝ≥0)) (f := fun q : ℝ≥0 ↦ (q : ℝ))
    (newsvendorProfit_continuousOn mu beta) isClosed_Ici
    (Eventually.of_forall fun q ↦ q.coe_nonneg)
    (finiteFirstMoment_integrable_coe lambda.finiteFirstMoment)
    (by
      change Integrable (fun q : ℝ≥0 ↦ newsvendorProfit mu beta (q : ℝ))
        (lambda.law : Measure ℝ≥0)
      exact randomizedProfitIntegrable mu hmu beta hbeta0 hbeta1 lambda)
  simpa [randomizedNewsvendorProfit, meanOrder, Function.comp_def] using hJensen

/-! ## A reusable unique-optimum criterion -/

theorem cdf_real_eq_measure_toReal (mu : Distribution) (q : ℝ≥0) :
    (cdf mu q : ℝ) = ((mu : Measure ℝ≥0) (Iic q)).toReal := by
  rw [cdf, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rfl

theorem openCDF_real_eq_measure_toReal (mu : Distribution) (q : ℝ≥0) :
    (openCDF mu q : ℝ) = ((mu : Measure ℝ≥0) (Iio q)).toReal := by
  rw [openCDF, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rfl

theorem measure_Iio_eq_zero_of_supported_Ici {mu : Distribution} {a q : ℝ≥0}
    (hsupport : SupportedOn mu (Ici a)) (hq : q ≤ a) :
    (mu : Measure ℝ≥0) (Iio q) = 0 := by
  have hsupport' : (mu : Measure ℝ≥0) (Ici a) = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hsupport
  have hcomp : (mu : Measure ℝ≥0) ((Ici a)ᶜ) = 0 :=
    (prob_compl_eq_zero_iff (μ := (mu : Measure ℝ≥0)) measurableSet_Ici).2 hsupport'
  exact measure_mono_null (fun x hx ↦ by
    change x < q at hx
    change ¬a ≤ x
    exact fun hax ↦ (not_le_of_gt (hx.trans_le hq)) hax) hcomp

theorem measure_Iic_eq_zero_of_supported_Ici {mu : Distribution} {a q : ℝ≥0}
    (hsupport : SupportedOn mu (Ici a)) (hq : q < a) :
    (mu : Measure ℝ≥0) (Iic q) = 0 := by
  have hsupport' : (mu : Measure ℝ≥0) (Ici a) = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hsupport
  have hcomp : (mu : Measure ℝ≥0) ((Ici a)ᶜ) = 0 :=
    (prob_compl_eq_zero_iff (μ := (mu : Measure ℝ≥0)) measurableSet_Ici).2 hsupport'
  exact measure_mono_null (fun x hx ↦ by
    change x ≤ q at hx
    change ¬a ≤ x
    exact fun hax ↦ (not_le_of_gt hq) (hax.trans hx)) hcomp

theorem openCDF_eq_zero_of_supported_Ici {mu : Distribution} {a : ℝ≥0}
    (hsupport : SupportedOn mu (Ici a)) : openCDF mu a = 0 := by
  rw [← NNReal.coe_eq_zero, openCDF_real_eq_measure_toReal,
    measure_Iio_eq_zero_of_supported_Ici hsupport le_rfl]
  simp

theorem cdf_eq_zero_of_supported_Ici {mu : Distribution} {a q : ℝ≥0}
    (hsupport : SupportedOn mu (Ici a)) (hq : q < a) : cdf mu q = 0 := by
  rw [← NNReal.coe_eq_zero, cdf_real_eq_measure_toReal,
    measure_Iic_eq_zero_of_supported_Ici hsupport hq]
  simp

theorem atom_toReal_le_cdf (mu : Distribution) (a : ℝ≥0) :
    ((mu : Measure ℝ≥0) {a}).toReal ≤ (cdf mu a : ℝ) := by
  rw [cdf_real_eq_measure_toReal]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (by simp))

theorem atom_toReal_le_openCDF_of_lt (mu : Distribution) {a q : ℝ≥0} (haq : a < q) :
    ((mu : Measure ℝ≥0) {a}).toReal ≤ (openCDF mu q : ℝ) := by
  rw [openCDF_real_eq_measure_toReal]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (by simpa using haq))

theorem newsvendorSales_eq_order_of_supported_Ici {mu : Distribution} {a : ℝ≥0}
    (hsupport : SupportedOn mu (Ici a)) : newsvendorSales mu (a : ℝ) = a := by
  have hsupport' : (mu : Measure ℝ≥0) (Ici a) = 1 := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hsupport
  have hae : ∀ᵐ d : ℝ≥0 ∂(mu : Measure ℝ≥0), d ∈ Ici a :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hsupport'
  rw [newsvendorSales]
  calc
    (∫ d : ℝ≥0, min (d : ℝ) (a : ℝ) ∂(mu : Measure ℝ≥0)) =
        ∫ _d : ℝ≥0, (a : ℝ) ∂(mu : Measure ℝ≥0) := by
      apply integral_congr_ae
      filter_upwards [hae] with d hd
      exact min_eq_right (by exact_mod_cast hd)
    _ = a := by simp

theorem newsvendorProfit_eq_beta_mul_of_supported_Ici {mu : Distribution} {a : ℝ≥0}
    (hsupport : SupportedOn mu (Ici a)) (beta : ℝ) :
    newsvendorProfit mu beta (a : ℝ) = beta * a := by
  rw [newsvendorProfit, newsvendorSales_eq_order_of_supported_Ici hsupport]
  ring

/-- A lower support point carrying more than the critical-fractile mass is the unique optimum. -/
theorem newsvendorArgmax_eq_singleton_of_supported_Ici_atom {mu : Distribution} {a : ℝ≥0}
    {beta : ℝ} (hbeta : 0 < beta) (hsupport : SupportedOn mu (Ici a))
    (hatom : beta < ((mu : Measure ℝ≥0) {a}).toReal) :
    newsvendorArgmax mu beta = {(a : ℝ)} := by
  ext q
  constructor
  · intro hqmax
    have hcrit := mem_criticalFractile_of_mem_newsvendorArgmax hbeta.le hqmax
    have hqcast : ((q.toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hcrit.1
    have hqnonneg : 0 ≤ q := hcrit.1
    rcases lt_trichotomy q (a : ℝ) with hqa | hqa | haq
    · rw [← hqcast] at hqa
      have hqNN : q.toNNReal < a := by exact_mod_cast hqa
      have hcdf0 := cdf_eq_zero_of_supported_Ici hsupport hqNN
      have : realCDF mu q = 0 := by
        rw [← hqcast, realCDF_coe, hcdf0]
        rfl
      linarith [hcrit.2.2]
    · simpa [hqa]
    · rw [← hqcast] at haq
      have haNN : a < q.toNNReal := by exact_mod_cast haq
      have hopen := atom_toReal_le_openCDF_of_lt mu haNN
      have hopen' : ((mu : Measure ℝ≥0) {a}).toReal ≤ realOpenCDF mu q := by
        rw [← hqcast, realOpenCDF_coe]
        exact hopen
      linarith [hcrit.2.1]
  · intro hq
    simp only [mem_singleton_iff] at hq
    subst q
    apply mem_newsvendorArgmax_of_mem_criticalFractile
    refine ⟨by positivity, ?_, ?_⟩
    · rw [realOpenCDF_coe, openCDF_eq_zero_of_supported_Ici hsupport]
      exact hbeta.le
    · rw [realCDF_coe]
      exact hatom.le.trans (atom_toReal_le_cdf mu a)

/-! ## Binary-separator optima (`lem:newsvendor-optima`) -/

/-- `lem:newsvendor-optima`, `sections/quantile.tex`, lines 112--139.

Singleton argmax equalities express uniqueness; the two following equalities are the corresponding
optimal profits.  All numerical hypotheses occur in the same order as in the manuscript.
-/
theorem newsvendor_optima {n B : ℕ} (d : BinarySeparator.Data n B)
    (beta epsilon : ℝ) (hbetaHalf : (1 : ℝ) / 2 ≤ beta) (hbetaOne : beta < 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hB : 4 / (epsilon * (1 - beta)) ≤ (B : ℝ))
    (hn : max (2 * (B : ℝ)) (2 / (1 - beta)) < (n : ℝ)) :
    newsvendorArgmax d.mu beta = {((B : ℝ≥0) : ℝ)} ∧
      newsvendorProfit d.mu beta (B : ℝ) = beta * B ∧
      newsvendorArgmax d.nu beta = {(1 : ℝ)} ∧
      newsvendorProfit d.nu beta 1 = beta := by
  have htail : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hden : 0 < epsilon * (1 - beta) := mul_pos hepsilon0 htail
  have hden_lt_half : epsilon * (1 - beta) < (1 : ℝ) / 2 := by
    calc
      epsilon * (1 - beta) < 1 * (1 - beta) :=
        mul_lt_mul_of_pos_right hepsilon1 htail
      _ ≤ (1 : ℝ) / 2 := by linarith
  have heigth_lt_fraction : (8 : ℝ) < 4 / (epsilon * (1 - beta)) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have hB8R : (8 : ℝ) < B := heigth_lt_fraction.trans_le hB
  have hB8 : 8 < B := by exact_mod_cast hB8R
  have hB3 : 3 ≤ B := by omega
  have hnTwoB : 2 * (B : ℝ) < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnTwoBNat : 2 * B < n := by exact_mod_cast hnTwoB
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hnTail : 2 / (1 - beta) < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnpos : (0 : ℝ) < n := by positivity
  have htwoMul : (2 : ℝ) < (n : ℝ) * (1 - beta) := by
    have := (div_lt_iff₀ htail).mp hnTail
    nlinarith
  have htwoDiv : 2 / (n : ℝ) < 1 - beta := by
    apply (div_lt_iff₀ hnpos).2
    nlinarith
  have hbetaThreshold : beta < 1 - 2 / (n : ℝ) := by linarith
  have hq1Threshold : 1 - 2 / (n : ℝ) ≤
      1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) := by
    rw [sub_le_sub_iff_left]
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have hscale : (1 : ℝ) ≤ (n : ℝ) * (B : ℝ) ^ 2 := by nlinarith
    have hlarge : (n : ℝ) ≤ (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * ((n : ℝ) * (B : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hscale hnpos.le
        _ = (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by ring
    calc
      1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤ 1 / (n : ℝ) :=
        one_div_le_one_div_of_le hnpos hlarge
      _ ≤ 2 / (n : ℝ) := div_le_div_of_nonneg_right (by norm_num) hnpos.le
  have hmuAtom : beta < ((d.mu : Measure ℝ≥0) {(B : ℝ≥0)}).toReal := by
    calc
      beta < 1 - 2 / (n : ℝ) := hbetaThreshold
      _ ≤ 1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) := hq1Threshold
      _ ≤ ((d.mu : Measure ℝ≥0) {BinarySeparator.nodeNN n B 1}).toReal := d.q1_ge
      _ = ((d.mu : Measure ℝ≥0) {(B : ℝ≥0)}).toReal := by simp
  have hnuAtom : beta < ((d.nu : Measure ℝ≥0) {(1 : ℝ≥0)}).toReal := by
    calc
      beta < 1 - 2 / (n : ℝ) := hbetaThreshold
      _ ≤ ((d.nu : Measure ℝ≥0) {BinarySeparator.nodeNN n B 0}).toReal := d.p0_ge
      _ = ((d.nu : Measure ℝ≥0) {(1 : ℝ≥0)}).toReal := by simp
  have hmuSupport := d.mu_supported_Ici hn3 hB3
  have hnuSupport := d.nu_supported_Ici_one hn3 hB3
  refine ⟨newsvendorArgmax_eq_singleton_of_supported_Ici_atom
      (lt_of_lt_of_le (by norm_num) hbetaHalf) hmuSupport hmuAtom,
    newsvendorProfit_eq_beta_mul_of_supported_Ici hmuSupport beta, ?_, ?_⟩
  · simpa using newsvendorArgmax_eq_singleton_of_supported_Ici_atom
      (lt_of_lt_of_le (by norm_num) hbetaHalf) hnuSupport hnuAtom
  · simpa using newsvendorProfit_eq_beta_mul_of_supported_Ici hnuSupport beta

/-! ## The randomized incompatibility bound (`thm:newsvendor`) -/

theorem newsvendorProfit_le_beta_mul_order (mu : Distribution) (beta : ℝ) {q : ℝ}
    (hq : 0 ≤ q) : newsvendorProfit mu beta q ≤ beta * q := by
  have hs := newsvendorSales_le_order mu hq
  simp only [newsvendorProfit]
  nlinarith

theorem atom_toReal_le_one (mu : Distribution) (a : ℝ≥0) :
    ((mu : Measure ℝ≥0) {a}).toReal ≤ 1 := by
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact_mod_cast mu.apply_le_one {a}

/-- If a law puts mass `p` at `a`, expected sales are bounded by `p a + (1-p)q`.
This is the atom/tail split used in the proof of `thm:newsvendor`. -/
theorem newsvendorSales_le_atom_envelope (mu : Distribution) (a : ℝ≥0) {q : ℝ}
    (hq : 0 ≤ q) :
    newsvendorSales mu q ≤
      ((mu : Measure ℝ≥0) {a}).toReal * (a : ℝ) +
        (1 - ((mu : Measure ℝ≥0) {a}).toReal) * q := by
  classical
  let envelope : ℝ≥0 → ℝ :=
    ({a} : Set ℝ≥0).piecewise (fun _ ↦ (a : ℝ)) (fun _ ↦ q)
  have henvelope : Integrable envelope (mu : Measure ℝ≥0) := by
    exact Integrable.piecewise (measurableSet_singleton a)
      (integrable_const (a : ℝ)).integrableOn (integrable_const q).integrableOn
  have hpoint : ∀ d : ℝ≥0, min (d : ℝ) q ≤ envelope d := by
    intro d
    by_cases hda : d = a
    · subst d
      simp [envelope, Set.piecewise]
    · simp [envelope, Set.piecewise, hda]
  rw [newsvendorSales]
  calc
    (∫ d : ℝ≥0, min (d : ℝ) q ∂(mu : Measure ℝ≥0)) ≤
        ∫ d : ℝ≥0, envelope d ∂(mu : Measure ℝ≥0) :=
      integral_mono (salesIntegrable hq) henvelope hpoint
    _ = ∫ _d : ℝ≥0 in ({a} : Set ℝ≥0), (a : ℝ) ∂(mu : Measure ℝ≥0) +
        ∫ _d : ℝ≥0 in ({a} : Set ℝ≥0)ᶜ, q ∂(mu : Measure ℝ≥0) := by
      exact integral_piecewise (measurableSet_singleton a)
        (integrable_const (a : ℝ)).integrableOn (integrable_const q).integrableOn
    _ = ((mu : Measure ℝ≥0) {a}).toReal * (a : ℝ) +
        ((mu : Measure ℝ≥0) ({a} : Set ℝ≥0)ᶜ).toReal * q := by
      rw [setIntegral_const, setIntegral_const]
      change ((mu : Measure ℝ≥0) {a}).toReal * (a : ℝ) +
        ((mu : Measure ℝ≥0) ({a} : Set ℝ≥0)ᶜ).toReal * q = _
      simp only [smul_eq_mul]
    _ = ((mu : Measure ℝ≥0) {a}).toReal * (a : ℝ) +
        (1 - ((mu : Measure ℝ≥0) {a}).toReal) * q := by
      change (mu : Measure ℝ≥0).real {a} * (a : ℝ) +
        (mu : Measure ℝ≥0).real ({a} : Set ℝ≥0)ᶜ * q = _
      rw [measureReal_compl (μ := (mu : Measure ℝ≥0)) (s := ({a} : Set ℝ≥0))
        (measurableSet_singleton a)]
      simp
      have hatom : (mu {a} : ℝ) = ((mu : Measure ℝ≥0) {a}).toReal := by
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        rfl
      rw [hatom]

/-- Division-free form of `thm:newsvendor`.  This is the primary guarantee statement: at least
one law gives less than `epsilon` times its (later proved positive) optimal value. -/
theorem newsvendor_universal_guarantee {n B : ℕ} (d : BinarySeparator.Data n B)
    (beta epsilon : ℝ) (hbetaHalf : (1 : ℝ) / 2 ≤ beta) (hbetaOne : beta < 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hB : 4 / (epsilon * (1 - beta)) ≤ (B : ℝ))
    (hn : max (2 * (B : ℝ)) (2 / (1 - beta)) < (n : ℝ))
    (lambda : RandomizedOrderingRule) :
    randomizedNewsvendorProfit d.mu beta lambda < epsilon * (beta * (B : ℝ)) ∨
      randomizedNewsvendorProfit d.nu beta lambda < epsilon * beta := by
  have hbeta0 : 0 ≤ beta := le_trans (by norm_num) hbetaHalf
  have hbetaPos : 0 < beta := lt_of_lt_of_le (by norm_num) hbetaHalf
  have htail : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hden : 0 < epsilon * (1 - beta) := mul_pos hepsilon0 htail
  have hcost : 4 ≤ (1 - beta) * (epsilon * (B : ℝ)) := by
    have hc := (div_le_iff₀ hden).mp hB
    calc
      (4 : ℝ) ≤ (B : ℝ) * (epsilon * (1 - beta)) := hc
      _ = (1 - beta) * (epsilon * (B : ℝ)) := by ring
  have hBpos : (0 : ℝ) < B := by
    have hfrac : 0 < 4 / (epsilon * (1 - beta)) := div_pos (by norm_num) hden
    exact hfrac.trans_le hB
  have hnTwoB : 2 * (B : ℝ) < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnpos : (0 : ℝ) < n := by nlinarith
  have hnTail : 2 / (1 - beta) < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have htwoMul : (2 : ℝ) < (n : ℝ) * (1 - beta) := by
    have := (div_lt_iff₀ htail).mp hnTail
    nlinarith
  have htwoDiv : 2 / (n : ℝ) < 1 - beta := by
    apply (div_lt_iff₀ hnpos).2
    nlinarith
  have hbetaThreshold : beta < 1 - 2 / (n : ℝ) := by linarith
  have hmuFinite : HasFiniteMoment d.mu 1 := d.momentEquivalent.left_finite 1
  have hnuFinite : HasFiniteMoment d.nu 1 := d.momentEquivalent.right_finite 1
  have hmuJensen := newsvendor_randomization d.mu beta hmuFinite hbeta0 hbetaOne.le lambda
  have hnuJensen := newsvendor_randomization d.nu beta hnuFinite hbeta0 hbetaOne.le lambda
  have hmean0 := meanOrder_nonneg lambda
  by_cases hmean : meanOrder lambda < epsilon * (B : ℝ)
  · left
    have hdet := newsvendorProfit_le_beta_mul_order d.mu beta hmean0
    have hstrict : beta * meanOrder lambda < beta * (epsilon * (B : ℝ)) :=
      mul_lt_mul_of_pos_left hmean hbetaPos
    nlinarith
  · right
    have hmeanGe : epsilon * (B : ℝ) ≤ meanOrder lambda := le_of_not_gt hmean
    let p : ℝ := ((d.nu : Measure ℝ≥0) {(1 : ℝ≥0)}).toReal
    have hpBeta : beta < p := by
      calc
        beta < 1 - 2 / (n : ℝ) := hbetaThreshold
        _ ≤ ((d.nu : Measure ℝ≥0) {BinarySeparator.nodeNN n B 0}).toReal := d.p0_ge
        _ = p := by simp [p]
    have hpOne : p ≤ 1 := atom_toReal_le_one d.nu 1
    have hpTail : 1 - p ≤ 2 / (n : ℝ) := by
      have hp0 : 1 - 2 / (n : ℝ) ≤ p := by simpa [p] using d.p0_ge
      linarith
    have hsales := newsvendorSales_le_atom_envelope d.nu (1 : ℝ≥0) hmean0
    have hprofit : randomizedNewsvendorProfit d.nu beta lambda ≤
        p + (beta - p) * meanOrder lambda := by
      simp only [newsvendorProfit] at hnuJensen
      dsimp [p] at hsales ⊢
      nlinarith
    have hcoef : beta - p < 0 := sub_neg.mpr hpBeta
    have hcoefMean : (beta - p) * meanOrder lambda ≤
        (beta - p) * (epsilon * (B : ℝ)) :=
      mul_le_mul_of_nonpos_left hmeanGe hcoef.le
    have hprofitAtCut : randomizedNewsvendorProfit d.nu beta lambda ≤
        p + (beta - p) * (epsilon * (B : ℝ)) := by linarith
    have hcut0 : 0 ≤ epsilon * (B : ℝ) := (mul_pos hepsilon0 hBpos).le
    have hpTailMul : (1 - p) * (epsilon * (B : ℝ)) ≤
        (2 / (n : ℝ)) * (epsilon * (B : ℝ)) :=
      mul_le_mul_of_nonneg_right hpTail hcut0
    have hratio : 2 * (B : ℝ) / (n : ℝ) < 1 := by
      apply (div_lt_iff₀ hnpos).2
      nlinarith
    have hsmall : (2 / (n : ℝ)) * (epsilon * (B : ℝ)) < epsilon := by
      have hm := mul_lt_mul_of_pos_left hratio hepsilon0
      have heq : (2 / (n : ℝ)) * (epsilon * (B : ℝ)) =
          epsilon * (2 * (B : ℝ) / (n : ℝ)) := by
        field_simp [ne_of_gt hnpos]
        <;> ring
      rw [heq]
      simpa only [mul_one] using hm
    have hnegative : randomizedNewsvendorProfit d.nu beta lambda < 0 := by
      nlinarith
    nlinarith [mul_pos hepsilon0 hbetaPos]

/-- `thm:newsvendor`, `sections/quantile.tex`, lines 145--185.

The displayed divisions occur only here, after `newsvendor_optima` has identified the denominators
and the proof below has established that both are strictly positive. -/
theorem newsvendor_impossibility {n B : ℕ} (d : BinarySeparator.Data n B)
    (beta epsilon : ℝ) (hbetaHalf : (1 : ℝ) / 2 ≤ beta) (hbetaOne : beta < 1)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hB : 4 / (epsilon * (1 - beta)) ≤ (B : ℝ))
    (hn : max (2 * (B : ℝ)) (2 / (1 - beta)) < (n : ℝ))
    (lambda : RandomizedOrderingRule) :
    min (randomizedNewsvendorProfit d.mu beta lambda / (beta * (B : ℝ)))
        (randomizedNewsvendorProfit d.nu beta lambda / beta) < epsilon := by
  have hbetaPos : 0 < beta := lt_of_lt_of_le (by norm_num) hbetaHalf
  have htail : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hden : 0 < epsilon * (1 - beta) := mul_pos hepsilon0 htail
  have hBpos : (0 : ℝ) < B :=
    (div_pos (by norm_num) hden).trans_le hB
  have hmuOptPos : 0 < beta * (B : ℝ) := mul_pos hbetaPos hBpos
  have _hoptima := newsvendor_optima d beta epsilon hbetaHalf hbetaOne hepsilon0 hepsilon1 hB hn
  rcases newsvendor_universal_guarantee d beta epsilon hbetaHalf hbetaOne
      hepsilon0 hepsilon1 hB hn lambda with hmu | hnu
  · exact (min_lt_iff.mpr <| Or.inl ((div_lt_iff₀ hmuOptPos).2 hmu))
  · exact (min_lt_iff.mpr <| Or.inr ((div_lt_iff₀ hbetaPos).2 hnu))

end

end MomentAmbiguity
