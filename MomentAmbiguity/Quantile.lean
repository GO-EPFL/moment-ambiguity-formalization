import MomentAmbiguity.BinarySeparator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Distribution functions and lower quantiles

The manuscript defines quantiles only on `(0,1)`.  For compositional Lean definitions we extend
the lower quantile to all real levels and choose the harmless value `0` outside `(0,1)`.  In
particular its value at the null endpoint of the LCVaR integral is arbitrary and irrelevant.
-/

open scoped ENNReal NNReal Interval

namespace MomentAmbiguity

open MeasureTheory Set

noncomputable section

/-- Closed CDF `P[X ≤ x]`. -/
def cdf (mu : Distribution) (x : ℝ≥0) : ℝ≥0 := mu (Iic x)

/-- Open CDF `P[X < x]`. -/
def openCDF (mu : Distribution) (x : ℝ≥0) : ℝ≥0 := mu (Iio x)

theorem cdf_mono (mu : Distribution) : Monotone (cdf mu) := by
  intro x y hxy
  exact mu.apply_mono (Iic_subset_Iic.2 hxy)

theorem openCDF_le_cdf (mu : Distribution) (x : ℝ≥0) :
    openCDF mu x ≤ cdf mu x := by
  exact mu.apply_mono Iio_subset_Iic_self

/-- The globally defined lower quantile.  Its out-of-domain value is fixed to zero. -/
def lowerQuantile (mu : Distribution) (u : ℝ) : ℝ≥0 :=
  if 0 < u ∧ u < 1 then
    sInf {x : ℝ≥0 | ENNReal.ofReal u ≤ (cdf mu x : ℝ≥0∞)}
  else 0

/-- Value-at-Risk is the lower quantile. -/
abbrev valueAtRisk := lowerQuantile

/-- Lower-tail average quantile.  The interval integral ignores both endpoints. -/
def lowerCVaR (mu : Distribution) (u : ℝ) : ℝ :=
  u⁻¹ * ∫ t in (0 : ℝ)..u, (lowerQuantile mu t : ℝ)

@[simp]
theorem lowerQuantile_of_nonpos (mu : Distribution) {u : ℝ} (hu : u ≤ 0) :
    lowerQuantile mu u = 0 := by
  simp [lowerQuantile, not_lt_of_ge hu]

@[simp]
theorem lowerQuantile_of_one_le (mu : Distribution) {u : ℝ} (hu : 1 ≤ u) :
    lowerQuantile mu u = 0 := by
  simp [lowerQuantile, not_lt_of_ge hu]

/-- A CDF crossing at `a` identifies the lower quantile exactly. -/
theorem lowerQuantile_eq_of_crossing (mu : Distribution) {u : ℝ} {a : ℝ≥0}
    (hu0 : 0 < u) (hu1 : u < 1)
    (hbelow : ∀ x < a, (cdf mu x : ℝ≥0∞) < ENNReal.ofReal u)
    (hat : ENNReal.ofReal u ≤ (cdf mu a : ℝ≥0∞)) :
    lowerQuantile mu u = a := by
  rw [lowerQuantile, if_pos ⟨hu0, hu1⟩]
  have hset : {x : ℝ≥0 | ENNReal.ofReal u ≤ (cdf mu x : ℝ≥0∞)} = Ici a := by
    ext x
    constructor
    · intro hx
      by_contra hxa
      have hlt : x < a := lt_of_not_ge hxa
      exact (not_lt_of_ge hx) (hbelow x hlt)
    · intro hx
      exact hat.trans (by
        exact_mod_cast cdf_mono mu (show a ≤ x from hx))
  rw [hset, csInf_Ici]

/-- A distribution supported above `a` and carrying at least level `u` at `a` has quantile
exactly `a`.  `SupportedOn` means measure one, not merely topological support containment. -/
theorem lowerQuantile_eq_of_supported_Ici_atom (mu : Distribution) {u : ℝ} {a : ℝ≥0}
    (hu0 : 0 < u) (hu1 : u < 1)
    (hsupport : SupportedOn mu (Ici a))
    (hatom : ENNReal.ofReal u ≤ ((mu : Measure ℝ≥0) {a})) :
    lowerQuantile mu u = a := by
  apply lowerQuantile_eq_of_crossing mu hu0 hu1
  · intro x hxa
    have hnull : (mu : Measure ℝ≥0) (Iic x) = 0 := by
      have hsupport' : (mu : Measure ℝ≥0) (Ici a) = 1 := by
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hsupport
      have hcomp : (mu : Measure ℝ≥0) ((Ici a)ᶜ) = 0 :=
        (prob_compl_eq_zero_iff (μ := (mu : Measure ℝ≥0)) measurableSet_Ici).2 hsupport'
      exact measure_mono_null (by
        intro y hy
        simp only [mem_Iic, mem_compl_iff, mem_Ici]
        exact fun hay ↦ (not_le_of_gt hxa) (hay.trans hy)) hcomp
    have hcdf0 : (cdf mu x : ℝ≥0∞) = 0 := by
      simpa [cdf, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hnull
    rw [hcdf0]
    exact ENNReal.ofReal_pos.mpr hu0
  · exact hatom.trans (by
      simpa [cdf, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        measure_mono (show ({a} : Set ℝ≥0) ⊆ Iic a by simp))

/-- If a quantile is constant on every positive level through `u`, then LCVaR equals that
constant.  This also proves explicitly that the arbitrary value at level zero is irrelevant. -/
theorem lowerCVaR_eq_of_quantile_constant (mu : Distribution) {u : ℝ} {a : ℝ≥0}
    (hu : 0 < u) (hQ : ∀ t, 0 < t → t ≤ u → lowerQuantile mu t = a) :
    lowerCVaR mu u = a := by
  have hAE : (fun t : ℝ ↦ (lowerQuantile mu t : ℝ)) =ᵐ[volume.restrict (uIoc 0 u)]
      fun _ ↦ (a : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hu.le] at ht
    exact_mod_cast hQ t ht.1 ht.2
  rw [lowerCVaR, intervalIntegral.integral_congr_ae_restrict hAE]
  simp [hu.ne']

/-- Regression: the chosen global endpoint value is zero. -/
example (mu : Distribution) : lowerQuantile mu 0 = 0 := by simp

/-! ## Consequences of the binary separator -/

namespace BinarySeparator.Data

/-- The odd law has no mass below its first support point `B`. -/
theorem mu_supported_Ici {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 3 ≤ n) (hB : 3 ≤ B) : SupportedOn d.mu (Ici (B : ℝ≥0)) := by
  apply SupportedOn.mono (s := BinarySeparator.oddSupport n B)
  · unfold SupportedOn
    rw [← ENNReal.coe_inj, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using d.mu_support
  · rintro x ⟨j, hj, rfl⟩
    have hj1 : 1 ≤ j := by
      rcases hj with ⟨k, rfl⟩
      omega
    exact_mod_cast (BinarySeparator.node_strictMono hn hB).monotone hj1

/-- The even law has no mass below its first support point `1`. -/
theorem nu_supported_Ici_one {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 3 ≤ n) (hB : 3 ≤ B) : SupportedOn d.nu (Ici (1 : ℝ≥0)) := by
  apply SupportedOn.mono (s := BinarySeparator.evenSupport n B)
  · unfold SupportedOn
    rw [← ENNReal.coe_inj, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa using d.nu_support
  · rintro x ⟨j, hj, rfl⟩
    exact_mod_cast (BinarySeparator.node_strictMono hn hB).monotone (Nat.zero_le j)

private theorem ofReal_le_atom_of_le_toReal (mu : Distribution) (a : ℝ≥0) {u : ℝ}
    (h : u ≤ ((mu : Measure ℝ≥0) {a}).toReal) :
    ENNReal.ofReal u ≤ (mu : Measure ℝ≥0) {a} := by
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 h

/-- The `μ` quantile is its designated first atom throughout the manuscript's range. -/
theorem lowerQuantile_mu_eq {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 4 ≤ n) (hB : 3 ≤ B) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ 1 - 2 / (n : ℝ)) :
    lowerQuantile d.mu u = B := by
  have hn3 : 3 ≤ n := by omega
  have hu1 : u < 1 := by
    have hnpos : (0 : ℝ) < n := by positivity
    have : (0 : ℝ) < 2 / n := div_pos (by norm_num) hnpos
    linarith
  apply lowerQuantile_eq_of_supported_Ici_atom d.mu hu0 hu1
    (d.mu_supported_Ici hn3 hB)
  apply ofReal_le_atom_of_le_toReal
  calc
    u ≤ 1 - 2 / (n : ℝ) := hu
    _ ≤ 1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) := by
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
      rw [sub_le_sub_iff_left]
      have hnpos : (0 : ℝ) < n := by positivity
      have hscale : (1 : ℝ) ≤ (n : ℝ) * (B : ℝ) ^ 2 := by
        have hn1 : (1 : ℝ) ≤ n := by linarith
        have hB1 : (1 : ℝ) ≤ (B : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hB1)]
      have hden : (n : ℝ) ≤ (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by
        calc
          (n : ℝ) = (n : ℝ) * 1 := by ring
          _ ≤ (n : ℝ) * ((n : ℝ) * (B : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hscale hnpos.le
          _ = (n : ℝ) ^ 2 * (B : ℝ) ^ 2 := by ring
      calc
        1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤ 1 / (n : ℝ) :=
          one_div_le_one_div_of_le hnpos hden
        _ ≤ 2 / (n : ℝ) := by
          apply div_le_div_of_nonneg_right (by norm_num) hnpos.le
    _ ≤ ((d.mu : Measure ℝ≥0) {BinarySeparator.nodeNN n B 1}).toReal := d.q1_ge

/-- The `ν` quantile is its designated first atom throughout the manuscript's range. -/
theorem lowerQuantile_nu_eq {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 4 ≤ n) (hB : 3 ≤ B) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ 1 - 2 / (n : ℝ)) :
    lowerQuantile d.nu u = 1 := by
  have hn3 : 3 ≤ n := by omega
  have hu1 : u < 1 := by
    have hnpos : (0 : ℝ) < n := by positivity
    have : (0 : ℝ) < 2 / n := div_pos (by norm_num) hnpos
    linarith
  apply lowerQuantile_eq_of_supported_Ici_atom d.nu hu0 hu1
    (d.nu_supported_Ici_one hn3 hB)
  apply ofReal_le_atom_of_le_toReal
  exact hu.trans d.p0_ge

/-- `cor:risk-quantile-separation`, `sections/quantile.tex`: VaR range. -/
theorem risk_quantile_separation_var {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 4 ≤ n) (hB : 3 ≤ B) {u : ℝ}
    (hu : (1 : ℝ) / 2 ≤ u) (hu' : u ≤ 1 - 2 / (n : ℝ)) :
    valueAtRisk d.mu u = B ∧ valueAtRisk d.nu u = 1 := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  exact ⟨d.lowerQuantile_mu_eq hn hB hu0 hu', d.lowerQuantile_nu_eq hn hB hu0 hu'⟩

/-- `cor:risk-quantile-separation`, `sections/quantile.tex`: LCVaR range. -/
theorem risk_quantile_separation_lcvar {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 4 ≤ n) (hB : 3 ≤ B) {u : ℝ}
    (hu0 : 0 < u) (hu : u ≤ 1 - 2 / (n : ℝ)) :
    lowerCVaR d.mu u = B ∧ lowerCVaR d.nu u = 1 := by
  constructor
  · apply lowerCVaR_eq_of_quantile_constant d.mu (a := (B : ℝ≥0)) hu0
    intro t ht htu
    exact d.lowerQuantile_mu_eq hn hB ht (htu.trans hu)
  · apply lowerCVaR_eq_of_quantile_constant d.nu (a := (1 : ℝ≥0)) hu0
    intro t ht htu
    exact d.lowerQuantile_nu_eq hn hB ht (htu.trans hu)

end BinarySeparator.Data

/-! ## Literal manuscript corollaries -/

/-- `cor:quantile-separation`, `sections/quantile.tex`: literal existential form. -/
theorem quantile_separation (beta : ℝ) (hbeta0 : (1 : ℝ) / 2 ≤ beta)
    (hbeta1 : beta < 1) (B : ℕ) (hB : 3 ≤ B) :
    ∃ mu nu : Distribution, MomentEquivalent mu nu ∧
      lowerQuantile mu beta = B ∧ lowerQuantile nu beta = 1 := by
  obtain ⟨n : ℕ, hnlarge : max (4 : ℝ) (2 / (1 - beta)) < n⟩ :=
    exists_nat_gt (max (4 : ℝ) (2 / (1 - beta)))
  have hn4 : 4 ≤ n := by
    have h4R : (4 : ℝ) < n := (le_max_left _ _).trans_lt hnlarge
    exact_mod_cast h4R.le
  have hn3 : 3 ≤ n := by omega
  have hden : 0 < 1 - beta := sub_pos.mpr hbeta1
  have hratio : 2 / (1 - beta) < (n : ℝ) :=
    (le_max_right (4 : ℝ) (2 / (1 - beta))).trans_lt hnlarge
  have hprod : (2 : ℝ) < n * (1 - beta) :=
    (div_lt_iff₀ hden).mp hratio
  have hnR : (0 : ℝ) < n := by positivity
  have hrange : beta ≤ 1 - 2 / (n : ℝ) := by
    have : (2 : ℝ) / n < 1 - beta := (div_lt_iff₀ hnR).2 (by nlinarith)
    linarith
  let d := BinarySeparator.binarySeparator n B hn3 hB
  refine ⟨d.mu, d.nu, d.momentEquivalent, ?_, ?_⟩
  · exact d.lowerQuantile_mu_eq hn4 hB (lt_of_lt_of_le (by norm_num) hbeta0) hrange
  · exact d.lowerQuantile_nu_eq hn4 hB (lt_of_lt_of_le (by norm_num) hbeta0) hrange

/-- A capacity is feasible at service level `beta` when its closed CDF reaches `beta`. -/
def ServiceLevelFeasible (mu : Distribution) (beta : ℝ) (q : ℝ≥0) : Prop :=
  ENNReal.ofReal beta ≤ (cdf mu q : ℝ≥0∞)

/-- A moment-based capacity rule receives only the disclosed full moment sequence. -/
abbrev CapacityRule := MomentSequence → ℝ≥0

/-- Exact static specialization of `def:moment-based-policy`: besides receiving only the
disclosed moment sequence, the capacity rule is measurable for the product Borel structure on
moment sequences.  The manuscript corollary is exposed with this type below; the unrestricted
`CapacityRule` theorem is retained as a useful strengthening. -/
abbrev MeasurableCapacityRule := {rule : CapacityRule // Measurable rule}

/-- Uniform feasibility over every law compatible with one moment disclosure. -/
def RobustCapacityFeasible (rule : CapacityRule) (moments : MomentSequence)
    (beta : ℝ) : Prop :=
  ∀ mu : Distribution, mu ∈ momentClass moments →
    ServiceLevelFeasible mu beta (rule moments)

/-- Integer-base helper for `cor:chance-capacity`. -/
theorem chance_capacity_nat (beta : ℝ) (hbeta0 : (1 : ℝ) / 2 ≤ beta)
    (hbeta1 : beta < 1) (B : ℕ) (hB : 3 ≤ B) :
    ∃ mu nu : Distribution, MomentEquivalent mu nu ∧
      (∀ rule : CapacityRule,
        RobustCapacityFeasible rule (momentSequence mu) beta →
          (B : ℝ≥0) ≤ rule (momentSequence mu)) ∧
      IsLeast {q : ℝ≥0 | ServiceLevelFeasible nu beta q} 1 := by
  obtain ⟨n : ℕ, hnlarge : max (4 : ℝ) (2 / (1 - beta)) < n⟩ :=
    exists_nat_gt (max (4 : ℝ) (2 / (1 - beta)))
  have hn4 : 4 ≤ n := by
    have h4R : (4 : ℝ) < n := (le_max_left _ _).trans_lt hnlarge
    exact_mod_cast h4R.le
  have hn3 : 3 ≤ n := by omega
  have hden : 0 < 1 - beta := sub_pos.mpr hbeta1
  have hratio : 2 / (1 - beta) < (n : ℝ) :=
    (le_max_right (4 : ℝ) (2 / (1 - beta))).trans_lt hnlarge
  have hprod : (2 : ℝ) < n * (1 - beta) :=
    (div_lt_iff₀ hden).mp hratio
  have hnR : (0 : ℝ) < n := by positivity
  have hrange : beta ≤ 1 - 2 / (n : ℝ) := by
    have : (2 : ℝ) / n < 1 - beta := (div_lt_iff₀ hnR).2 (by nlinarith)
    linarith
  have hbetaPos : 0 < beta := lt_of_lt_of_le (by norm_num) hbeta0
  let d := BinarySeparator.binarySeparator n B hn3 hB
  have hmuMember : d.mu ∈ momentClass (momentSequence d.mu) :=
    ⟨d.momentEquivalent.left_finite, rfl⟩
  have hnuSupport := d.nu_supported_Ici_one hn3 hB
  have hnuFeasible : ServiceLevelFeasible d.nu beta 1 := by
    unfold ServiceLevelFeasible
    have hbetaAtom : ENNReal.ofReal beta ≤
        (d.nu : Measure ℝ≥0) {BinarySeparator.nodeNN n B 0} := by
      apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
      exact hrange.trans d.p0_ge
    exact hbetaAtom.trans (by
      simpa [cdf, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        measure_mono (show ({(1 : ℝ≥0)} : Set ℝ≥0) ⊆ Iic 1 by simp))
  refine ⟨d.mu, d.nu, d.momentEquivalent, ?_, ⟨hnuFeasible, ?_⟩⟩
  · intro rule hrule
    have hfeas := hrule d.mu hmuMember
    by_contra hnot
    have hqB : rule (momentSequence d.mu) < (B : ℝ≥0) := lt_of_not_ge hnot
    have hnull : (d.mu : Measure ℝ≥0) (Iic (rule (momentSequence d.mu))) = 0 := by
      have hsupport' : (d.mu : Measure ℝ≥0) (Ici (B : ℝ≥0)) = 1 := by
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) (d.mu_supported_Ici hn3 hB)
      have hcomp : (d.mu : Measure ℝ≥0) ((Ici (B : ℝ≥0))ᶜ) = 0 :=
        (prob_compl_eq_zero_iff (μ := (d.mu : Measure ℝ≥0)) measurableSet_Ici).2 hsupport'
      exact measure_mono_null (by
        intro x hx
        simp only [mem_Iic, mem_compl_iff, mem_Ici]
        exact fun hBx ↦ (not_le_of_gt hqB) (hBx.trans hx)) hcomp
    unfold ServiceLevelFeasible at hfeas
    have hcdfzero : (cdf d.mu (rule (momentSequence d.mu)) : ℝ≥0∞) = 0 := by
      simpa [cdf, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hnull
    rw [hcdfzero] at hfeas
    exact (not_lt_of_ge hfeas) (ENNReal.ofReal_pos.mpr hbetaPos)
  · intro q hq
    by_contra hnot
    have hq1 : q < (1 : ℝ≥0) := lt_of_not_ge hnot
    have hnull : (d.nu : Measure ℝ≥0) (Iic q) = 0 := by
      have hsupport' : (d.nu : Measure ℝ≥0) (Ici (1 : ℝ≥0)) = 1 := by
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        exact congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hnuSupport
      have hcomp : (d.nu : Measure ℝ≥0) ((Ici (1 : ℝ≥0))ᶜ) = 0 :=
        (prob_compl_eq_zero_iff (μ := (d.nu : Measure ℝ≥0)) measurableSet_Ici).2 hsupport'
      exact measure_mono_null (by
        intro x hx
        simp only [mem_Iic, mem_compl_iff, mem_Ici]
        exact fun h1x ↦ (not_le_of_gt hq1) (h1x.trans hx)) hcomp
    change ServiceLevelFeasible d.nu beta q at hq
    unfold ServiceLevelFeasible at hq
    have hcdfzero : (cdf d.nu q : ℝ≥0∞) = 0 := by
      simpa [cdf, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hnull
    rw [hcdfzero] at hq
    exact (not_lt_of_ge hq) (ENNReal.ofReal_pos.mpr hbetaPos)

/-- `cor:chance-capacity`, `sections/quantile.tex`.  The manuscript leaves `B ≥ 3`
untyped here, so this literal interface quantifies over real `B` and applies the integer
separator at `⌈B⌉`.  The final `IsLeast` clause says that `1` is exactly the
distribution-specific minimum feasible capacity; the preceding real inequality is therefore
the claimed factor-`B` over-capacity, without division. -/
theorem chance_capacity (beta : ℝ) (hbeta0 : (1 : ℝ) / 2 ≤ beta)
    (hbeta1 : beta < 1) (B : ℝ) (hB : 3 ≤ B) :
    ∃ mu nu : Distribution, MomentEquivalent mu nu ∧
      (∀ rule : CapacityRule,
        RobustCapacityFeasible rule (momentSequence mu) beta →
          B ≤ (rule (momentSequence mu) : ℝ)) ∧
      IsLeast {q : ℝ≥0 | ServiceLevelFeasible nu beta q} 1 := by
  let K : ℕ := ⌈B⌉₊
  have hBK : B ≤ (K : ℝ) := by
    simpa [K] using Nat.le_ceil B
  have hK : 3 ≤ K := by
    have : (3 : ℝ) ≤ (K : ℝ) := hB.trans hBK
    exact_mod_cast this
  obtain ⟨mu, nu, hmn, hrules, hleast⟩ :=
    chance_capacity_nat beta hbeta0 hbeta1 K hK
  refine ⟨mu, nu, hmn, ?_, hleast⟩
  intro rule hfeasible
  have hcapNN : (K : ℝ≥0) ≤ rule (momentSequence mu) := hrules rule hfeasible
  have hcapR : (K : ℝ) ≤ (rule (momentSequence mu) : ℝ) := by
    exact_mod_cast hcapNN
  exact hBK.trans hcapR

/-- `cor:chance-capacity`, `sections/quantile.tex`: exact measurable-policy interface inherited
from `def:moment-based-policy`.  It follows from `chance_capacity`, which proves the stronger
claim for every function of the disclosed moment sequence. -/
theorem chance_capacity_measurable (beta : ℝ) (hbeta0 : (1 : ℝ) / 2 ≤ beta)
    (hbeta1 : beta < 1) (B : ℝ) (hB : 3 ≤ B) :
    ∃ mu nu : Distribution, MomentEquivalent mu nu ∧
      (∀ rule : MeasurableCapacityRule,
        RobustCapacityFeasible rule.1 (momentSequence mu) beta →
          B ≤ (rule.1 (momentSequence mu) : ℝ)) ∧
      IsLeast {q : ℝ≥0 | ServiceLevelFeasible nu beta q} 1 := by
  obtain ⟨mu, nu, hmoment, hrules, hleast⟩ :=
    chance_capacity beta hbeta0 hbeta1 B hB
  exact ⟨mu, nu, hmoment, fun rule hfeasible ↦ hrules rule.1 hfeasible, hleast⟩

end

end MomentAmbiguity
