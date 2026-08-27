import MomentAmbiguity.NWaySeparator
import MomentAmbiguity.BinarySeparator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Posted-price revenue

Prices used by randomized rules inhabit the positive-price subtype.  In particular, no
irrelevant first-moment condition is imposed on a pricing rule.  Internal approximation
guarantees are stated multiplicatively; ratio statements are introduced only with a separate
strict-positivity hypothesis on the benchmark.
-/

open scoped ENNReal NNReal BigOperators

namespace MomentAmbiguity

open MeasureTheory Set

noncomputable section

/-- Strictly positive posted prices. -/
abbrev PositivePrice := {v : ℝ≥0 // 0 < v}

/-- Revenue at a deterministic (possibly zero) threshold. -/
def postedRevenue (mu : Distribution) (v : ℝ≥0) : ℝ :=
  (v : ℝ) * (mu (Ici v) : ℝ)

/-- Optimal deterministic posted-price revenue. -/
def optimalPostedRevenue (mu : Distribution) : ℝ :=
  sSup (Set.range (postedRevenue mu))

/-- A randomized pricing rule is a probability law on positive prices. -/
abbrev PricingRule := ProbabilityMeasure PositivePrice

/-- Expected revenue of a randomized pricing rule. -/
def randomizedPostedRevenue (mu : Distribution) (lambda : PricingRule) : ℝ :=
  ∫ v, postedRevenue mu v.1 ∂(lambda : Measure PositivePrice)

theorem postedRevenue_nonneg (mu : Distribution) (v : ℝ≥0) :
    0 ≤ postedRevenue mu v := by
  exact mul_nonneg (by positivity) (by positivity)

/-- Tail probabilities are antitone and hence Borel measurable. -/
theorem measurable_tailProbability (mu : Distribution) :
    Measurable (fun v : ℝ≥0 ↦ mu (Ici v)) := by
  apply Antitone.measurable
  intro v w hvw
  exact mu.apply_mono (Ici_subset_Ici.2 hvw)

theorem measurable_postedRevenue (mu : Distribution) :
    Measurable (postedRevenue mu) := by
  unfold postedRevenue
  exact measurable_coe_nnreal_real.mul
    (measurable_coe_nnreal_real.comp (measurable_tailProbability mu))

theorem integrable_cast_of_finite_firstMoment {mu : Distribution}
    (hfirst : HasFiniteMoment mu 1) :
    Integrable (fun x : ℝ≥0 ↦ (x : ℝ)) (mu : Measure ℝ≥0) := by
  change Integrable (fun x : ℝ≥0 ↦ (x : ℝ) ^ 1) (mu : Measure ℝ≥0) at hfirst
  simpa only [pow_one] using hfirst

/-- The standard threshold bound `v P[X ≥ v] ≤ E[X]`. -/
theorem postedRevenue_le_firstMoment {mu : Distribution} (hfirst : HasFiniteMoment mu 1)
    (v : ℝ≥0) : postedRevenue mu v ≤ moment mu 1 := by
  have hxint := integrable_cast_of_finite_firstMoment hfirst
  have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ (v : ℝ)) (Ici v) (mu : Measure ℝ≥0) :=
    integrableOn_const
  have hset : (∫ _ in Ici v, (v : ℝ) ∂(mu : Measure ℝ≥0)) ≤
      ∫ x in Ici v, (x : ℝ) ∂(mu : Measure ℝ≥0) := by
    apply integral_mono_ae hconst hxint.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact_mod_cast hx
  have hwhole : (∫ x in Ici v, (x : ℝ) ∂(mu : Measure ℝ≥0)) ≤
      ∫ x, (x : ℝ) ∂(mu : Measure ℝ≥0) := by
    exact integral_mono_measure (Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun _ ↦ by positivity) hxint
  calc
    postedRevenue mu v = ∫ _ in Ici v, (v : ℝ) ∂(mu : Measure ℝ≥0) := by
      simp [postedRevenue, setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in Ici v, (x : ℝ) ∂(mu : Measure ℝ≥0) := hset
    _ ≤ ∫ x, (x : ℝ) ∂(mu : Measure ℝ≥0) := hwhole
    _ = moment mu 1 := by simp [moment, momentIntegrand]

/-- Revenue is integrable under every price lottery when demand has a finite first moment. -/
theorem integrable_randomizedPostedRevenue {mu : Distribution}
    (hfirst : HasFiniteMoment mu 1) (lambda : PricingRule) :
    Integrable (fun v : PositivePrice ↦ postedRevenue mu v.1)
      (lambda : Measure PositivePrice) := by
  apply Integrable.of_bound
    ((measurable_postedRevenue mu).comp measurable_subtype_coe).aestronglyMeasurable
    (moment mu 1)
  filter_upwards [] with v
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (postedRevenue_nonneg mu v.1)]
  exact postedRevenue_le_firstMoment hfirst v.1

/-- Every deterministic revenue is below the supremum benchmark. -/
theorem postedRevenue_le_optimal {mu : Distribution} (hfirst : HasFiniteMoment mu 1)
    (v : ℝ≥0) : postedRevenue mu v ≤ optimalPostedRevenue mu := by
  apply le_csSup
  · refine ⟨moment mu 1, ?_⟩
    rintro y ⟨w, rfl⟩
    exact postedRevenue_le_firstMoment hfirst w
  · exact mem_range_self v

/-- Multiplication-form guarantee, safe even when the benchmark is zero. -/
def PricingGuarantee (alpha : ℝ) (mu : Distribution) (lambda : PricingRule) : Prop :=
  alpha * optimalPostedRevenue mu ≤ randomizedPostedRevenue mu lambda

/-- A ratio bridge is available only after benchmark positivity has been established. -/
theorem pricingGuarantee_iff_ratio {alpha : ℝ} {mu : Distribution} {lambda : PricingRule}
    (hopt : 0 < optimalPostedRevenue mu) :
    PricingGuarantee alpha mu lambda ↔
      alpha ≤ randomizedPostedRevenue mu lambda / optimalPostedRevenue mu := by
  exact (le_div_iff₀ hopt).symm

/-- Zero benchmark regression: the internal guarantee contains no division. -/
example (mu : Distribution) (lambda : PricingRule)
    (hzero : optimalPostedRevenue mu = 0)
    (hrevenue : 0 ≤ randomizedPostedRevenue mu lambda) :
    PricingGuarantee 1 mu lambda := by
  simpa [PricingGuarantee, hzero] using hrevenue

/-! ## Deterministic pricing against the binary separator -/

/-- The threshold-revenue bound before the tail integral is enlarged to the whole first
moment.  This is the first inequality in the last price range of
`thm:revenue-deterministic`. -/
theorem postedRevenue_le_tailFirstMoment {mu : Distribution}
    (hfirst : HasFiniteMoment mu 1) (v : ℝ≥0) :
    postedRevenue mu v ≤
      ∫ x in Ici v, (x : ℝ) ∂(mu : Measure ℝ≥0) := by
  have hxint := integrable_cast_of_finite_firstMoment hfirst
  have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ (v : ℝ)) (Ici v)
      (mu : Measure ℝ≥0) := integrableOn_const
  have hset : (∫ _ in Ici v, (v : ℝ) ∂(mu : Measure ℝ≥0)) ≤
      ∫ x in Ici v, (x : ℝ) ∂(mu : Measure ℝ≥0) := by
    apply integral_mono_ae hconst hxint.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact_mod_cast hx
  calc
    postedRevenue mu v = ∫ _ in Ici v, (v : ℝ) ∂(mu : Measure ℝ≥0) := by
      simp [postedRevenue, setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in Ici v, (x : ℝ) ∂(mu : Measure ℝ≥0) := hset

private theorem binaryNodeNN_injective {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Function.Injective (BinarySeparator.nodeNN n B) := by
  intro i j hij
  apply BinarySeparator.node_injective hn hB
  exact congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hij

/-- The part of the binary support strictly above its first two nodes. -/
private def binaryPricingTailSupport (n B : ℕ) : Set ℝ≥0 :=
  Set.range (fun r : ℕ ↦ BinarySeparator.nodeNN n B (3 + r))

private theorem binaryOddSupport_countable (n B : ℕ) :
    (BinarySeparator.oddSupport n B).Countable := by
  apply (Set.countable_range (BinarySeparator.nodeNN n B)).mono
  rintro x ⟨j, _hj, rfl⟩
  exact mem_range_self j

private theorem binaryMu_ae_oddSupport {n B : ℕ} (d : BinarySeparator.Data n B) :
    ∀ᵐ x ∂(d.mu : Measure ℝ≥0), x ∈ BinarySeparator.oddSupport n B := by
  have hs : MeasurableSet (BinarySeparator.oddSupport n B) :=
    (binaryOddSupport_countable n B).measurableSet
  have hcompl :
      (d.mu : Measure ℝ≥0) (BinarySeparator.oddSupport n B)ᶜ = 0 := by
    rw [measure_compl hs (measure_ne_top _ _), d.mu_support]
    simp
  rw [ae_iff]
  change (d.mu : Measure ℝ≥0) {x | x ∉ BinarySeparator.oddSupport n B} = 0
  have hset : {x | x ∉ BinarySeparator.oddSupport n B} =
      (BinarySeparator.oddSupport n B)ᶜ := by
    ext x
    simp
  rw [hset]
  exact hcompl

private theorem binaryMu_tail_eventually_le {n B : ℕ} (d : BinarySeparator.Data n B)
    (v : ℝ≥0) (hv : (B : ℝ) < v) :
    Ici v ≤ᵐ[(d.mu : Measure ℝ≥0)] binaryPricingTailSupport n B := by
  filter_upwards [binaryMu_ae_oddSupport d] with x hx hxmin
  rcases hx with ⟨j, hjodd, rfl⟩
  rcases hjodd with ⟨k, hk⟩
  have hj3 : 3 ≤ j := by
    by_contra h
    have hjle : j ≤ 2 := by omega
    have hj1 : j = 1 := by omega
    rw [hj1, BinarySeparator.nodeNN_one] at hxmin
    have hvle : (v : ℝ) ≤ B := by
      exact_mod_cast hxmin
    linarith
  refine ⟨j - 3, ?_⟩
  exact congrArg (BinarySeparator.nodeNN n B) (Nat.add_sub_of_le hj3)

private theorem binaryMu_atomReal_le_weight {n B : ℕ}
    (d : BinarySeparator.Data n B) (j : ℕ) :
    (d.mu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B j} ≤
      |d.weights j| / d.normalizer := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [measureReal_def, d.mu_atom_even j hj]
    exact div_nonneg (abs_nonneg _) d.normalizer_pos.le
  · rw [measureReal_def, d.mu_atom_odd j hj]

private theorem binaryMu_tailIntegral_eq_tsum {n B : ℕ}
    (d : BinarySeparator.Data n B) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∫ x in binaryPricingTailSupport n B, (x : ℝ) ∂(d.mu : Measure ℝ≥0)) =
      ∑' r : ℕ,
        (d.mu : Measure ℝ≥0).real
            {BinarySeparator.nodeNN n B (3 + r)} *
          BinarySeparator.node n B (3 + r) := by
  let x : ℕ → ℝ≥0 := fun r ↦ BinarySeparator.nodeNN n B (3 + r)
  have hxinj : Function.Injective x :=
    (binaryNodeNN_injective hn hB).comp (fun _ _ h ↦ Nat.add_left_cancel h)
  have hdisj : Pairwise (Function.onFun Disjoint fun r : ℕ ↦ ({x r} : Set ℝ≥0)) := by
    intro i j hij
    exact Set.disjoint_singleton.mpr (hxinj.ne hij)
  have hint : Integrable (fun z : ℝ≥0 ↦ (z : ℝ)) (d.mu : Measure ℝ≥0) :=
    integrable_cast_of_finite_firstMoment (d.momentEquivalent.left_finite 1)
  rw [binaryPricingTailSupport, Set.range_eq_iUnion]
  rw [integral_iUnion (fun _ ↦ measurableSet_singleton _) hdisj hint.integrableOn]
  apply tsum_congr
  intro r
  rw [integral_singleton]
  simp only [smul_eq_mul]
  rfl

private theorem summable_binary_inv_tail {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (fun r : ℕ ↦ 1 / BinarySeparator.node n B (3 + r)) := by
  simpa [add_comm] using
    (summable_nat_add_iff 3).2 (BinarySeparator.summable_inv_node hn hB)

private theorem tsum_binary_inv_tail_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∑' r : ℕ, 1 / BinarySeparator.node n B (3 + r)) ≤
      2 / BinarySeparator.node n B 3 := by
  apply Real.tsum_le_of_sum_range_le
  · intro r
    exact one_div_nonneg.mpr (BinarySeparator.node_pos hn hB _).le
  · intro t
    simpa [add_comm] using BinarySeparator.sum_inv_node_tail_le hn hB (q := 3) (t := t)
      (by omega)

/-- The manuscript's explicit binary-tail revenue estimate
`Rev_mu(v) ≤ 16 n B² / x₃` for every `v>B`. -/
theorem binaryMu_postedRevenue_tail_le {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 3 ≤ n) (hB : 3 ≤ B) (v : ℝ≥0) (hv : (B : ℝ) < v) :
    postedRevenue d.mu v ≤
      16 * (n : ℝ) * (B : ℝ) ^ 2 / BinarySeparator.node n B 3 := by
  have hfirst := d.momentEquivalent.left_finite 1
  have hint := integrable_cast_of_finite_firstMoment hfirst
  have hmeasure :
      (d.mu : Measure ℝ≥0).restrict (Ici v) ≤
        (d.mu : Measure ℝ≥0).restrict (binaryPricingTailSupport n B) :=
    MeasureTheory.Measure.restrict_mono_ae (binaryMu_tail_eventually_le d v hv)
  have hintegral :
      (∫ x in Ici v, (x : ℝ) ∂(d.mu : Measure ℝ≥0)) ≤
        ∫ x in binaryPricingTailSupport n B, (x : ℝ) ∂(d.mu : Measure ℝ≥0) :=
    integral_mono_measure hmeasure
      (Filter.Eventually.of_forall fun x ↦ by positivity) hint.integrableOn
  have hterm : ∀ r : ℕ,
      (d.mu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B (3 + r)} *
          BinarySeparator.node n B (3 + r) ≤
        (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
          (1 / BinarySeparator.node n B (3 + r)) := by
    intro r
    let j := 3 + r
    have hx : 0 < BinarySeparator.node n B j := BinarySeparator.node_pos hn hB j
    have hatom := binaryMu_atomReal_le_weight d j
    have hweight := d.weight_decay_two j
    calc
      (d.mu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B j} *
            BinarySeparator.node n B j ≤
          (|d.weights j| / d.normalizer) * BinarySeparator.node n B j :=
        mul_le_mul_of_nonneg_right hatom hx.le
      _ ≤ ((8 * (n * B : ℝ) ^ 2 / BinarySeparator.node n B j ^ 2) /
            d.normalizer) * BinarySeparator.node n B j := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hweight d.normalizer_pos.le) hx.le
      _ = (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
            (1 / BinarySeparator.node n B j) := by
        field_simp [ne_of_gt hx, ne_of_gt d.normalizer_pos]
        <;> ring
  have hsumTerms : Summable (fun r : ℕ ↦
      (d.mu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B (3 + r)} *
        BinarySeparator.node n B (3 + r)) := by
    apply Summable.of_nonneg_of_le
      (fun r ↦ mul_nonneg measureReal_nonneg (BinarySeparator.node_pos hn hB _).le)
      hterm
    exact (summable_binary_inv_tail hn hB).mul_left _
  have htsum :
      (∑' r : ℕ,
          (d.mu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B (3 + r)} *
            BinarySeparator.node n B (3 + r)) ≤
        (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
          (2 / BinarySeparator.node n B 3) := by
    calc
      _ ≤ ∑' r : ℕ, (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
            (1 / BinarySeparator.node n B (3 + r)) :=
        hsumTerms.tsum_le_tsum hterm ((summable_binary_inv_tail hn hB).mul_left _)
      _ = (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
            ∑' r : ℕ, 1 / BinarySeparator.node n B (3 + r) := by
        rw [tsum_mul_left]
      _ ≤ (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
            (2 / BinarySeparator.node n B 3) := by
        exact mul_le_mul_of_nonneg_left (tsum_binary_inv_tail_le hn hB)
          (div_nonneg (by positivity) d.normalizer_pos.le)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx3 : 0 < BinarySeparator.node n B 3 := BinarySeparator.node_pos hn hB 3
  calc
    postedRevenue d.mu v ≤ ∫ x in Ici v, (x : ℝ) ∂(d.mu : Measure ℝ≥0) :=
      postedRevenue_le_tailFirstMoment hfirst v
    _ ≤ ∫ x in binaryPricingTailSupport n B, (x : ℝ) ∂(d.mu : Measure ℝ≥0) :=
      hintegral
    _ = ∑' r : ℕ,
          (d.mu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B (3 + r)} *
            BinarySeparator.node n B (3 + r) := binaryMu_tailIntegral_eq_tsum d hn hB
    _ ≤ (8 * (n * B : ℝ) ^ 2 / d.normalizer) *
          (2 / BinarySeparator.node n B 3) := htsum
    _ ≤ (8 * (n * B : ℝ) ^ 2 / n) *
          (2 / BinarySeparator.node n B 3) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hnpos d.normalizer_ge)
        (div_nonneg (by norm_num) hx3.le)
    _ = 16 * (n : ℝ) * (B : ℝ) ^ 2 / BinarySeparator.node n B 3 := by
      field_simp [ne_of_gt hnpos, ne_of_gt hx3]
      <;> ring

private theorem binaryMu_tail_le_four {n B : ℕ} (hn : 2 * B ≤ n) (hB : 3 ≤ B) :
    16 * (n : ℝ) * (B : ℝ) ^ 2 / BinarySeparator.node n B 3 ≤ 4 := by
  have hn3 : 3 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hBOne : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hbase : (1 : ℝ) ≤ n * B := by
    have hnat : 1 * 1 ≤ n * B := Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast hnat
  have hpow : (n * B : ℝ) ^ 3 ≤ (n * B : ℝ) ^ B :=
    pow_le_pow_right₀ hbase hB
  have hden : (0 : ℝ) < (n * B : ℝ) ^ 3 := by positivity
  have hfirst :
      16 * (n : ℝ) * (B : ℝ) ^ 2 / BinarySeparator.node n B 3 ≤
        16 * (n : ℝ) * (B : ℝ) ^ 2 / (n * B : ℝ) ^ 3 := by
    rw [BinarySeparator.node_three]
    exact div_le_div_of_nonneg_left (by positivity) hden hpow
  have hrewrite :
      16 * (n : ℝ) * (B : ℝ) ^ 2 / (n * B : ℝ) ^ 3 =
        16 / ((n : ℝ) ^ 2 * B) := by
    field_simp [ne_of_gt hnpos, ne_of_gt hBpos]
    <;> ring
  have hden4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 * B := by
    have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hnSq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
    simpa using mul_le_mul hnSq hBOne (by norm_num) (by positivity)
  calc
    _ ≤ 16 * (n : ℝ) * (B : ℝ) ^ 2 / (n * B : ℝ) ^ 3 := hfirst
    _ = 16 / ((n : ℝ) ^ 2 * B) := hrewrite
    _ ≤ 4 := (div_le_iff₀ (mul_pos (sq_pos_of_pos hnpos) hBpos)).2 (by nlinarith)

private theorem binaryMu_support_Ici_B {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (d.mu : Measure ℝ≥0) (Ici (B : ℝ≥0)) = 1 := by
  have hsubset : BinarySeparator.oddSupport n B ⊆ Ici (B : ℝ≥0) := by
    rintro x ⟨j, hj, rfl⟩
    rcases hj with ⟨k, hk⟩
    have hj1 : 1 ≤ j := by omega
    exact_mod_cast (BinarySeparator.node_strictMono hn hB).monotone hj1
  apply le_antisymm prob_le_one
  simpa only [d.mu_support] using
    measure_mono (μ := (d.mu : Measure ℝ≥0)) hsubset

private theorem binaryMu_optimal_ge_B {n B : ℕ} (d : BinarySeparator.Data n B)
    (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (B : ℝ) ≤ optimalPostedRevenue d.mu := by
  calc
    (B : ℝ) = postedRevenue d.mu (B : ℝ≥0) := by
      unfold postedRevenue
      change (B : ℝ) = (B : ℝ) * (d.mu : Measure ℝ≥0).real (Ici (B : ℝ≥0))
      have hs : (d.mu : Measure ℝ≥0).real (Ici (B : ℝ≥0)) = 1 := by
        rw [measureReal_def, binaryMu_support_Ici_B d hn hB]
        norm_num
      rw [hs]
      ring
    _ ≤ optimalPostedRevenue d.mu :=
      postedRevenue_le_optimal (d.momentEquivalent.left_finite 1) _

private theorem binaryNu_optimal_ge_quarter_B {n B : ℕ}
    (d : BinarySeparator.Data n B) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (B : ℝ) / 4 ≤ optimalPostedRevenue d.nu := by
  let x2 := BinarySeparator.nodeNN n B 2
  have hmono :
      (d.nu : Measure ℝ≥0).real {x2} ≤ (d.nu : Measure ℝ≥0).real (Ici x2) := by
    exact measureReal_mono (singleton_subset_iff.mpr left_mem_Ici) (measure_ne_top _ _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx2 : (x2 : ℝ) = (n : ℝ) * B := by
    simp [x2, BinarySeparator.nodeNN_add_two]
  have hp2 : 1 / (4 * (n : ℝ)) ≤ (d.nu : Measure ℝ≥0).real {x2} := by
    rw [measureReal_def]
    simpa [x2] using d.p2_ge
  calc
    (B : ℝ) / 4 = ((n : ℝ) * B) * (1 / (4 * (n : ℝ))) := by
      field_simp [ne_of_gt hnpos]
      <;> ring
    _ ≤ ((n : ℝ) * B) * (d.nu : Measure ℝ≥0).real {x2} := by
      exact mul_le_mul_of_nonneg_left hp2 (by positivity)
    _ ≤ ((n : ℝ) * B) * (d.nu : Measure ℝ≥0).real (Ici x2) := by
      gcongr
    _ = postedRevenue d.nu x2 := by
      unfold postedRevenue
      change ((n : ℝ) * B) * (d.nu : Measure ℝ≥0).real (Ici x2) =
        (x2 : ℝ) * (d.nu : Measure ℝ≥0).real (Ici x2)
      rw [hx2]
    _ ≤ optimalPostedRevenue d.nu :=
      postedRevenue_le_optimal (d.momentEquivalent.right_finite 1) _

private theorem binaryNu_tailReal_le_two_div_n {n B : ℕ}
    (d : BinarySeparator.Data n B) (hn : 3 ≤ n) (v : ℝ≥0)
    (hv : (1 : ℝ) < v) :
    (d.nu : Measure ℝ≥0).real (Ici v) ≤ 2 / (n : ℝ) := by
  have hsubset : Ici v ⊆ ({BinarySeparator.nodeNN n B 0} : Set ℝ≥0)ᶜ := by
    intro x hx hxeq
    have : x = 1 := by simpa using hxeq
    subst x
    exact (not_le_of_gt hv) (by exact_mod_cast hx)
  have htail :
      (d.nu : Measure ℝ≥0).real (Ici v) ≤
        (d.nu : Measure ℝ≥0).real ({BinarySeparator.nodeNN n B 0} : Set ℝ≥0)ᶜ :=
    measureReal_mono hsubset (measure_ne_top _ _)
  have hcompl := measureReal_add_measureReal_compl
    (μ := (d.nu : Measure ℝ≥0))
    (MeasurableSet.singleton (BinarySeparator.nodeNN n B 0))
  simp only [measureReal_univ_eq_one] at hcompl
  have hp0 : 1 - 2 / (n : ℝ) ≤
      (d.nu : Measure ℝ≥0).real {BinarySeparator.nodeNN n B 0} := by
    rw [measureReal_def]
    exact d.p0_ge
  linarith

private theorem manuscript_binary_parameters {n B : ℕ} {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hB : ⌈4 / epsilon⌉₊ + 1 ≤ B) (hn : 2 * B ≤ n) :
    3 ≤ B ∧ 3 ≤ n ∧ 4 < epsilon * B := by
  have hfourDivPos : 0 ≤ 4 / epsilon := (div_pos (by norm_num) hepsilon0).le
  have hceil : 4 / epsilon ≤ (⌈4 / epsilon⌉₊ : ℝ) := Nat.le_ceil _
  have hceilB : ((⌈4 / epsilon⌉₊ + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast hB
  have hBstrict : 4 / epsilon < (B : ℝ) := by
    calc
      4 / epsilon ≤ (⌈4 / epsilon⌉₊ : ℝ) := hceil
      _ < ((⌈4 / epsilon⌉₊ + 1 : ℕ) : ℝ) := by norm_num
      _ ≤ B := hceilB
  have hfour : (4 : ℝ) < epsilon * B := by
    apply (div_lt_iff₀ hepsilon0).mp at hBstrict
    nlinarith
  have hBnat : 3 ≤ B := by
    have : (4 : ℝ) < B := by
      have : (4 : ℝ) < 4 / epsilon := by
        apply (lt_div_iff₀ hepsilon0).2
        nlinarith
      exact this.trans hBstrict
    exact_mod_cast (show (3 : ℝ) ≤ B by linarith)
  exact ⟨hBnat, by omega, hfour⟩

/-- Division-free form of `thm:revenue-deterministic`, for the canonical binary-separator
interface.  It is safe even before benchmark positivity is known. -/
theorem revenue_deterministic_universal {n B : ℕ} (d : BinarySeparator.Data n B)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hB : ⌈4 / epsilon⌉₊ + 1 ≤ B) (hn : 2 * B ≤ n)
    (v : PositivePrice) :
    postedRevenue d.mu v.1 < epsilon * optimalPostedRevenue d.mu ∨
      postedRevenue d.nu v.1 < epsilon * optimalPostedRevenue d.nu := by
  obtain ⟨hB3, hn3, hfour⟩ :=
    manuscript_binary_parameters hepsilon0 hepsilon1 hB hn
  have hmuOpt := binaryMu_optimal_ge_B d hn3 hB3
  have hnuOpt := binaryNu_optimal_ge_quarter_B d hn3 hB3
  have hepsilonNonneg := hepsilon0.le
  by_cases hv1 : (v.1 : ℝ) ≤ 1
  · right
    have hrev : postedRevenue d.nu v.1 ≤ 1 := by
      calc
        postedRevenue d.nu v.1 ≤ (v.1 : ℝ) * 1 := by
          rw [postedRevenue]
          gcongr
          exact measureReal_le_one
        _ ≤ 1 := by simpa using hv1
    calc
      postedRevenue d.nu v.1 ≤ 1 := hrev
      _ < epsilon * ((B : ℝ) / 4) := by nlinarith
      _ ≤ epsilon * optimalPostedRevenue d.nu := by gcongr
  · have hv1' : (1 : ℝ) < v.1 := lt_of_not_ge hv1
    by_cases hvB : (v.1 : ℝ) ≤ B
    · right
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have htail := binaryNu_tailReal_le_two_div_n d hn3 v.1 hv1'
      have hrev : postedRevenue d.nu v.1 ≤ 1 := by
        calc
          postedRevenue d.nu v.1 ≤ (B : ℝ) * (2 / (n : ℝ)) := by
            rw [postedRevenue]
            exact mul_le_mul hvB htail measureReal_nonneg (by positivity)
          _ = (2 * (B : ℝ)) / n := by ring
          _ ≤ 1 := (div_le_iff₀ hnpos).2 (by
            have hnreal : (2 : ℝ) * B ≤ n := by exact_mod_cast hn
            nlinarith)
      calc
        postedRevenue d.nu v.1 ≤ 1 := hrev
        _ < epsilon * ((B : ℝ) / 4) := by nlinarith
        _ ≤ epsilon * optimalPostedRevenue d.nu := by gcongr
    · left
      have hvB' : (B : ℝ) < v.1 := lt_of_not_ge hvB
      calc
        postedRevenue d.mu v.1 ≤
            16 * (n : ℝ) * (B : ℝ) ^ 2 / BinarySeparator.node n B 3 :=
          binaryMu_postedRevenue_tail_le d hn3 hB3 v.1 hvB'
        _ ≤ 4 := binaryMu_tail_le_four hn hB3
        _ < epsilon * (B : ℝ) := hfour
        _ ≤ epsilon * optimalPostedRevenue d.mu := by gcongr

/-- Generic form of `thm:revenue-deterministic`, specialized to an arbitrary witness of the
canonical binary-separator interface.

The result records moment equivalence and quantifies over every strictly positive deterministic
price.  The displayed ratios are introduced only after the proof has established that both
optimal revenues are positive. -/
theorem revenue_deterministic_of_data {n B : ℕ} (d : BinarySeparator.Data n B)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hB : ⌈4 / epsilon⌉₊ + 1 ≤ B) (hn : 2 * B ≤ n) :
    MomentEquivalent d.mu d.nu ∧
      ∀ v : PositivePrice,
        min (postedRevenue d.mu v.1 / optimalPostedRevenue d.mu)
            (postedRevenue d.nu v.1 / optimalPostedRevenue d.nu) < epsilon := by
  obtain ⟨hB3, hn3, _hfour⟩ :=
    manuscript_binary_parameters hepsilon0 hepsilon1 hB hn
  have hmuOpt : 0 < optimalPostedRevenue d.mu :=
    lt_of_lt_of_le (by exact_mod_cast (show 0 < B by omega))
      (binaryMu_optimal_ge_B d hn3 hB3)
  have hnuOpt : 0 < optimalPostedRevenue d.nu :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast (show 0 < B by omega)) (by norm_num))
      (binaryNu_optimal_ge_quarter_B d hn3 hB3)
  refine ⟨d.momentEquivalent, fun v ↦ ?_⟩
  rcases revenue_deterministic_universal d epsilon hepsilon0 hepsilon1 hB hn v with
    hmu | hnu
  · exact min_lt_iff.mpr (Or.inl ((div_lt_iff₀ hmuOpt).2 hmu))
  · exact min_lt_iff.mpr (Or.inr ((div_lt_iff₀ hnuOpt).2 hnu))

/-- `thm:revenue-deterministic`, `sections/revenue.tex`, lines 7--40.

For every `epsilon ∈ (0,1)`, the concrete binary construction supplies two
moment-equivalent laws for which every positive deterministic price has relative revenue less
than `epsilon` on at least one law. -/
theorem revenue_deterministic (epsilon : ℝ) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < 1) :
    ∃ mu nu : Distribution,
      MomentEquivalent mu nu ∧
        ∀ v : PositivePrice,
          min (postedRevenue mu v.1 / optimalPostedRevenue mu)
              (postedRevenue nu v.1 / optimalPostedRevenue nu) < epsilon := by
  let B : ℕ := ⌈4 / epsilon⌉₊ + 1
  let n : ℕ := 2 * B
  have hparams := manuscript_binary_parameters (n := n) (B := B)
    hepsilon0 hepsilon1 (by simp [B]) (by simp [n])
  let d : BinarySeparator.Data n B :=
    BinarySeparator.binarySeparator n B hparams.2.1 hparams.1
  exact ⟨d.mu, d.nu,
    revenue_deterministic_of_data d epsilon hepsilon0 hepsilon1 (by simp [B]) (by simp [n])⟩

/-! ## The localization-series constant -/

/-- The nonnegative summand in the manuscript's definition of `C_N`.  Integer powers are
essential here because `2j-e(j)-(N-2)` is negative on the tail. -/
def pricingSeriesTerm (N j : ℕ) : ℝ :=
  (2 : ℝ) ^ ((2 * (j : ℤ)) - (nwayExponent N j : ℤ) - ((N - 2 : ℕ) : ℤ))

theorem pricingSeriesTerm_pos (N j : ℕ) : 0 < pricingSeriesTerm N j := by
  exact zpow_pos (by norm_num) _

/-- The special exponent block `{N-1,…,2N-2}`. -/
def pricingSpecialBlock (N : ℕ) : Set ℕ := Set.Icc (N - 1) (2 * N - 2)

local instance pricingSpecialBlockMembershipDecidable (N : ℕ) :
    DecidablePred (· ∈ pricingSpecialBlock N) := Classical.decPred _

/-- The manuscript constant `C_N`; nonspecial exponents are retained by an indicator. -/
noncomputable def pricingCNIntegrand (N j : ℕ) : ℝ :=
  by
    classical
    exact if j ∈ pricingSpecialBlock N then 0 else pricingSeriesTerm N j

def pricingCN (N : ℕ) : ℝ := ∑' j : ℕ, pricingCNIntegrand N j

private theorem nway_level_block {N L b : ℕ} (hN : 2 ≤ N) (hb : b < N - 1) :
    nwayLevel N ((N - 1) * L + b) = L := by
  simp only [nwayLevel]
  rw [Nat.mul_add_div (by omega)]
  simp [Nat.div_eq_of_lt hb]

private theorem nway_remainder_block {N L b : ℕ} (hN : 2 ≤ N) (hb : b < N - 1) :
    nwayRemainder N ((N - 1) * L + b) = b := by
  simp only [nwayRemainder]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hb

private theorem nway_exponent_block {N L b : ℕ} (hN : 2 ≤ N) (hb : b < N - 1) :
    nwayExponent N ((N - 1) * L + b) =
      (N - 1) * (L * (L - 1) / 2) + L * b := by
  simp [nwayExponent, nway_level_block hN hb, nway_remainder_block hN hb]

private theorem triangular_succ (L : ℕ) :
    (L + 1) * ((L + 1) - 1) / 2 = L * (L - 1) / 2 + L := by
  rw [← Nat.choose_two_right (L + 1), ← Nat.choose_two_right L,
    Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

/-- Reindexing `j=L(N-1)+b` gives the exact manuscript block exponent. -/
theorem pricingSeriesTerm_block {N L b : ℕ} (hN : 2 ≤ N) (hb : b < N - 1) :
    pricingSeriesTerm N ((N - 1) * L + b) =
      (2 : ℝ) ^
    ((2 : ℤ) * (((N - 1) * L + b : ℕ) : ℤ) -
          (((N - 1) * (L * (L - 1) / 2) + L * b : ℕ) : ℤ) -
          ((N - 2 : ℕ) : ℤ)) := by
  rw [pricingSeriesTerm, nway_exponent_block hN hb]

private theorem pricing_block_exponent_succ_sub
    {N L b : ℕ} (hN : 2 ≤ N) (hb : b < N - 1) :
    ((2 : ℤ) * (((N - 1) * (L + 1) + b : ℕ) : ℤ) -
        (((N - 1) * ((L + 1) * ((L + 1) - 1) / 2) + (L + 1) * b : ℕ) : ℤ) -
        ((N - 2 : ℕ) : ℤ)) -
      ((2 : ℤ) * (((N - 1) * L + b : ℕ) : ℤ) -
        (((N - 1) * (L * (L - 1) / 2) + L * b : ℕ) : ℤ) -
        ((N - 2 : ℕ) : ℤ)) =
      ((N - 1 : ℕ) : ℤ) * (2 - (L : ℤ)) - (b : ℤ) := by
  rw [triangular_succ]
  push_cast
  ring

private theorem pricingSeriesTerm_block_ratio {N L b : ℕ} (hN : 2 ≤ N)
    (hb : b < N - 1) (hL : 7 ≤ L) :
    pricingSeriesTerm N ((N - 1) * (L + 1) + b) ≤
      (1 / 32 : ℝ) * pricingSeriesTerm N ((N - 1) * L + b) := by
  rw [pricingSeriesTerm_block hN hb, pricingSeriesTerm_block hN hb]
  let E : ℕ → ℤ := fun K ↦
    (2 : ℤ) * (((N - 1) * K + b : ℕ) : ℤ) -
      (((N - 1) * (K * (K - 1) / 2) + K * b : ℕ) : ℤ) -
      ((N - 2 : ℕ) : ℤ)
  change (2 : ℝ) ^ E (L + 1) ≤ (1 / 32 : ℝ) * (2 : ℝ) ^ E L
  have hdiff : E (L + 1) - E L ≤ (-5 : ℤ) := by
    rw [show E (L + 1) - E L =
      ((N - 1 : ℕ) : ℤ) * (2 - (L : ℤ)) - (b : ℤ) from
        pricing_block_exponent_succ_sub hN hb]
    have hd : (1 : ℤ) ≤ (N - 1 : ℕ) := by omega
    have hb0 : (0 : ℤ) ≤ b := by omega
    nlinarith
  have hz := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hdiff
  have hEL : 0 < (2 : ℝ) ^ E L := zpow_pos (by norm_num) _
  calc
    (2 : ℝ) ^ E (L + 1) = ((2 : ℝ) ^ (E (L + 1) - E L)) * (2 : ℝ) ^ E L := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (-5 : ℤ) * (2 : ℝ) ^ E L :=
      mul_le_mul_of_nonneg_right hz hEL.le
    _ = (1 / 32 : ℝ) * (2 : ℝ) ^ E L := by norm_num

/-- The geometric block tail proves `C_N < ∞` in the substantive sense: its defining
nonnegative real series is summable.  This is the manuscript's `j=L(N-1)+b`, `L≥7` proof. -/
theorem summable_pricingSeriesTerm (N : ℕ) (hN : 2 ≤ N) :
    Summable (pricingSeriesTerm N) := by
  let d := N - 1
  letI : NeZero d := ⟨by simp [d]; omega⟩
  let e : ℕ ≃ ℕ × Fin d := Nat.divModEquiv d
  have hfiber : ∀ b : Fin d,
      Summable (fun L : ℕ ↦ pricingSeriesTerm N (d * L + b)) := by
    intro b
    apply summable_of_ratio_norm_eventually_le (r := (1 / 32 : ℝ)) (by norm_num)
    rw [Filter.eventually_atTop]
    refine ⟨7, fun L hL ↦ ?_⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (pricingSeriesTerm_pos N _), abs_of_pos (pricingSeriesTerm_pos N _)]
    simpa [d] using pricingSeriesTerm_block_ratio hN b.isLt hL
  have hprod : Summable (fun p : ℕ × Fin d ↦
      pricingSeriesTerm N (d * p.1 + p.2)) := by
    apply (summable_prod_of_nonneg (fun p ↦ (pricingSeriesTerm_pos N _).le)).2
    constructor
    · intro L
      exact summable_of_finite_support (Set.toFinite _)
    · have hsum : Summable (fun L : ℕ ↦
          ∑ b : Fin d, pricingSeriesTerm N (d * L + b)) := by
          exact summable_sum (s := Finset.univ)
            (f := fun (b : Fin d) (L : ℕ) ↦ pricingSeriesTerm N (d * L + b))
            (fun b hb ↦ hfiber b)
      simpa only [tsum_fintype] using hsum
  apply (e.symm.summable_iff).mp
  simpa [e, d, Function.comp_def, Nat.divModEquiv, mul_comm] using hprod

theorem summable_pricingCN (N : ℕ) (hN : 2 ≤ N) :
    Summable (pricingCNIntegrand N) := by
  classical
  exact (summable_pricingSeriesTerm N hN).of_norm_bounded
    (fun j ↦ by
      simp only [pricingCNIntegrand]
      split
      · simpa using (pricingSeriesTerm_pos N j).le
      · rw [Real.norm_eq_abs, abs_of_pos (pricingSeriesTerm_pos N j)])

theorem pricingCN_nonneg (N : ℕ) : 0 ≤ pricingCN N := by
  classical
  rw [pricingCN]
  apply tsum_nonneg
  intro j
  simp only [pricingCNIntegrand]
  split
  · exact le_rfl
  · exact (pricingSeriesTerm_pos N j).le

/-! ## Revenue localization for the concrete `N`-way separator -/

/-- The unique exponent in `{N-1,…,2N-2}` congruent to `h` modulo `N`. -/
def pricingSpecialIndex (N : ℕ) (h : Fin N) : ℕ :=
  if h.val = N - 1 then N - 1 else N + h.val

theorem pricingSpecialIndex_bounds {N : ℕ} (hN : 2 ≤ N) (h : Fin N) :
    N - 1 ≤ pricingSpecialIndex N h ∧ pricingSpecialIndex N h ≤ 2 * N - 2 := by
  unfold pricingSpecialIndex
  split_ifs with hh
  · omega
  · have hh' : h.val ≤ N - 2 := by omega
    omega

theorem pricingSpecialIndex_mod {N : ℕ} (hN : 2 ≤ N) (h : Fin N) :
    pricingSpecialIndex N h % N = h.val := by
  unfold pricingSpecialIndex
  split_ifs with hh
  · rw [hh, Nat.mod_eq_of_lt]
    omega
  · have hh' : h.val < N - 1 := by omega
    simp only [Nat.add_mod, Nat.mod_self, zero_add]
    simp [Nat.mod_eq_of_lt h.isLt]

theorem pricingSpecialIndex_injective {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (pricingSpecialIndex N) := by
  intro h h' heq
  apply Fin.ext
  rw [← pricingSpecialIndex_mod hN h, ← pricingSpecialIndex_mod hN h', heq]

theorem pricingSpecialIndex_exponent_gap {N : ℕ} (hN : 2 ≤ N) (h : Fin N) :
    (pricingSpecialIndex N h : ℤ) - nwayExponent N (pricingSpecialIndex N h) =
      (N - 1 : ℕ) := by
  exact (nway_index_sub_exponent_eq_iff N (pricingSpecialIndex N h) hN).2
    (pricingSpecialIndex_bounds hN h)

theorem pricingSpecialIndex_mem_block {N : ℕ} (hN : 2 ≤ N) (h : Fin N) :
    pricingSpecialIndex N h ∈ pricingSpecialBlock N :=
  pricingSpecialIndex_bounds hN h

/-- Uniqueness of the representative of residue `h` in the special exponent block. -/
theorem eq_pricingSpecialIndex_of_mem_block_of_mod {N j : ℕ} (hN : 2 ≤ N)
    (h : Fin N) (hj : j ∈ pricingSpecialBlock N) (hmod : j % N = h.val) :
    j = pricingSpecialIndex N h := by
  rcases hj with ⟨hjlo, hjhi⟩
  by_cases hjN : j < N
  · have hjmod : j % N = j := Nat.mod_eq_of_lt hjN
    have hjh : j = h.val := by omega
    have hh : h.val = N - 1 := by omega
    simp [pricingSpecialIndex, hh, hjh]
  · have hNj : N ≤ j := by omega
    have hjsub : j - N < N := by omega
    have hjmod : j % N = j - N := by
      rw [Nat.mod_eq_sub_mod hNj, Nat.mod_eq_of_lt hjsub]
    have hjh : j = N + h.val := by omega
    have hh : h.val ≠ N - 1 := by
      intro heq
      omega
    simp [pricingSpecialIndex, hh, hjh]

/-- The good-price interval `I_h=(B^(n_h-1),B^n_h]`, lifted to positive prices. -/
def pricingGoodInterval (B N : ℕ) (h : Fin N) : Set PositivePrice :=
  (fun v : PositivePrice ↦ v.1) ⁻¹'
    (Ioc (nwayNode B (pricingSpecialIndex N h - 1))
      (nwayNode B (pricingSpecialIndex N h)) : Set ℝ≥0)

theorem measurableSet_pricingGoodInterval (B N : ℕ) (h : Fin N) :
    MeasurableSet (pricingGoodInterval B N h) := by
  exact measurableSet_Ioc.preimage measurable_subtype_coe

private theorem nwayNode_strictMono {B : ℕ} (hB : 2 ≤ B) :
    StrictMono (nwayNode B) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [nwayNode, pow_succ]
  have hx : (0 : ℝ≥0) < (B : ℝ≥0) ^ j := by positivity
  have hBone : (1 : ℝ≥0) < B := by exact_mod_cast (show 1 < B by omega)
  nlinarith

theorem pricingGoodInterval_pairwiseDisjoint {B N : ℕ} (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Pairwise (Function.onFun Disjoint (pricingGoodInterval B N)) := by
  intro h h' hne
  change Disjoint (pricingGoodInterval B N h) (pricingGoodInterval B N h')
  rw [Set.disjoint_left]
  intro v hv hv'
  have hidx : pricingSpecialIndex N h ≠ pricingSpecialIndex N h' :=
    fun heq ↦ hne (pricingSpecialIndex_injective hN heq)
  rcases lt_or_gt_of_ne hidx with hlt | hgt
  · have hstep : pricingSpecialIndex N h ≤ pricingSpecialIndex N h' - 1 := by omega
    have hnodes := (nwayNode_strictMono hB).monotone hstep
    exact (not_lt_of_ge (hv.2.trans hnodes)) hv'.1
  · have hstep : pricingSpecialIndex N h' ≤ pricingSpecialIndex N h - 1 := by omega
    have hnodes := (nwayNode_strictMono hB).monotone hstep
    exact (not_lt_of_ge (hv'.2.trans hnodes)) hv.1

/-- The concrete `N`-way law used in the pricing application. -/
noncomputable def pricingNWayLaw (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) : Distribution :=
  (nwayResidueWeightCertificate B N hB hN).law h

theorem mem_range_nwayExponentEmbedding_iff {N : ℕ} (hN : 1 ≤ N)
    (h : Fin N) (j : ℕ) :
    j ∈ Set.range (nwayExponentEmbedding N h) ↔ j % N = h.val := by
  constructor
  · rintro ⟨m, rfl⟩
    simp [nwayExponentEmbedding, Nat.add_mod, Nat.mod_eq_of_lt h.isLt]
  · intro hj
    refine ⟨j / N, ?_⟩
    rw [nwayExponentEmbedding, ← hj]
    exact Nat.mod_add_div j N

/-- Unfolded real mass formula for the concrete residue certificate. -/
theorem pricingNWayCertificate_mass_toReal (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (j : ℕ) :
    ((nwayResidueWeightCertificate B N hB hN).mass h j).toReal =
      if j % N = h.val then nwayCoeff B N j / nwayNormalizer B N else 0 := by
  classical
  rw [show (nwayResidueWeightCertificate B N hB hN).mass h j =
      nwayMass B N hB hN h j by rfl]
  simp only [nwayMass, nwayMassNN]
  rw [if_congr (mem_range_nwayExponentEmbedding_iff (by omega) h j) rfl rfl]
  split_ifs
  · change nwayCoeff B N j / nwayNormalizer B N = _
    rfl
  · simp

/-- Real atom mass of a concrete `N`-way law. -/
theorem pricingNWayLaw_atomReal (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (j : ℕ) :
    (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real {nwayNode B j} =
      if j % N = h.val then nwayCoeff B N j / nwayNormalizer B N else 0 := by
  let C := nwayResidueWeightCertificate B N hB hN
  have hatom := atomicLaw_toMeasure_singleton_of_injective
    (C.exponentPMF h) (nwayNode B) (by fun_prop) (nwayNode_injective hB) j
  have hreal := congrArg ENNReal.toReal hatom
  change (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real {nwayNode B j} = _
  rw [measureReal_def]
  change ENNReal.toReal
      (((atomicLaw (C.exponentPMF h) (nwayNode B) : ProbabilityMeasure ℝ≥0) :
        Measure ℝ≥0) {nwayNode B j}) = _
  rw [hatom]
  change (C.mass h j).toReal = _
  exact pricingNWayCertificate_mass_toReal B N hB hN h j

/-- Atomic-series formula for posted revenue of a concrete `N`-way law. -/
theorem pricingNWayLaw_postedRevenue_eq_tsum (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (v : ℝ≥0) :
    postedRevenue (pricingNWayLaw B N hB hN h) v =
      ∑' j : ℕ,
        ((nwayResidueWeightCertificate B N hB hN).mass h j).toReal *
          (if v ≤ nwayNode B j then (v : ℝ) else 0) := by
  let C := nwayResidueWeightCertificate B N hB hN
  let f : ℝ≥0 → ℝ := fun x ↦ if v ≤ x then (v : ℝ) else 0
  have hfmeas : StronglyMeasurable f := by
    have hm : Measurable f := by
      change Measurable ((Set.Ici v).indicator (fun _ : ℝ≥0 ↦ (v : ℝ)))
      exact measurable_const.indicator measurableSet_Ici
    exact hm.stronglyMeasurable
  have hcomp : Integrable (f ∘ nwayNode B) (C.exponentPMF h).toMeasure := by
    apply Integrable.of_bound
      (hfmeas.comp_measurable (by fun_prop)).aestronglyMeasurable (v : ℝ)
    filter_upwards [] with j
    dsimp only [Function.comp_apply, f]
    split_ifs <;> simp
  calc
    postedRevenue (pricingNWayLaw B N hB hN h) v =
        ∫ x, f x ∂((C.law h : Distribution) : Measure ℝ≥0) := by
      rw [show f = (Set.Ici v).indicator (fun _ : ℝ≥0 ↦ (v : ℝ)) by
        funext x
        simp [f, Set.indicator, mem_Ici]]
      rw [integral_indicator measurableSet_Ici]
      simp [postedRevenue, pricingNWayLaw, C, smul_eq_mul, mul_comm]
    _ = ∑' j : ℕ, (C.exponentPMF h j).toReal • f (nwayNode B j) :=
      integral_atomicLaw_eq_tsum (C.exponentPMF h) (nwayNode B) f
        (by fun_prop) hfmeas hcomp
    _ = ∑' j : ℕ,
        (C.mass h j).toReal *
          (if v ≤ nwayNode B j then (v : ℝ) else 0) := by
      apply tsum_congr
      intro j
      simp [C, f, smul_eq_mul]

/-- Only the distinguished residue representative can carry mass inside the special block. -/
theorem pricingNWay_specialRevenue_tsum_eq (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (v : ℝ≥0) :
    (∑' j : ℕ, if j ∈ pricingSpecialBlock N then
        ((nwayResidueWeightCertificate B N hB hN).mass h j).toReal *
          (if v ≤ nwayNode B j then (v : ℝ) else 0)
      else 0) =
      ((nwayResidueWeightCertificate B N hB hN).mass h (pricingSpecialIndex N h)).toReal *
        (if v ≤ nwayNode B (pricingSpecialIndex N h) then (v : ℝ) else 0) := by
  classical
  let C := nwayResidueWeightCertificate B N hB hN
  rw [tsum_eq_single (pricingSpecialIndex N h)]
  · rw [if_pos (pricingSpecialIndex_mem_block hN h)]
  · intro j hjne
    by_cases hj : j ∈ pricingSpecialBlock N
    · have hmass : C.mass h j = 0 := by
        by_contra hmass
        have hmod := C.supported h j hmass
        exact hjne (eq_pricingSpecialIndex_of_mem_block_of_mod hN h hj hmod)
      rw [if_pos hj, hmass]
      simp
    · rw [if_neg hj]

private theorem zpow_anti_left_of_nonpos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {k : ℤ} (hk : k ≤ 0) : b ^ k ≤ a ^ k := by
  have hb : 0 < b := ha.trans_le hab
  have hinv : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb ha).2 hab
  have hz := zpow_le_zpow_left₀ (neg_nonneg.mpr hk) (inv_nonneg.mpr hb.le) hinv
  simpa [inv_zpow] using hz

/-- A nonspecial exponent's first-moment contribution is bounded by the corresponding
summand of `C_N`.  The coefficient estimate is supplied explicitly so this lemma isolates the
pricing-specific `B ≥ 2` negative-power comparison. -/
theorem pricingNWay_nonspecialContribution_le (B N j : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N)
    (hj : j ∉ pricingSpecialBlock N)
    (hcoeff : nwayCoeff B N j ≤
      (2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ))) :
    ((nwayResidueWeightCertificate B N hB hN).mass h j).toReal * (B : ℝ) ^ j ≤
      pricingSeriesTerm N j * (B : ℝ) ^ (N - 2) := by
  let C := nwayResidueWeightCertificate B N hB hN
  have hBpos : (0 : ℝ) < B := by positivity
  have hBtwo : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hcoeff0 := nwayCoeff_nonneg B N j hB hN
  have hmass : (C.mass h j).toReal ≤ nwayCoeff B N j := by
    rw [pricingNWayCertificate_mass_toReal B N hB hN h j]
    split_ifs
    · exact div_le_self hcoeff0 (nwayNormalizer_ge_one B N hB hN)
    · exact hcoeff0
  have hgap :
      (j : ℤ) - nwayExponent N j ≤ ((N - 2 : ℕ) : ℤ) := by
    have hle := nway_index_sub_exponent_le N j hN
    have hne : (j : ℤ) - nwayExponent N j ≠ ((N - 1 : ℕ) : ℤ) := by
      intro heq
      exact hj ((nway_index_sub_exponent_eq_iff N j hN).1 heq)
    omega
  let delta : ℤ := (j : ℤ) - nwayExponent N j - ((N - 2 : ℕ) : ℤ)
  have hdelta : delta ≤ 0 := by dsimp [delta]; omega
  have hnegativePower : (B : ℝ) ^ delta ≤ (2 : ℝ) ^ delta :=
    zpow_anti_left_of_nonpos (by norm_num) hBtwo hdelta
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
  have hpowJoin₁ :
      (B : ℝ) ^ (-(nwayExponent N j : ℤ)) * (B : ℝ) ^ (j : ℤ) =
        (B : ℝ) ^ ((j : ℤ) - nwayExponent N j) := by
    rw [← zpow_add₀ hBne]
    congr 1
    ring
  have hpowJoin₂ :
      (B : ℝ) ^ delta * (B : ℝ) ^ ((N - 2 : ℕ) : ℤ) =
        (B : ℝ) ^ ((j : ℤ) - nwayExponent N j) := by
    rw [← zpow_add₀ hBne]
    congr 1
    dsimp [delta]
    ring
  have hpowJoin₃ :
      (2 : ℝ) ^ (j : ℤ) * (2 : ℝ) ^ delta =
        (2 : ℝ) ^ ((2 * (j : ℤ)) - nwayExponent N j - ((N - 2 : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    dsimp [delta]
    ring
  calc
    (C.mass h j).toReal * (B : ℝ) ^ j ≤
        nwayCoeff B N j * (B : ℝ) ^ j :=
      mul_le_mul_of_nonneg_right hmass (pow_nonneg (by positivity) _)
    _ ≤ ((2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ))) *
        (B : ℝ) ^ j :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by positivity) _)
    _ = (2 : ℝ) ^ j * (B : ℝ) ^ ((j : ℤ) - nwayExponent N j) := by
      rw [show (B : ℝ) ^ j = (B : ℝ) ^ (j : ℤ) by simp]
      rw [mul_assoc, hpowJoin₁]
    _ = (2 : ℝ) ^ j *
        ((B : ℝ) ^ delta * (B : ℝ) ^ (N - 2)) := by
      rw [show (B : ℝ) ^ (N - 2) =
        (B : ℝ) ^ ((N - 2 : ℕ) : ℤ) by simp, hpowJoin₂]
    _ ≤ (2 : ℝ) ^ j *
        ((2 : ℝ) ^ delta * (B : ℝ) ^ (N - 2)) := by
      gcongr
    _ = pricingSeriesTerm N j * (B : ℝ) ^ (N - 2) := by
      rw [pricingSeriesTerm]
      rw [show (2 : ℝ) ^ j = (2 : ℝ) ^ (j : ℤ) by simp]
      rw [← mul_assoc, hpowJoin₃]

/-- Summed nonspecial-atom bound used in `lem:N-class-revenue-localization`. -/
theorem pricingNWay_nonspecialContribution_tsum_le (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N)
    (hcoeff : ∀ j : ℕ, nwayCoeff B N j ≤
      (2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ))) :
    (∑' j : ℕ, if j ∈ pricingSpecialBlock N then 0 else
        ((nwayResidueWeightCertificate B N hB hN).mass h j).toReal * (B : ℝ) ^ j) ≤
      pricingCN N * (B : ℝ) ^ (N - 2) := by
  classical
  let C := nwayResidueWeightCertificate B N hB hN
  let f : ℕ → ℝ := fun j ↦
    if j ∈ pricingSpecialBlock N then 0 else
      (C.mass h j).toReal * (B : ℝ) ^ j
  have hfirst : Summable (fun j : ℕ ↦ (C.mass h j).toReal * (B : ℝ) ^ j) := by
    simpa using C.moment_summable h 1
  have hf : Summable f := hfirst.of_norm_bounded (fun j ↦ by
    dsimp only [f]
    by_cases hj : j ∈ pricingSpecialBlock N
    · rw [if_pos hj, norm_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by positivity) _)
    · rw [if_neg hj, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by positivity) _))])
  have hg : Summable (fun j : ℕ ↦
      pricingCNIntegrand N j * (B : ℝ) ^ (N - 2)) :=
    (summable_pricingCN N hN).mul_right _
  have hterm : ∀ j : ℕ, f j ≤ pricingCNIntegrand N j * (B : ℝ) ^ (N - 2) := by
    intro j
    dsimp only [f, pricingCNIntegrand]
    by_cases hj : j ∈ pricingSpecialBlock N
    · simp [hj]
    · simp only [hj, if_false]
      exact pricingNWay_nonspecialContribution_le B N j hB hN h hj (hcoeff j)
  change tsum f ≤ _
  calc
    tsum f ≤ ∑' j : ℕ, pricingCNIntegrand N j * (B : ℝ) ^ (N - 2) :=
      hf.tsum_le_tsum hterm hg
    _ = pricingCN N * (B : ℝ) ^ (N - 2) := by
      rw [tsum_mul_right]
      rfl

/-- Revenue decomposition into the unique special-block atom and the `C_N` tail. -/
theorem pricingNWay_postedRevenue_le_special_add_tail (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N)
    (hcoeff : ∀ j : ℕ, nwayCoeff B N j ≤
      (2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ)))
    (v : ℝ≥0) :
    postedRevenue (pricingNWayLaw B N hB hN h) v ≤
      ((nwayResidueWeightCertificate B N hB hN).mass h
          (pricingSpecialIndex N h)).toReal *
        (if v ≤ nwayNode B (pricingSpecialIndex N h) then (v : ℝ) else 0) +
      pricingCN N * (B : ℝ) ^ (N - 2) := by
  classical
  let C := nwayResidueWeightCertificate B N hB hN
  let r : ℕ → ℝ := fun j ↦
    (C.mass h j).toReal * (if v ≤ nwayNode B j then (v : ℝ) else 0)
  let s : ℕ → ℝ := fun j ↦
    if j ∈ pricingSpecialBlock N then r j else 0
  let g : ℕ → ℝ := fun j ↦
    if j ∈ pricingSpecialBlock N then 0 else
      (C.mass h j).toReal * (B : ℝ) ^ j
  let first : ℕ → ℝ := fun j ↦ (C.mass h j).toReal * (B : ℝ) ^ j
  have hfirst : Summable first := by
    simpa [first] using C.moment_summable h 1
  have hr_nonneg : ∀ j, 0 ≤ r j := by
    intro j
    dsimp only [r]
    split <;> positivity
  have hfirst_nonneg : ∀ j, 0 ≤ first j := by
    intro j
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by positivity) _)
  have hr : Summable r := hfirst.of_norm_bounded (fun j ↦ by
    dsimp only [r, first]
    by_cases hvj : v ≤ nwayNode B j
    · rw [if_pos hvj]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (by positivity))]
      have hvreal' : (v : ℝ) ≤ (nwayNode B j : ℝ) := by exact_mod_cast hvj
      have hvreal : (v : ℝ) ≤ (B : ℝ) ^ j := by simpa [nwayNode] using hvreal'
      exact mul_le_mul_of_nonneg_left hvreal ENNReal.toReal_nonneg
    · rw [if_neg hvj, mul_zero, norm_zero]
      exact hfirst_nonneg j)
  have hs : Summable s := hr.of_norm_bounded (fun j ↦ by
    dsimp only [s]
    by_cases hj : j ∈ pricingSpecialBlock N
    · rw [if_pos hj, Real.norm_eq_abs, abs_of_nonneg (hr_nonneg j)]
    · rw [if_neg hj, norm_zero]
      exact hr_nonneg j)
  have hg : Summable g := hfirst.of_norm_bounded (fun j ↦ by
    dsimp only [g, first]
    by_cases hj : j ∈ pricingSpecialBlock N
    · rw [if_pos hj, norm_zero]
      exact hfirst_nonneg j
    · rw [if_neg hj, Real.norm_eq_abs, abs_of_nonneg (hfirst_nonneg j)])
  have hterm : ∀ j, r j ≤ s j + g j := by
    intro j
    dsimp only [r, s, g]
    by_cases hj : j ∈ pricingSpecialBlock N
    · rw [if_pos hj, if_pos hj]
      simp
    · rw [if_neg hj, if_neg hj, zero_add]
      by_cases hvj : v ≤ nwayNode B j
      · rw [if_pos hvj]
        have hvreal' : (v : ℝ) ≤ (nwayNode B j : ℝ) := by exact_mod_cast hvj
        have hvreal : (v : ℝ) ≤ (B : ℝ) ^ j := by simpa [nwayNode] using hvreal'
        exact mul_le_mul_of_nonneg_left hvreal ENNReal.toReal_nonneg
      · rw [if_neg hvj, mul_zero]
        exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by positivity) _)
  rw [pricingNWayLaw_postedRevenue_eq_tsum B N hB hN h v]
  change tsum r ≤ _
  calc
    tsum r ≤ ∑' j, (s j + g j) := hr.tsum_le_tsum hterm (hs.add hg)
    _ = tsum s + tsum g := hs.tsum_add hg
    _ = ((C.mass h (pricingSpecialIndex N h)).toReal *
          (if v ≤ nwayNode B (pricingSpecialIndex N h) then (v : ℝ) else 0)) +
        tsum g := by
      rw [show tsum s =
          (C.mass h (pricingSpecialIndex N h)).toReal *
            (if v ≤ nwayNode B (pricingSpecialIndex N h) then (v : ℝ) else 0) by
        have heq := pricingNWay_specialRevenue_tsum_eq B N hB hN h v
        change tsum s =
          (C.mass h (pricingSpecialIndex N h)).toReal *
            (if v ≤ nwayNode B (pricingSpecialIndex N h) then (v : ℝ) else 0) at heq
        exact heq]
    _ ≤ ((C.mass h (pricingSpecialIndex N h)).toReal *
          (if v ≤ nwayNode B (pricingSpecialIndex N h) then (v : ℝ) else 0)) +
        pricingCN N * (B : ℝ) ^ (N - 2) := by
      exact add_le_add (le_refl _)
        (by simpa [g, C] using
          pricingNWay_nonspecialContribution_tsum_le B N hB hN h hcoeff)

/-- Outside `I_h`, once the price is above `B^(N-2)`, the distinguished special atom
contributes at most the explicit `2^(2N-2) B^(N-2)` term. -/
theorem pricingNWay_specialRevenue_le (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N)
    (hcoeff : ∀ j : ℕ, nwayCoeff B N j ≤
      (2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ)))
    (v : PositivePrice) (hvout : v ∉ pricingGoodInterval B N h) :
    ((nwayResidueWeightCertificate B N hB hN).mass h
        (pricingSpecialIndex N h)).toReal *
      (if v.1 ≤ nwayNode B (pricingSpecialIndex N h) then (v.1 : ℝ) else 0) ≤
      (2 : ℝ) ^ (2 * N - 2) * (B : ℝ) ^ (N - 2) := by
  let C := nwayResidueWeightCertificate B N hB hN
  let j₀ := pricingSpecialIndex N h
  have hjbounds := pricingSpecialIndex_bounds hN h
  have hjmod := pricingSpecialIndex_mod hN h
  have hmass : (C.mass h j₀).toReal ≤ nwayCoeff B N j₀ := by
    rw [pricingNWayCertificate_mass_toReal B N hB hN h j₀, if_pos hjmod]
    exact div_le_self (nwayCoeff_nonneg B N j₀ hB hN)
      (nwayNormalizer_ge_one B N hB hN)
  by_cases hvbuy : v.1 ≤ nwayNode B j₀
  · rw [if_pos hvbuy]
    have hvlower : (v.1 : ℝ) ≤ (nwayNode B (j₀ - 1) : ℝ) := by
      change ¬((nwayNode B (j₀ - 1) : ℝ≥0) < v.1 ∧
        v.1 ≤ nwayNode B j₀) at hvout
      exact le_of_not_gt (fun hgt ↦ hvout ⟨hgt, hvbuy⟩)
    have hcoeffj := hcoeff j₀
    have hBne : (B : ℝ) ≠ 0 := by positivity
    have hgap := pricingSpecialIndex_exponent_gap hN h
    have hgapPred :
        ((j₀ - 1 : ℕ) : ℤ) - nwayExponent N j₀ = ((N - 2 : ℕ) : ℤ) := by
      dsimp [j₀] at hjbounds hgap ⊢
      omega
    have hpowJoin :
        (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) *
            (B : ℝ) ^ (j₀ - 1) =
          (B : ℝ) ^ (N - 2) := by
      rw [show (B : ℝ) ^ (j₀ - 1) =
        (B : ℝ) ^ ((j₀ - 1 : ℕ) : ℤ) by simp]
      rw [← zpow_add₀ hBne]
      rw [show (-(nwayExponent N j₀ : ℤ) + (j₀ - 1 : ℕ)) =
        ((N - 2 : ℕ) : ℤ) by omega]
      simp
    have htwo : (2 : ℝ) ^ j₀ ≤ (2 : ℝ) ^ (2 * N - 2) := by
      exact pow_le_pow_right₀ (by norm_num) hjbounds.2
    calc
      (C.mass h j₀).toReal * (v.1 : ℝ) ≤
          nwayCoeff B N j₀ * (nwayNode B (j₀ - 1) : ℝ) :=
        mul_le_mul hmass hvlower (by positivity) (nwayCoeff_nonneg B N j₀ hB hN)
      _ ≤ ((2 : ℝ) ^ j₀ *
            (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ))) *
          (nwayNode B (j₀ - 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoeffj (by positivity)
      _ = (2 : ℝ) ^ j₀ * (B : ℝ) ^ (N - 2) := by
        simp only [nwayNode, NNReal.coe_pow, NNReal.coe_natCast]
        rw [mul_assoc, hpowJoin]
      _ ≤ (2 : ℝ) ^ (2 * N - 2) * (B : ℝ) ^ (N - 2) :=
        mul_le_mul_of_nonneg_right htwo (pow_nonneg (by positivity) _)
  · dsimp [j₀] at hvbuy ⊢
    rw [if_neg hvbuy]
    rw [mul_zero]
    exact mul_nonneg
      (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (2 * N - 2))
      (pow_nonneg (show (0 : ℝ) ≤ B by positivity) (N - 2))

/-- Upper-bound half of `lem:N-class-revenue-localization`. -/
theorem pricingNWay_revenue_localization_upper (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N)
    (hcoeff : ∀ j : ℕ, nwayCoeff B N j ≤
      (2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ)))
    (v : PositivePrice) (hvout : v ∉ pricingGoodInterval B N h) :
    postedRevenue (pricingNWayLaw B N hB hN h) v.1 ≤
      ((2 : ℝ) ^ (2 * N - 2) + pricingCN N) * (B : ℝ) ^ (N - 2) := by
  have hdecomp := pricingNWay_postedRevenue_le_special_add_tail B N hB hN h hcoeff v.1
  have hspecial := pricingNWay_specialRevenue_le B N hB hN h hcoeff v hvout
  calc
    postedRevenue (pricingNWayLaw B N hB hN h) v.1 ≤
        ((nwayResidueWeightCertificate B N hB hN).mass h
            (pricingSpecialIndex N h)).toReal *
          (if v.1 ≤ nwayNode B (pricingSpecialIndex N h) then (v.1 : ℝ) else 0) +
        pricingCN N * (B : ℝ) ^ (N - 2) := hdecomp
    _ ≤ (2 : ℝ) ^ (2 * N - 2) * (B : ℝ) ^ (N - 2) +
        pricingCN N * (B : ℝ) ^ (N - 2) := add_le_add hspecial (le_refl _)
    _ = ((2 : ℝ) ^ (2 * N - 2) + pricingCN N) * (B : ℝ) ^ (N - 2) := by
      ring

/-- Lower-bound half of `lem:N-class-revenue-localization`. -/
theorem pricingNWay_optimalRevenue_lower (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N)
    (hcoeff : ∀ j : ℕ,
      (B : ℝ) ^ (-(nwayExponent N j : ℤ)) ≤ nwayCoeff B N j) :
    (B : ℝ) ^ (N - 1) / 4 ≤
      optimalPostedRevenue (pricingNWayLaw B N hB hN h) := by
  let C := nwayResidueWeightCertificate B N hB hN
  let j₀ := pricingSpecialIndex N h
  have hjmod := pricingSpecialIndex_mod hN h
  have hgap := pricingSpecialIndex_exponent_gap hN h
  have hlowpos : 0 < (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) := by positivity
  have hWpos := nwayNormalizer_pos B N hB hN
  have hWlt := nwayNormalizer_lt_four B N hB hN
  have hmassEq : (C.mass h j₀).toReal =
      nwayCoeff B N j₀ / nwayNormalizer B N := by
    rw [show (C.mass h j₀).toReal =
        if j₀ % N = h.val then nwayCoeff B N j₀ / nwayNormalizer B N else 0 by
      simpa [C] using pricingNWayCertificate_mass_toReal B N hB hN h j₀]
    rw [if_pos]
    simpa [j₀] using hjmod
  have hmassLower :
      (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) / 4 ≤ (C.mass h j₀).toReal := by
    rw [hmassEq]
    calc
      (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) / 4 ≤
          (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) / nwayNormalizer B N := by
        exact (div_le_div_iff_of_pos_left hlowpos (by norm_num) hWpos).2 hWlt.le
      _ ≤ nwayCoeff B N j₀ / nwayNormalizer B N :=
        div_le_div_of_nonneg_right (hcoeff j₀) hWpos.le
  have hBne : (B : ℝ) ≠ 0 := by positivity
  change (j₀ : ℤ) - nwayExponent N j₀ = ((N - 1 : ℕ) : ℤ) at hgap
  have hpowJoin :
      (B : ℝ) ^ j₀ * (B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) =
        (B : ℝ) ^ (N - 1) := by
    rw [show (B : ℝ) ^ j₀ = (B : ℝ) ^ (j₀ : ℤ) by simp]
    rw [← zpow_add₀ hBne]
    rw [show (j₀ : ℤ) + -(nwayExponent N j₀ : ℤ) =
      ((N - 1 : ℕ) : ℤ) by linarith]
    simp
  have hatom :
      (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real {nwayNode B j₀} =
        (C.mass h j₀).toReal := by
    rw [pricingNWayLaw_atomReal B N hB hN h j₀, if_pos hjmod]
    exact hmassEq.symm
  have hatomTail :
      (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real {nwayNode B j₀} ≤
        (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real (Ici (nwayNode B j₀)) :=
    measureReal_mono (singleton_subset_iff.mpr Set.self_mem_Ici) (measure_ne_top _ _)
  calc
    (B : ℝ) ^ (N - 1) / 4 =
        (B : ℝ) ^ j₀ *
          ((B : ℝ) ^ (-(nwayExponent N j₀ : ℤ)) / 4) := by
      rw [← hpowJoin]
      ring
    _ ≤ (B : ℝ) ^ j₀ * (C.mass h j₀).toReal := by
      exact mul_le_mul_of_nonneg_left hmassLower (pow_nonneg (by positivity) _)
    _ = (nwayNode B j₀ : ℝ) *
        (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real {nwayNode B j₀} := by
      rw [hatom]
      simp [nwayNode]
    _ ≤ (nwayNode B j₀ : ℝ) *
        (pricingNWayLaw B N hB hN h : Measure ℝ≥0).real (Ici (nwayNode B j₀)) := by
      gcongr
    _ = postedRevenue (pricingNWayLaw B N hB hN h) (nwayNode B j₀) := rfl
    _ ≤ optimalPostedRevenue (pricingNWayLaw B N hB hN h) :=
      postedRevenue_le_optimal
        ((nwayResidueWeightCertificate B N hB hN).law_hasFiniteMoments h 1) _

/-- `lem:N-class-revenue-localization`, `sections/revenue.tex`, lines 82--113. -/
theorem N_class_revenue_localization (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    (B : ℝ) ^ (N - 1) / 4 ≤
        optimalPostedRevenue (pricingNWayLaw B N hB hN h) ∧
      ∀ v : PositivePrice, v ∉ pricingGoodInterval B N h →
        postedRevenue (pricingNWayLaw B N hB hN h) v.1 ≤
          ((2 : ℝ) ^ (2 * N - 2) + pricingCN N) * (B : ℝ) ^ (N - 2) := by
  constructor
  · exact pricingNWay_optimalRevenue_lower B N hB hN h
      (fun j ↦ nwayCoeff_lower_bound B N j hB hN)
  · intro v hv
    exact pricingNWay_revenue_localization_upper B N hB hN h
      (fun j ↦ nwayCoeff_upper_bound B N j hB hN) v hv

/-- All concrete pricing laws in one `N`-way family agree on every finite moment. -/
theorem pricingNWayLaw_momentEquivalent (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h h' : Fin N) :
    MomentEquivalent (pricingNWayLaw B N hB hN h)
      (pricingNWayLaw B N hB hN h') :=
  (nwayResidueWeightCertificate B N hB hN).law_momentEquivalent h h'

/-- A finite-first-moment law has a nonnegative optimal posted-price benchmark. -/
theorem optimalPostedRevenue_nonneg_of_finiteFirstMoment {mu : Distribution}
    (hfirst : HasFiniteMoment mu 1) : 0 ≤ optimalPostedRevenue mu := by
  simpa [postedRevenue] using postedRevenue_le_optimal hfirst 0

/-- Pigeonhole step in `thm:randomized-pricing-all-moments`: one of the pairwise-disjoint
good-price intervals receives probability at most `1/N`. -/
theorem exists_pricingGoodInterval_measureReal_le {B N : ℕ}
    (hB : 2 ≤ B) (hN : 2 ≤ N) (lambda : PricingRule) :
    ∃ h : Fin N,
      (lambda : Measure PositivePrice).real (pricingGoodInterval B N h) ≤ 1 / (N : ℝ) := by
  have hsum :
      (∑ h : Fin N,
          (lambda : Measure PositivePrice).real (pricingGoodInterval B N h)) ≤ 1 := by
    calc
      (∑ h : Fin N,
          (lambda : Measure PositivePrice).real (pricingGoodInterval B N h)) =
          (lambda : Measure PositivePrice).real
            (⋃ h : Fin N, pricingGoodInterval B N h) :=
        (measureReal_iUnion_fintype (pricingGoodInterval_pairwiseDisjoint hB hN)
          (measurableSet_pricingGoodInterval B N)).symm
      _ ≤ (lambda : Measure PositivePrice).real Set.univ :=
        measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
      _ = 1 := probReal_univ
  have hconst : (∑ _h : Fin N, (1 / (N : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
  have hcompare :
      (∑ h : Fin N,
          (lambda : Measure PositivePrice).real (pricingGoodInterval B N h)) ≤
        ∑ _h : Fin N, (1 / (N : ℝ)) := by
    rw [hconst]
    exact hsum
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨h, _hhmem, hh⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin N)))
      huniv hcompare
  exact ⟨h, hh⟩

/-- The integral-splitting argument in `thm:randomized-pricing-all-moments`, stated for an
arbitrary measurable good-price region.  The conclusion is multiplication-form and contains
no division by a possibly-zero benchmark. -/
theorem randomizedPostedRevenue_le_of_localization {mu : Distribution}
    (hfirst : HasFiniteMoment mu 1) (lambda : PricingRule) {s : Set PositivePrice}
    (hs : MeasurableSet s) {K : ℝ} (hK : 0 ≤ K)
    (hout : ∀ v : PositivePrice, v ∉ s → postedRevenue mu v.1 ≤ K) :
    randomizedPostedRevenue mu lambda ≤
      (lambda : Measure PositivePrice).real s * optimalPostedRevenue mu + K := by
  let f : PositivePrice → ℝ := fun v ↦ postedRevenue mu v.1
  have hf : Integrable f (lambda : Measure PositivePrice) :=
    integrable_randomizedPostedRevenue hfirst lambda
  have hopt0 := optimalPostedRevenue_nonneg_of_finiteFirstMoment hfirst
  have hin :
      (∫ v in s, f v ∂(lambda : Measure PositivePrice)) ≤
        (lambda : Measure PositivePrice).real s * optimalPostedRevenue mu := by
    calc
      (∫ v in s, f v ∂(lambda : Measure PositivePrice)) ≤
          ∫ _v in s, optimalPostedRevenue mu ∂(lambda : Measure PositivePrice) := by
        apply setIntegral_mono_on hf.integrableOn (integrable_const _) hs
        intro v hv
        exact postedRevenue_le_optimal hfirst v.1
      _ = (lambda : Measure PositivePrice).real s * optimalPostedRevenue mu := by
        simp [setIntegral_const, smul_eq_mul]
  have hout' :
      (∫ v in sᶜ, f v ∂(lambda : Measure PositivePrice)) ≤ K := by
    calc
      (∫ v in sᶜ, f v ∂(lambda : Measure PositivePrice)) ≤
          ∫ _v in sᶜ, K ∂(lambda : Measure PositivePrice) := by
        apply setIntegral_mono_on hf.integrableOn (integrable_const _) hs.compl
        intro v hv
        exact hout v hv
      _ = (lambda : Measure PositivePrice).real sᶜ * K := by
        simp [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * K := by
        exact mul_le_mul_of_nonneg_right measureReal_le_one hK
      _ = K := one_mul K
  calc
    randomizedPostedRevenue mu lambda =
        (∫ v in s, f v ∂(lambda : Measure PositivePrice)) +
          ∫ v in sᶜ, f v ∂(lambda : Measure PositivePrice) := by
      exact (integral_add_compl hs hf).symm
    _ ≤ (lambda : Measure PositivePrice).real s * optimalPostedRevenue mu + K :=
      add_le_add hin hout'

/-- Multiplication-form randomized-pricing bound obtained from a finite family of disjoint
localized good-price regions. -/
theorem exists_randomizedPostedRevenue_le_of_localized_family {B N : ℕ}
    (hB : 2 ≤ B) (hN : 2 ≤ N) (mu : Fin N → Distribution)
    (hfirst : ∀ h, HasFiniteMoment (mu h) 1) {K : ℝ} (hK : 0 ≤ K)
    (hout : ∀ (h : Fin N) (v : PositivePrice),
      v ∉ pricingGoodInterval B N h → postedRevenue (mu h) v.1 ≤ K)
    (lambda : PricingRule) :
    ∃ h : Fin N,
      randomizedPostedRevenue (mu h) lambda ≤
        (1 / (N : ℝ)) * optimalPostedRevenue (mu h) + K := by
  obtain ⟨h, hh⟩ := exists_pricingGoodInterval_measureReal_le hB hN lambda
  refine ⟨h, ?_⟩
  have hsplit := randomizedPostedRevenue_le_of_localization (hfirst h) lambda
    (measurableSet_pricingGoodInterval B N h) hK (hout h)
  calc
    randomizedPostedRevenue (mu h) lambda ≤
        (lambda : Measure PositivePrice).real (pricingGoodInterval B N h) *
            optimalPostedRevenue (mu h) + K := hsplit
    _ ≤ (1 / (N : ℝ)) * optimalPostedRevenue (mu h) + K := by
      gcongr
      exact optimalPostedRevenue_nonneg_of_finiteFirstMoment (hfirst h)

/-- Ratio bridge for the localized-family bound, applied only after a strictly positive common
lower bound on every optimal revenue has been supplied. -/
theorem exists_randomizedPostedRevenue_ratio_le_of_localized_family {B N : ℕ}
    (hB : 2 ≤ B) (hN : 2 ≤ N) (mu : Fin N → Distribution)
    (hfirst : ∀ h, HasFiniteMoment (mu h) 1) {L K : ℝ}
    (hL : 0 < L) (hK : 0 ≤ K)
    (hlower : ∀ h, L ≤ optimalPostedRevenue (mu h))
    (hout : ∀ (h : Fin N) (v : PositivePrice),
      v ∉ pricingGoodInterval B N h → postedRevenue (mu h) v.1 ≤ K)
    (lambda : PricingRule) :
    ∃ h : Fin N,
      randomizedPostedRevenue (mu h) lambda / optimalPostedRevenue (mu h) ≤
        1 / (N : ℝ) + K / L := by
  obtain ⟨h, hh⟩ := exists_randomizedPostedRevenue_le_of_localized_family
    hB hN mu hfirst hK hout lambda
  have hopt : 0 < optimalPostedRevenue (mu h) := hL.trans_le (hlower h)
  refine ⟨h, (div_le_iff₀ hopt).2 ?_⟩
  have hKL : K ≤ (K / L) * optimalPostedRevenue (mu h) := by
    calc
      K = (K / L) * L := by field_simp [ne_of_gt hL]
      _ ≤ (K / L) * optimalPostedRevenue (mu h) := by
        exact mul_le_mul_of_nonneg_left (hlower h) (div_nonneg hK hL.le)
  calc
    randomizedPostedRevenue (mu h) lambda ≤
        (1 / (N : ℝ)) * optimalPostedRevenue (mu h) + K := hh
    _ ≤ (1 / (N : ℝ)) * optimalPostedRevenue (mu h) +
        (K / L) * optimalPostedRevenue (mu h) := add_le_add (le_refl _) hKL
    _ = (1 / (N : ℝ) + K / L) * optimalPostedRevenue (mu h) := by ring

/-- Concrete parameterized randomized-pricing bound, in division-free form. -/
theorem randomizedPricing_universal_of_parameters (epsilon : ℝ) (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N)
    (hNsmall : 1 / (N : ℝ) < epsilon / 2)
    (hBsmall : 4 * ((2 : ℝ) ^ (2 * N - 2) + pricingCN N) / B < epsilon / 2)
    (lambda : PricingRule) :
    ∃ h : Fin N,
      randomizedPostedRevenue (pricingNWayLaw B N hB hN h) lambda <
        epsilon * optimalPostedRevenue (pricingNWayLaw B N hB hN h) := by
  let mu : Fin N → Distribution := pricingNWayLaw B N hB hN
  let A : ℝ := (2 : ℝ) ^ (2 * N - 2) + pricingCN N
  let L : ℝ := (B : ℝ) ^ (N - 1) / 4
  let K : ℝ := A * (B : ℝ) ^ (N - 2)
  have hA : 0 ≤ A := add_nonneg (pow_nonneg (by positivity) _) (pricingCN_nonneg N)
  have hK : 0 ≤ K := mul_nonneg hA (pow_nonneg (by positivity) _)
  have hfirst : ∀ h, HasFiniteMoment (mu h) 1 := fun h ↦
    (nwayResidueWeightCertificate B N hB hN).law_hasFiniteMoments h 1
  have hout : ∀ (h : Fin N) (v : PositivePrice),
      v ∉ pricingGoodInterval B N h → postedRevenue (mu h) v.1 ≤ K := by
    intro h v hv
    simpa [mu, K, A] using (N_class_revenue_localization B N hB hN h).2 v hv
  obtain ⟨h, hrev⟩ := exists_randomizedPostedRevenue_le_of_localized_family
    hB hN mu hfirst hK hout lambda
  have hlower : L ≤ optimalPostedRevenue (mu h) := by
    simpa [mu, L] using (N_class_revenue_localization B N hB hN h).1
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hopt : 0 < optimalPostedRevenue (mu h) := hLpos.trans_le hlower
  have hscale : K = (4 * A / B) * L := by
    have hNm : N - 1 = (N - 2) + 1 := by omega
    dsimp [K, L]
    rw [hNm, pow_succ]
    field_simp [show (B : ℝ) ≠ 0 by positivity]
    <;> ring
  have hKopt : K ≤ (4 * A / B) * optimalPostedRevenue (mu h) := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hlower (div_nonneg (mul_nonneg (by norm_num) hA) (by positivity))
  refine ⟨h, ?_⟩
  calc
    randomizedPostedRevenue (mu h) lambda ≤
        (1 / (N : ℝ)) * optimalPostedRevenue (mu h) + K := hrev
    _ ≤ (1 / (N : ℝ)) * optimalPostedRevenue (mu h) +
        (4 * A / B) * optimalPostedRevenue (mu h) := add_le_add (le_refl _) hKopt
    _ = (1 / (N : ℝ) + 4 * A / B) * optimalPostedRevenue (mu h) := by ring
    _ < epsilon * optimalPostedRevenue (mu h) := by
      apply mul_lt_mul_of_pos_right _ hopt
      have : 4 * A / B < epsilon / 2 := by simpa [A] using hBsmall
      linarith

/-- Explicit Archimedean choice of the two integer parameters used in
`thm:randomized-pricing-all-moments`. -/
theorem exists_randomizedPricing_parameters (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N B : ℕ, 2 ≤ N ∧ 2 ≤ B ∧
      1 / (N : ℝ) < epsilon / 2 ∧
      4 * ((2 : ℝ) ^ (2 * N - 2) + pricingCN N) / B < epsilon / 2 := by
  let N : ℕ := ⌈2 / epsilon⌉₊ + 2
  have hN : 2 ≤ N := by simp [N]
  have hNgt : 2 / epsilon < (N : ℝ) := by
    calc
      2 / epsilon ≤ (⌈2 / epsilon⌉₊ : ℝ) := Nat.le_ceil _
      _ < ((⌈2 / epsilon⌉₊ + 2 : ℕ) : ℝ) := by norm_num
      _ = (N : ℝ) := by rfl
  have hNeps : 2 < epsilon * (N : ℝ) := by
    have := (div_lt_iff₀ hepsilon).1 hNgt
    nlinarith
  have hNsmall : 1 / (N : ℝ) < epsilon / 2 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < N by positivity)).2
    nlinarith
  let A : ℝ := (2 : ℝ) ^ (2 * N - 2) + pricingCN N
  have hA : 0 ≤ A := add_nonneg (pow_nonneg (by positivity) _) (pricingCN_nonneg N)
  let B : ℕ := ⌈8 * A / epsilon⌉₊ + 2
  have hB : 2 ≤ B := by simp [B]
  have hBgt : 8 * A / epsilon < (B : ℝ) := by
    calc
      8 * A / epsilon ≤ (⌈8 * A / epsilon⌉₊ : ℝ) := Nat.le_ceil _
      _ < ((⌈8 * A / epsilon⌉₊ + 2 : ℕ) : ℝ) := by norm_num
      _ = (B : ℝ) := by rfl
  have hBeps : 8 * A < epsilon * (B : ℝ) := by
    have := (div_lt_iff₀ hepsilon).1 hBgt
    nlinarith
  have hBsmall : 4 * A / (B : ℝ) < epsilon / 2 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < B by positivity)).2
    nlinarith
  exact ⟨N, B, hN, hB, hNsmall, by simpa [A] using hBsmall⟩

/-- Division-free form of `thm:randomized-pricing-all-moments`, preserving the repaired
quantifier order `∀ epsilon>0, ∃ N≥2, ∃ (mu_h), ∀ lambda, ∃ h`. -/
theorem randomized_pricing_all_moments_universal (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∃ mu : Fin N → Distribution,
        (∀ h h' : Fin N, MomentEquivalent (mu h) (mu h')) ∧
          ∀ lambda : PricingRule, ∃ h : Fin N,
            randomizedPostedRevenue (mu h) lambda <
              epsilon * optimalPostedRevenue (mu h) := by
  obtain ⟨N, B, hN, hB, hNsmall, hBsmall⟩ :=
    exists_randomizedPricing_parameters epsilon hepsilon
  letI : NeZero N := ⟨by omega⟩
  let mu : Fin N → Distribution := pricingNWayLaw B N hB hN
  refine ⟨N, hN, mu, ?_, ?_⟩
  · exact fun h h' ↦ pricingNWayLaw_momentEquivalent B N hB hN h h'
  · exact fun lambda ↦
      randomizedPricing_universal_of_parameters epsilon B N hB hN hNsmall hBsmall lambda

/-- `thm:randomized-pricing-all-moments`, `sections/revenue.tex`, lines 120--143.

The ratio is formed only after `N_class_revenue_localization` proves the selected law's
optimal revenue is strictly positive. -/
theorem randomized_pricing_all_moments (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∃ mu : Fin N → Distribution,
        (∀ h h' : Fin N, MomentEquivalent (mu h) (mu h')) ∧
          ∀ lambda : PricingRule, ∃ h : Fin N,
            randomizedPostedRevenue (mu h) lambda / optimalPostedRevenue (mu h) < epsilon := by
  obtain ⟨N, B, hN, hB, hNsmall, hBsmall⟩ :=
    exists_randomizedPricing_parameters epsilon hepsilon
  letI : NeZero N := ⟨by omega⟩
  let mu : Fin N → Distribution := pricingNWayLaw B N hB hN
  refine ⟨N, hN, mu, ?_, ?_⟩
  · exact fun h h' ↦ pricingNWayLaw_momentEquivalent B N hB hN h h'
  · intro lambda
    obtain ⟨h, hrev⟩ :=
      randomizedPricing_universal_of_parameters epsilon B N hB hN hNsmall hBsmall lambda
    have hlower := (N_class_revenue_localization B N hB hN h).1
    have hopt : 0 < optimalPostedRevenue (mu h) := by
      apply (show 0 < (B : ℝ) ^ (N - 1) / 4 by positivity).trans_le
      simpa [mu] using hlower
    exact ⟨h, (div_lt_iff₀ hopt).2 (by simpa [mu] using hrev)⟩

end

end MomentAmbiguity
