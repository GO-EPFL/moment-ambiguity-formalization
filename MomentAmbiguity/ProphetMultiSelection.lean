import MomentAmbiguity.Prophet
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Reduction from multiple selections to one selection

The manuscript samples one of `r` selection slots uniformly before arrivals.  The kernel below
implements that reduction extensionally: conditional on the selected set, every selected index
receives mass `1/r`, and unused mass is assigned to `none`.  On the null event that a purported
at-most-`r` policy outputs too many indices, it also returns `none`.
-/

open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Conditional mass assigned to a single uniform selection slot. -/
def uniformSelectedWeight {m r : ℕ} (_hr : 1 ≤ r) (s : Finset (Fin m))
    (choice : Option (Fin m)) : ℝ≥0 :=
  if _hs : s.card ≤ r then
    match choice with
    | none => ((r - s.card : ℕ) : ℝ≥0) / r
    | some i => if i ∈ s then (1 : ℝ≥0) / r else 0
  else if choice = none then 1 else 0

theorem sum_uniformSelectedWeight {m r : ℕ} (hr : 1 ≤ r) (s : Finset (Fin m)) :
    ∑ choice : Option (Fin m), uniformSelectedWeight hr s choice = 1 := by
  classical
  by_cases hs : s.card ≤ r
  · rw [Fintype.sum_option]
    simp only [uniformSelectedWeight, hs, ↓reduceDIte]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [show ({x ∈ Finset.univ | x ∈ s} : Finset (Fin m)) = s by ext; simp]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hr0 : (r : ℝ≥0) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    simp only [div_eq_mul_inv, one_mul]
    rw [← add_mul]
    rw [show ((r - s.card : ℕ) : ℝ≥0) + s.card = r by
      exact_mod_cast Nat.sub_add_cancel hs]
    exact mul_inv_cancel₀ hr0
  · rw [Fintype.sum_option]
    simp [uniformSelectedWeight, hs]

/-- The conditional PMF that chooses a uniformly random one of `r` slots. -/
def uniformSelectedPMF {m r : ℕ} (hr : 1 ≤ r) (s : Finset (Fin m)) :
    PMF (Option (Fin m)) :=
  pmfOfFintype (uniformSelectedWeight hr s) (sum_uniformSelectedWeight hr s)

@[simp] theorem uniformSelectedPMF_apply {m r : ℕ} (hr : 1 ≤ r)
    (s : Finset (Fin m)) (choice : Option (Fin m)) :
    uniformSelectedPMF hr s choice = uniformSelectedWeight hr s choice := by
  simp [uniformSelectedPMF]

/-- A Markov kernel implementing the conditional uniform-slot choice. -/
def uniformSelectedKernel {m r : ℕ} (hr : 1 ≤ r) :
    Kernel (Finset (Fin m)) (Option (Fin m)) where
  toFun s := (uniformSelectedPMF hr s).toMeasure
  measurable' := measurable_of_finite _

instance uniformSelectedKernel_isMarkov {m r : ℕ} (hr : 1 ≤ r) :
    IsMarkovKernel (uniformSelectedKernel (m := m) hr) := by
  refine ⟨fun s ↦ ?_⟩
  change IsProbabilityMeasure (uniformSelectedPMF hr s).toMeasure
  infer_instance

/-- The `ENNReal` mass of one of the `r` ex-ante slots. -/
def uniformSlotMass (r : ℕ) : ℝ≥0∞ := (((1 : ℝ≥0) / r : ℝ≥0) : ℝ≥0∞)

theorem uniformSelectedKernel_singleton {m r : ℕ} (hr : 1 ≤ r)
    (s : Finset (Fin m)) (hs : s.card ≤ r) (i : Fin m) :
    uniformSelectedKernel hr s {some i} =
      if i ∈ s then uniformSlotMass r else 0 := by
  rw [show uniformSelectedKernel hr s {some i} =
      (uniformSelectedPMF hr s).toMeasure {some i} from rfl,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSpace.measurableSet_top)]
  rw [uniformSelectedPMF_apply]
  by_cases hi : i ∈ s
  · unfold uniformSelectedWeight uniformSlotMass
    simp [hs, hi]
  · simp [uniformSelectedWeight, hs, hi]

/-- Composing the slot sampler with an almost-surely valid multi-selection kernel makes the
probability of choosing `i` exactly `1/r` times its membership marginal. -/
theorem comp_uniformSelectedKernel_singleton {X : Type*} [MeasurableSpace X]
    {m r : ℕ} (hr : 1 ≤ r) (K : Kernel X (Finset (Fin m))) [IsMarkovKernel K]
    (x : X) (i : Fin m) (hvalid : ∀ᵐ s ∂K x, s.card ≤ r) :
    (uniformSelectedKernel hr ∘ₖ K) x {some i} =
      uniformSlotMass r * K x {s | i ∈ s} := by
  rw [Kernel.comp_apply' _ _ _ MeasurableSpace.measurableSet_top]
  rw [lintegral_congr_ae (hvalid.mono fun s hs ↦
    uniformSelectedKernel_singleton hr s hs i)]
  have hset : MeasurableSet {s : Finset (Fin m) | i ∈ s} :=
    MeasurableSpace.measurableSet_top
  rw [show (fun s : Finset (Fin m) ↦ if i ∈ s then uniformSlotMass r else 0) =
      {s : Finset (Fin m) | i ∈ s}.indicator (fun _ ↦ uniformSlotMass r) by
        funext s
        by_cases hi : i ∈ s <;> simp [Set.indicator, hi]]
  rw [lintegral_indicator hset]
  simp

/-- The induced single-choice policy obtained by sampling a uniform selection slot. -/
def inducedSinglePolicy {m r : ℕ} (hr : 1 ≤ r) (policy : MultiSelectionPolicy m r) :
    ProphetPolicy m where
  kernel := uniformSelectedKernel hr ∘ₖ policy.kernel
  isMarkov := inferInstance
  causal := by
    intro profile x y t hxy
    have hxvalid : ∀ᵐ s ∂policy.kernel (profile, x), s.card ≤ r := by
      exact (ae_iff_prob_eq_one (measurable_of_finite _)).2 (policy.card_le profile x)
    have hyvalid : ∀ᵐ s ∂policy.kernel (profile, y), s.card ≤ r := by
      exact (ae_iff_prob_eq_one (measurable_of_finite _)).2 (policy.card_le profile y)
    rw [comp_uniformSelectedKernel_singleton hr policy.kernel (profile, x) t hxvalid,
      comp_uniformSelectedKernel_singleton hr policy.kernel (profile, y) t hyvalid,
      policy.causal profile x y t hxy]

/-! ## Exact reward identity -/

/-- On a valid selected set, a uniformly sampled slot receives exactly `1/r` of its total
value in conditional expectation. -/
theorem integral_uniformSelectedKernel_reward {m r : ℕ} (hr : 1 ≤ r)
    (x : ProphetPath m) (s : Finset (Fin m)) (hs : s.card ≤ r) :
    (∫ choice, (match choice with | none => 0 | some i => (x i : ℝ))
        ∂uniformSelectedKernel hr s) =
      (1 / (r : ℝ)) * ∑ i ∈ s, (x i : ℝ) := by
  rw [integral_fintype (MeasureTheory.Integrable.of_finite)]
  simp only [Fintype.sum_option, smul_eq_mul, mul_zero, zero_add]
  simp only [Measure.real_def]
  simp_rw [uniformSelectedKernel_singleton hr s hs]
  simp only [apply_ite, ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [show ({i ∈ Finset.univ | i ∈ s} : Finset (Fin m)) = s by ext; simp]
  have hmass : (uniformSlotMass r).toReal = 1 / (r : ℝ) := by
    unfold uniformSlotMass
    rw [ENNReal.coe_toReal]
    norm_num
  simp_rw [hmass]
  rw [Finset.mul_sum]

/-- Conditional on any realized path, the induced policy's expected reward is exactly
`1/r` times the multi-selection policy's expected total reward. -/
theorem kernel_inducedSinglePolicy_reward {m r : ℕ} (hr : 1 ≤ r)
    (policy : MultiSelectionPolicy m r) (profile : MomentProfile m)
    (x : ProphetPath m) :
    (∫ choice, (match choice with | none => 0 | some i => (x i : ℝ))
        ∂(inducedSinglePolicy hr policy).kernel (profile, x)) =
      (1 / (r : ℝ)) *
        ∫ selected, (∑ i ∈ selected, (x i : ℝ)) ∂policy.kernel (profile, x) := by
  change (∫ choice, (match choice with | none => 0 | some i => (x i : ℝ))
      ∂(uniformSelectedKernel hr ∘ₖ policy.kernel) (profile, x)) = _
  rw [Kernel.integral_comp (MeasureTheory.Integrable.of_finite)]
  have hvalid : ∀ᵐ s ∂policy.kernel (profile, x), s.card ≤ r :=
    (ae_iff_prob_eq_one (measurable_of_finite _)).2 (policy.card_le profile x)
  rw [integral_congr_ae (hvalid.mono fun s hs ↦
    integral_uniformSelectedKernel_reward hr x s hs)]
  rw [integral_const_mul]

/-- The induced single-choice reward is exactly the multi-selection total divided by `r`.
This identity needs no integrability side condition: all inner action spaces are finite, and
both outer functions are pointwise nonnegative, so the Bochner integral convention agrees on
both sides even outside the finite-first-moment instances used downstream. -/
theorem inducedSinglePolicy_expectedReward {m r : ℕ} (hr : 1 ≤ r)
    (policy : MultiSelectionPolicy m r) (laws : Fin m → Distribution) :
    prophetExpectedReward (inducedSinglePolicy hr policy) laws =
      (1 / (r : ℝ)) * multiExpectedReward policy laws := by
  unfold prophetExpectedReward multiExpectedReward
  calc
    (∫ x, ∫ choice,
        (match choice with | none => 0 | some i => (x i : ℝ))
          ∂(inducedSinglePolicy hr policy).kernel (disclosedProfile laws, x)
        ∂(independentValues laws : Measure _)) =
        ∫ x, (1 / (r : ℝ)) *
          (∫ selected, (∑ i ∈ selected, (x i : ℝ))
            ∂policy.kernel (disclosedProfile laws, x))
          ∂(independentValues laws : Measure _) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        kernel_inducedSinglePolicy_reward hr policy (disclosedProfile laws) x
    _ = (1 / (r : ℝ)) *
        ∫ x, ∫ selected, (∑ i ∈ selected, (x i : ℝ))
          ∂policy.kernel (disclosedProfile laws, x)
        ∂(independentValues laws : Measure _) := by
      rw [integral_const_mul]

/-- Multiplication form of the exact reduction, convenient for the manuscript's final
corollary. -/
theorem multiExpectedReward_eq_r_mul_induced {m r : ℕ} (hr : 1 ≤ r)
    (policy : MultiSelectionPolicy m r) (laws : Fin m → Distribution) :
    multiExpectedReward policy laws =
      (r : ℝ) * prophetExpectedReward (inducedSinglePolicy hr policy) laws := by
  rw [inducedSinglePolicy_expectedReward hr policy laws]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp

/-- Any internally proved adversarial upper family for single-selection policies transfers to
at-most-`r` total reward with precisely the factor `r`.  This helper keeps every guarantee in
multiplication form and does not divide by the order-statistic benchmark. -/
theorem exists_multiSelection_upper_of_single {m r : ℕ} (hr : 1 ≤ r)
    (hrm : r ≤ m) (C : ℝ)
    (hsingle : ∀ policy : ProphetPolicy m,
      ∃ laws : Fin m → Distribution,
        (∀ i, HasFiniteMoments (laws i)) ∧
        prophetExpectedReward policy laws ≤
          C * orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) laws)
    (policy : MultiSelectionPolicy m r) :
    ∃ laws : Fin m → Distribution,
      (∀ i, HasFiniteMoments (laws i)) ∧
      multiExpectedReward policy laws ≤
        ((r : ℝ) * C) *
          orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) laws := by
  obtain ⟨laws, hfinite, hupper⟩ := hsingle (inducedSinglePolicy hr policy)
  refine ⟨laws, hfinite, ?_⟩
  rw [multiExpectedReward_eq_r_mul_induced hr policy laws]
  calc
    (r : ℝ) * prophetExpectedReward (inducedSinglePolicy hr policy) laws ≤
        (r : ℝ) * (C * orderStatisticBenchmark
          (⟨r, hr, hrm⟩ : ValidRank m) laws) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = ((r : ℝ) * C) *
        orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) laws := by ring

/-- The pointwise form of `cor:prophet-r-selection`: a single-selection upper witness with
constant `b` transfers to total reward at the claimed constant `r b`. -/
theorem prophet_r_selection_of_upper_witness (r : ℕ) (hr : 1 ≤ r)
    (b : ℝ) (m₀ : ℕ) (hrm₀ : r ≤ m₀)
    (hsingle : ∀ (m : ℕ) (hm : m₀ ≤ m) (policy : ProphetPolicy m),
      ∃ laws : Fin m → Distribution,
        (∀ i, HasFiniteMoments (laws i)) ∧
        prophetExpectedReward policy laws ≤
          (b / Real.log m) *
            orderStatisticBenchmark (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) laws) :
    ∀ (m : ℕ) (hm : m₀ ≤ m) (policy : MultiSelectionPolicy m r),
      ∃ laws : Fin m → Distribution,
        (∀ i, HasFiniteMoments (laws i)) ∧
        multiExpectedReward policy laws ≤
          ((r : ℝ) * b / Real.log m) *
            orderStatisticBenchmark (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) laws := by
  intro m hm policy
  obtain ⟨laws, hfinite, hupper⟩ := hsingle m hm (inducedSinglePolicy hr policy)
  refine ⟨laws, hfinite, ?_⟩
  rw [multiExpectedReward_eq_r_mul_induced hr policy laws]
  calc
    (r : ℝ) * prophetExpectedReward (inducedSinglePolicy hr policy) laws ≤
        (r : ℝ) * ((b / Real.log m) * orderStatisticBenchmark
          (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) laws) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = ((r : ℝ) * b / Real.log m) * orderStatisticBenchmark
        (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) laws := by ring

/-- `cor:prophet-r-selection`, `sections/prophet.tex`.  The constant and horizon come from the
proved upper construction.  For every at-most-`r` marginal-causal terminal-set
policy, the witness is an independent length-`m` instance with all moments finite. -/
theorem prophet_r_selection (r : ℕ) (hr : 1 ≤ r) :
    ∃ b : ℝ, 0 < b ∧ ∃ m₀ : ℕ,
      ∃ hrm₀ : r ≤ m₀, ∃ _hm₀ : 2 ≤ m₀,
        ∀ (m : ℕ) (hm : m₀ ≤ m) (policy : MultiSelectionPolicy m r),
          ∃ laws : Fin m → Distribution,
            (∀ i, HasFiniteMoments (laws i)) ∧
            multiExpectedReward policy laws ≤
              ((r : ℝ) * b / Real.log m) *
                orderStatisticBenchmark
                  (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) laws := by
  obtain ⟨b, hb, m₀, hrm₀, hm₀, hsingle⟩ := prophet_upper_witness r hr
  exact ⟨b, hb, m₀, hrm₀, hm₀,
    prophet_r_selection_of_upper_witness r hr b m₀ hrm₀ hsingle⟩

end

end MomentAmbiguity
