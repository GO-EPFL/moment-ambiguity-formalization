import MomentAmbiguity.ProphetEmbedding

/-!
# The internal prophet block-switch argument

`ProphetHardBlock` records consequences proved for a concrete binary-separator pair.  The final
upper theorem instantiates every block with that constructor; this module proves all remaining
product-measure, causality, tail, and averaging arguments internally.
-/

open scoped BigOperators ENNReal NNReal

namespace MomentAmbiguity

open MeasureTheory

noncomputable section

/-- Exact per-block consequences of `cor:order-stat-separator` at base `B=3`. -/
structure ProphetHardBlock (r n : ℕ) (kappa : ℝ) where
  pair : ProphetBlockPair
  hr : 1 ≤ r
  hrn : r ≤ n
  threshold : ℝ≥0
  nu_gap : ∀ᵐ x ∂(pair.nu : Measure ℝ≥0),
    x < threshold → x ≤ (3 * n : ℕ)
  mu_gap : ∀ᵐ x ∂(pair.mu : Measure ℝ≥0),
    x < threshold → x ≤ (3 : ℕ)
  nu_tail : (n : ℝ) *
      (∫ x, upperTailValue threshold x ∂(pair.nu : Measure ℝ≥0)) ≤ 6 / (n : ℝ)
  mu_tail : (n : ℝ) *
      (∫ x, upperTailValue threshold x ∂(pair.mu : Measure ℝ≥0)) ≤ 6 / (n : ℝ)
  rank_lower : 3 * kappa * (n : ℝ) ≤
    orderStatisticBenchmark (⟨r, hr, hrn⟩ : ValidRank n) (fun _ ↦ pair.nu)

def hardBlockPairs {L r N : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa) :
    Fin L → ProphetBlockPair := fun j ↦ (blocks j).pair

theorem hardBlock_end_le {m N L : ℕ} (hN : 0 < N)
    (hpacked : prophetBlockStart N L ≤ m) (j : Fin L) :
    prophetBlockStart N (j.1 + 1) ≤ m := by
  exact (prophetBlockStart_mono hN (by omega)).trans hpacked

def prophetBlockEmbedding {m N L : ℕ} (hN : 0 < N)
    (hpacked : prophetBlockStart N L ≤ m) (j : Fin L) :
    Fin (prophetBlockSize N j.1) ↪ Fin m where
  toFun := prophetBlockCoord N j.1 (hardBlock_end_le hN hpacked j)
  inj' := by
    intro a b hab
    apply Fin.ext
    have hv := Fin.ext_iff.mp hab
    change prophetBlockStart N j.1 + a.1 = prophetBlockStart N j.1 + b.1 at hv
    omega

theorem prophetBlockEmbedding_mem {m N L : ℕ} (hN : 0 < N)
    (hpacked : prophetBlockStart N L ≤ m) (j : Fin L)
    (i : Fin (prophetBlockSize N j.1)) :
    InProphetBlock N j (prophetBlockEmbedding hN hpacked j i).1 :=
  prophetBlockCoord_mem N j.1 (hardBlock_end_le hN hpacked j) i

theorem hardSwitch_hasFiniteFirstMoments {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) :
    HasFiniteFirstMoments
      (prophetSwitchLaws m N L (hardBlockPairs blocks) t) :=
  fun i ↦ prophetSwitchLaws_hasFiniteMoments (hardBlockPairs blocks) t i 1

/-- Block `t` alone transfers its iid order-statistic lower bound to the complete switch
instance. -/
theorem hardSwitch_benchmark_lower {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hpacked : prophetBlockStart N L ≤ m)
    (hrm : r ≤ m)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) :
    3 * kappa * (prophetBlockSize N t.1 : ℝ) ≤
      orderStatisticBenchmark (⟨r, (blocks t).hr, hrm⟩ : ValidRank m)
        (prophetSwitchLaws m N L (hardBlockPairs blocks) t) := by
  let e := prophetBlockEmbedding hN hpacked t
  let sub : Fin (prophetBlockSize N t.1) → Distribution := fun _ ↦ (blocks t).pair.nu
  let full := prophetSwitchLaws m N L (hardBlockPairs blocks) t
  have hcoord : ∀ i, full (e i) = sub i := by
    intro i
    exact prophetSwitchLaws_eq_nu_of_block hN (hardBlockPairs blocks) le_rfl
      (prophetBlockEmbedding_mem hN hpacked t i)
  have hsub : HasFiniteFirstMoments sub := fun _ ↦
    (blocks t).pair.momentEquivalent.right_finite 1
  have hfull : HasFiniteFirstMoments full := hardSwitch_hasFiniteFirstMoments blocks t
  exact (blocks t).rank_lower.trans
    (orderStatisticBenchmark_subvector_le (blocks t).hr (blocks t).hrn hrm e
      sub full hcoord hsub hfull)

/-- Threshold selected by the block containing a coordinate; padding coordinates use `1`. -/
def hardCoordinateThreshold {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (i : Fin m) : ℝ≥0 :=
  match prophetBlockOf N L i.1 with
  | none => 1
  | some j => (blocks j).threshold

/-- Non-tail cap in switch instance `t`. -/
def hardCoordinateCap {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) (i : Fin m) : ℝ≥0 :=
  match prophetBlockOf N L i.1 with
  | none => 3
  | some j => if j ≤ t then (3 * prophetBlockSize N j.1 : ℕ) else 3

theorem hardCoordinate_gap {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) (i : Fin m) :
    ∀ᵐ x ∂(prophetSwitchLaws m N L (hardBlockPairs blocks) t i : Measure ℝ≥0),
      x < hardCoordinateThreshold blocks i → x ≤ hardCoordinateCap blocks t i := by
  cases hblock : prophetBlockOf N L i.1 with
  | none =>
      simp only [prophetSwitchLaws, hardCoordinateThreshold, hardCoordinateCap,
        hblock, zeroDistribution]
      filter_upwards with x
      intro hx
      exact hx.le.trans (by norm_num)
  | some j =>
      by_cases hjt : j ≤ t
      · simp only [prophetSwitchLaws, hardCoordinateThreshold, hardCoordinateCap,
          hblock, hjt, ↓reduceIte]
        change ∀ᵐ x ∂((blocks j).pair.nu : Measure ℝ≥0),
          x < (blocks j).threshold → x ≤ (3 * prophetBlockSize N j.1 : ℕ)
        exact (blocks j).nu_gap
      · simp only [prophetSwitchLaws, hardCoordinateThreshold, hardCoordinateCap,
          hblock, hjt, ↓reduceIte]
        change ∀ᵐ x ∂((blocks j).pair.mu : Measure ℝ≥0),
          x < (blocks j).threshold → x ≤ (3 : ℕ)
        exact (blocks j).mu_gap

def hardCoordinateTail {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) (i : Fin m) : ℝ :=
  ∫ x, upperTailValue (hardCoordinateThreshold blocks i) x
    ∂(prophetSwitchLaws m N L (hardBlockPairs blocks) t i : Measure ℝ≥0)

theorem hardCoordinateTail_nonneg {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) (i : Fin m) : 0 ≤ hardCoordinateTail blocks t i := by
  exact integral_nonneg fun x ↦ upperTailValue_nonneg _ x

theorem hardCoordinateTail_eq_zero_of_none {m N L r : ℕ} {kappa : ℝ}
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) (i : Fin m) (hi : prophetBlockOf N L i.1 = none) :
    hardCoordinateTail blocks t i = 0 := by
  simp only [hardCoordinateTail, hardCoordinateThreshold, prophetSwitchLaws, hi,
    zeroDistribution]
  change (∫ x : ℝ≥0, upperTailValue 1 x ∂Measure.dirac 0) = 0
  rw [integral_dirac]
  simp [upperTailValue]

theorem sum_hardCoordinateTail_block_le {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hpacked : prophetBlockStart N L ≤ m)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t j : Fin L) :
    (∑ i ∈ prophetBlockIndices m N j.1, hardCoordinateTail blocks t i) ≤
      6 / (prophetBlockSize N j.1 : ℝ) := by
  rw [sum_prophetBlockIndices (hardBlock_end_le hN hpacked j)]
  by_cases hjt : j ≤ t
  · have heq : ∀ k : Fin (prophetBlockSize N j.1),
        hardCoordinateTail blocks t
          (prophetBlockCoord N j.1 (hardBlock_end_le hN hpacked j) k) =
          ∫ x, upperTailValue (blocks j).threshold x
            ∂((blocks j).pair.nu : Measure ℝ≥0) := by
      intro k
      simp [hardCoordinateTail, hardCoordinateThreshold, prophetSwitchLaws,
        prophetBlockOf_eq_some hN j
          (prophetBlockCoord_mem N j.1 (hardBlock_end_le hN hpacked j) k), hjt]
      rfl
    simp_rw [heq]
    simpa using (blocks j).nu_tail
  · have heq : ∀ k : Fin (prophetBlockSize N j.1),
        hardCoordinateTail blocks t
          (prophetBlockCoord N j.1 (hardBlock_end_le hN hpacked j) k) =
          ∫ x, upperTailValue (blocks j).threshold x
            ∂((blocks j).pair.mu : Measure ℝ≥0) := by
      intro k
      simp [hardCoordinateTail, hardCoordinateThreshold, prophetSwitchLaws,
        prophetBlockOf_eq_some hN j
          (prophetBlockCoord_mem N j.1 (hardBlock_end_le hN hpacked j) k), hjt]
      rfl
    simp_rw [heq]
    simpa using (blocks j).mu_tail

theorem sum_hardCoordinateTail_le {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hpacked : prophetBlockStart N L ≤ m)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (t : Fin L) :
    (∑ i : Fin m, hardCoordinateTail blocks t i) ≤ 12 / (N : ℝ) := by
  rw [sum_univ_eq_sum_blocks_of_zero_outside hN (hardCoordinateTail blocks t)
    (hardCoordinateTail_eq_zero_of_none blocks t)]
  calc
    (∑ j : Fin L, ∑ i ∈ prophetBlockIndices m N j.1,
        hardCoordinateTail blocks t i) ≤
        ∑ j : Fin L, 6 / (prophetBlockSize N j.1 : ℝ) := by
      exact Finset.sum_le_sum fun j _ ↦
        sum_hardCoordinateTail_block_le hN hpacked blocks t j
    _ ≤ 12 / (N : ℝ) := sum_six_div_prophetBlockSize_le hN

/-- Expected reward on switch instance `t`, bounded by the all-`nu` stopping probabilities
of the preceding blocks plus the explicit tail term. -/
theorem hardSwitch_reward_le {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hpacked : prophetBlockStart N L ≤ m)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (policy : ProphetPolicy m) (t : Fin L) :
    prophetExpectedReward policy
        (prophetSwitchLaws m N L (hardBlockPairs blocks) t) ≤
      3 * (∑ j : Fin L, if j ≤ t then
          (prophetBlockSize N j.1 : ℝ) *
            prophetBlockStopProbability policy
              (disclosedProfile (prophetAllNuLaws m N L (hardBlockPairs blocks)))
              (prophetAllNuLaws m N L (hardBlockPairs blocks)) N j.1
        else 0) + 3 + 12 / (N : ℝ) := by
  let lawsS := prophetSwitchLaws m N L (hardBlockPairs blocks) t
  let lawsJ := prophetAllNuLaws m N L (hardBlockPairs blocks)
  let profile := disclosedProfile lawsJ
  let p : Fin m → ℝ := fun i ↦
    ∫ x, prophetSelectProbability policy profile i x
      ∂(independentValues lawsS : Measure _)
  have hfirst : HasFiniteFirstMoments lawsS := hardSwitch_hasFiniteFirstMoments blocks t
  have hprofile : disclosedProfile lawsS = profile := by
    exact disclosedProfile_prophetSwitch_eq_allNu (hardBlockPairs blocks) t
  have hcoord : ∀ i : Fin m,
      (∫ x, (x i : ℝ) * prophetSelectProbability policy profile i x
          ∂(independentValues lawsS : Measure _)) ≤
        (hardCoordinateCap blocks t i : ℝ) * p i + hardCoordinateTail blocks t i := by
    intro i
    exact coordinate_reward_le_cap_mul_stop_add_tail policy profile lawsS hfirst i
      (hardCoordinateCap blocks t i) (hardCoordinateThreshold blocks i)
      (hardCoordinate_gap blocks t i)
  have hpnonneg : ∀ i, 0 ≤ p i := fun i ↦ integral_nonneg fun x ↦
    prophetSelectProbability_nonneg policy profile i x
  have hpsum : (∑ i : Fin m, p i) ≤ 1 :=
    sum_integral_prophetSelectProbability_le_one policy profile lawsS
  let c : Fin L → ℝ := fun j ↦
    if j ≤ t then 3 * (prophetBlockSize N j.1 : ℝ) else 0
  have hcap_pointwise : ∀ i : Fin m,
      (hardCoordinateCap blocks t i : ℝ) * p i ≤
        3 * p i +
          match prophetBlockOf N L i.1 with
          | none => 0
          | some j => c j * p i := by
    intro i
    cases hblock : prophetBlockOf N L i.1 with
    | none => simp [hardCoordinateCap, hblock]
    | some j =>
        by_cases hjt : j ≤ t
        · simp only [hardCoordinateCap, hblock, hjt, ↓reduceIte, c]
          have hp0 := hpnonneg i
          have hn0 : (0 : ℝ) ≤ prophetBlockSize N j.1 := by positivity
          norm_num [Nat.cast_mul]
          nlinarith
        · simp [hardCoordinateCap, hblock, hjt, c]
  have hcap : (∑ i : Fin m, (hardCoordinateCap blocks t i : ℝ) * p i) ≤
      3 + ∑ j : Fin L, c j *
        prophetBlockStopProbability policy profile lawsJ N j.1 := by
    calc
      (∑ i : Fin m, (hardCoordinateCap blocks t i : ℝ) * p i) ≤
          ∑ i : Fin m, (3 * p i +
            match prophetBlockOf N L i.1 with
            | none => 0
            | some j => c j * p i) :=
        Finset.sum_le_sum fun i _ ↦ hcap_pointwise i
      _ = 3 * (∑ i : Fin m, p i) +
          ∑ i : Fin m, (match prophetBlockOf N L i.1 with
            | none => 0
            | some j => c j * p i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 3 + ∑ i : Fin m, (match prophetBlockOf N L i.1 with
            | none => 0
            | some j => c j * p i) := by
        have hthree : 3 * (∑ i : Fin m, p i) ≤ 3 := by nlinarith
        linarith
      _ = 3 + ∑ j : Fin L, c j *
          prophetBlockStopProbability policy profile lawsS N j.1 := by
        change 3 + (∑ i : Fin m, match prophetBlockOf N L i.1 with
          | none => 0
          | some j => c j * p i) =
            3 + ∑ j : Fin L, c j *
              (∑ i ∈ prophetBlockIndices m N j.1, p i)
        congr 1
        exact (sum_weighted_blocks_eq hN c p).symm
      _ = 3 + ∑ j : Fin L, c j *
          prophetBlockStopProbability policy profile lawsJ N j.1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjt : j ≤ t
        · rw [prophetBlockStopProbability_switch_eq_allNu hN
            (hardBlockPairs blocks) policy hjt]
        · simp [c, hjt]
  rw [prophetExpectedReward_eq_sum_selectProbability policy lawsS hfirst, hprofile]
  calc
    (∑ i : Fin m, ∫ x, (x i : ℝ) *
        prophetSelectProbability policy profile i x
        ∂(independentValues lawsS : Measure _)) ≤
        ∑ i : Fin m, ((hardCoordinateCap blocks t i : ℝ) * p i +
          hardCoordinateTail blocks t i) :=
      Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = (∑ i : Fin m, (hardCoordinateCap blocks t i : ℝ) * p i) +
        ∑ i : Fin m, hardCoordinateTail blocks t i := Finset.sum_add_distrib
    _ ≤ (3 + ∑ j : Fin L, c j *
          prophetBlockStopProbability policy profile lawsJ N j.1) +
        12 / (N : ℝ) := add_le_add hcap
      (sum_hardCoordinateTail_le hN hpacked blocks t)
    _ = 3 * (∑ j : Fin L, if j ≤ t then
          (prophetBlockSize N j.1 : ℝ) *
            prophetBlockStopProbability policy profile lawsJ N j.1 else 0) +
        3 + 12 / (N : ℝ) := by
      have hc : (∑ j : Fin L, c j *
          prophetBlockStopProbability policy profile lawsJ N j.1) =
          3 * (∑ j : Fin L, if j ≤ t then
            (prophetBlockSize N j.1 : ℝ) *
              prophetBlockStopProbability policy profile lawsJ N j.1 else 0) := by
        dsimp only [c]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjt : j ≤ t <;> simp [hjt] <;> ring
      rw [hc]
      ring

/-- The dyadically weighted average reward of all switch instances is bounded by the
explicit numerator used in the manuscript.  This is the internal averaging step: it uses
only causality of the policy, the block tails, and that a policy stops with probability at
most one. -/
theorem weighted_hardSwitch_reward_le {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hpacked : prophetBlockStart N L ≤ m)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (policy : ProphetPolicy m) :
    (∑ t : Fin L, dyadicSwitchWeight t.1 *
      prophetExpectedReward policy
        (prophetSwitchLaws m N L (hardBlockPairs blocks) t)) ≤
      6 * (N : ℝ) + 3 + 12 / (N : ℝ) := by
  let lawsJ := prophetAllNuLaws m N L (hardBlockPairs blocks)
  let profile := disclosedProfile lawsJ
  let a : Fin L → ℝ := fun j ↦
    prophetBlockStopProbability policy profile lawsJ N j.1
  let S : Fin L → ℝ := fun t ↦
    ∑ j : Fin L, if j ≤ t then (prophetBlockSize N j.1 : ℝ) * a j else 0
  let c₀ : ℝ := 3 + 12 / (N : ℝ)
  have ha : ∀ j, 0 ≤ a j := fun j ↦
    prophetBlockStopProbability_nonneg policy profile lawsJ N j.1
  have hasum : (∑ j : Fin L, a j) ≤ 1 :=
    sum_prophetBlockStopProbability_le_one hN policy profile lawsJ
  have hR : ∀ t : Fin L,
      prophetExpectedReward policy
          (prophetSwitchLaws m N L (hardBlockPairs blocks) t) ≤ 3 * S t + c₀ := by
    intro t
    dsimp only [S, a, c₀, profile, lawsJ]
    have ht := hardSwitch_reward_le hN hpacked blocks policy t
    nlinarith
  have hweighted :
      (∑ t : Fin L, dyadicSwitchWeight t.1 *
        prophetExpectedReward policy
          (prophetSwitchLaws m N L (hardBlockPairs blocks) t)) ≤
        ∑ t : Fin L, dyadicSwitchWeight t.1 * (3 * S t + c₀) := by
    exact Finset.sum_le_sum fun t _ ↦
      mul_le_mul_of_nonneg_left (hR t) (dyadicSwitchWeight_pos t.1).le
  have hswap :
      (∑ t : Fin L, dyadicSwitchWeight t.1 * S t) =
        ∑ j : Fin L, (prophetBlockSize N j.1 : ℝ) * a j *
          (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t.1 else 0) := by
    simp only [S]
    calc
      (∑ t : Fin L, dyadicSwitchWeight t.1 *
          ∑ j : Fin L, if j ≤ t then
            (prophetBlockSize N j.1 : ℝ) * a j else 0) =
          ∑ t : Fin L, ∑ j : Fin L, dyadicSwitchWeight t.1 *
            (if j ≤ t then (prophetBlockSize N j.1 : ℝ) * a j else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
      _ = ∑ j : Fin L, ∑ t : Fin L, dyadicSwitchWeight t.1 *
            (if j ≤ t then (prophetBlockSize N j.1 : ℝ) * a j else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin L, (prophetBlockSize N j.1 : ℝ) * a j *
          (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t.1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hjt : j ≤ t <;> simp [hjt] <;> ring
  have hsize (j : Fin L) :
      (prophetBlockSize N j.1 : ℝ) * (1 / 2 : ℝ) ^ j.1 = N := by
    simp only [prophetBlockSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (N : ℝ) * 2 ^ j.1 * (1 / 2 : ℝ) ^ j.1 =
          (N : ℝ) * ((2 : ℝ) * (1 / 2 : ℝ)) ^ j.1 := by
        rw [mul_pow]
        ring
      _ = N := by simp
  have hterm (j : Fin L) :
      (prophetBlockSize N j.1 : ℝ) * a j *
          (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t.1 else 0) ≤
        (N : ℝ) * a j := by
    have htail := dyadicSwitchWeight_tail_le j
    have hcoef : 0 ≤ (prophetBlockSize N j.1 : ℝ) * a j :=
      mul_nonneg (Nat.cast_nonneg _) (ha j)
    have hmul := mul_le_mul_of_nonneg_left htail hcoef
    calc
      (prophetBlockSize N j.1 : ℝ) * a j *
          (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t.1 else 0) ≤
        (prophetBlockSize N j.1 : ℝ) * a j * (1 / 2 : ℝ) ^ j.1 := hmul
      _ = (N : ℝ) * a j := by rw [← hsize j]; ring
  have hdouble : (∑ t : Fin L, dyadicSwitchWeight t.1 * S t) ≤ (N : ℝ) := by
    rw [hswap]
    calc
      (∑ j : Fin L, (prophetBlockSize N j.1 : ℝ) * a j *
          (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t.1 else 0)) ≤
          ∑ j : Fin L, (N : ℝ) * a j :=
        Finset.sum_le_sum fun j _ ↦ hterm j
      _ = (N : ℝ) * ∑ j : Fin L, a j := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hasum (Nat.cast_nonneg N)
      _ = (N : ℝ) := mul_one _
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀]
    positivity
  have hwSum := sum_dyadicSwitchWeight_le_one L
  have hdecomp :
      (∑ t : Fin L, dyadicSwitchWeight t.1 * (3 * S t + c₀)) =
        3 * (∑ t : Fin L, dyadicSwitchWeight t.1 * S t) +
          c₀ * (∑ t : Fin L, dyadicSwitchWeight t.1) := by
    calc
      (∑ t : Fin L, dyadicSwitchWeight t.1 * (3 * S t + c₀)) =
          ∑ t : Fin L, (3 * (dyadicSwitchWeight t.1 * S t) +
            c₀ * dyadicSwitchWeight t.1) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = 3 * (∑ t : Fin L, dyadicSwitchWeight t.1 * S t) +
          c₀ * (∑ t : Fin L, dyadicSwitchWeight t.1) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hdecomp] at hweighted
  have hcpart : c₀ * (∑ t : Fin L, dyadicSwitchWeight t.1) ≤ c₀ := by
    simpa using mul_le_mul_of_nonneg_left hwSum hc₀
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  dsimp only [c₀] at hweighted hcpart ⊢
  nlinarith

/-- Every policy has a switch instance on which its reward satisfies the explicit
multiplication-form upper guarantee.  No benchmark division is used. -/
theorem exists_hardSwitch_policy_upper {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hL : 1 ≤ L) (hpacked : prophetBlockStart N L ≤ m)
    (hrm : r ≤ m) (hkappa : 0 < kappa)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa)
    (policy : ProphetPolicy m) :
    ∃ t : Fin L,
      prophetExpectedReward policy
          (prophetSwitchLaws m N L (hardBlockPairs blocks) t) ≤
        (2 * (6 * (N : ℝ) + 3 + 12 / (N : ℝ)) /
            (3 * kappa * (N : ℝ) * (L : ℝ))) *
          orderStatisticBenchmark
            (⟨r, (blocks t).hr, hrm⟩ : ValidRank m)
            (prophetSwitchLaws m N L (hardBlockPairs blocks) t) := by
  let R : Fin L → ℝ := fun t ↦
    prophetExpectedReward policy
      (prophetSwitchLaws m N L (hardBlockPairs blocks) t)
  let Q : Fin L → ℝ := fun t ↦
    orderStatisticBenchmark (⟨r, (blocks t).hr, hrm⟩ : ValidRank m)
      (prophetSwitchLaws m N L (hardBlockPairs blocks) t)
  let A : ℝ := 6 * (N : ℝ) + 3 + 12 / (N : ℝ)
  let C : ℝ := 2 * A / (3 * kappa * (N : ℝ) * (L : ℝ))
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hden : 0 < 3 * kappa * (N : ℝ) * (L : ℝ) := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hRsum : (∑ t : Fin L, dyadicSwitchWeight t.1 * R t) ≤ A := by
    simpa [R, A] using weighted_hardSwitch_reward_le hN hpacked blocks policy
  have hQpoint : ∀ t : Fin L,
      3 * kappa * ((N : ℝ) * (2 : ℝ) ^ t.1) ≤ Q t := by
    intro t
    dsimp only [Q]
    simpa [prophetBlockSize, Nat.cast_mul, Nat.cast_pow] using
      hardSwitch_benchmark_lower hN hpacked hrm blocks t
  have hQsum : 3 * kappa * (N : ℝ) * (L : ℝ) / 2 ≤
      ∑ t : Fin L, dyadicSwitchWeight t.1 * Q t :=
    weighted_dyadic_benchmark_lower (N : ℝ) kappa Q hQpoint
  have hcalgebra :
      C * (3 * kappa * (N : ℝ) * (L : ℝ) / 2) = A := by
    dsimp only [C]
    field_simp
  have hAupper : A ≤ C * ∑ t : Fin L, dyadicSwitchWeight t.1 * Q t := by
    rw [← hcalgebra]
    exact mul_le_mul_of_nonneg_left hQsum hC
  have hsum : (∑ t : Fin L, dyadicSwitchWeight t.1 * R t) ≤
      C * ∑ t : Fin L, dyadicSwitchWeight t.1 * Q t := hRsum.trans hAupper
  obtain ⟨t, ht⟩ := exists_pointwise_le_of_weighted_sum_le hL
    (fun t : Fin L ↦ dyadicSwitchWeight t.1) R Q C
    (fun t ↦ dyadicSwitchWeight_pos t.1) hsum
  exact ⟨t, ht⟩

/-- A concrete collection of separator blocks bounds the universal robust constant.  The
proof applies the guarantee to the adversarial switch instance and cancels only after proving
that its benchmark is strictly positive. -/
theorem rhoMom_le_of_hardBlocks {m N L r : ℕ} {kappa : ℝ}
    (hN : 0 < N) (hL : 1 ≤ L) (hpacked : prophetBlockStart N L ≤ m)
    (hr : 1 ≤ r) (hrm : r ≤ m) (hkappa : 0 < kappa)
    (blocks : ∀ j : Fin L, ProphetHardBlock r (prophetBlockSize N j.1) kappa) :
    rhoMom (⟨r, hr, hrm⟩ : ValidRank m) ≤
      2 * (6 * (N : ℝ) + 3 + 12 / (N : ℝ)) /
        (3 * kappa * (N : ℝ) * (L : ℝ)) := by
  let rank : ValidRank m := ⟨r, hr, hrm⟩
  let C : ℝ := 2 * (6 * (N : ℝ) + 3 + 12 / (N : ℝ)) /
    (3 * kappa * (N : ℝ) * (L : ℝ))
  apply csSup_le (prophetFeasibleSet_nonempty rank)
  intro alpha halpha
  obtain ⟨halpha0, policy, hpolicy⟩ := halpha
  obtain ⟨t, ht⟩ := exists_hardSwitch_policy_upper hN hL hpacked hrm hkappa blocks policy
  let laws := prophetSwitchLaws m N L (hardBlockPairs blocks) t
  have hfinite : ∀ i, HasFiniteMoments (laws i) := fun i ↦
    prophetSwitchLaws_hasFiniteMoments (hardBlockPairs blocks) t i
  have hguarantee : alpha * orderStatisticBenchmark rank laws ≤
      prophetExpectedReward policy laws := hpolicy laws hfinite
  have hqLower : 3 * kappa * (prophetBlockSize N t.1 : ℝ) ≤
      orderStatisticBenchmark rank laws := by
    simpa [rank, laws] using hardSwitch_benchmark_lower hN hpacked hrm blocks t
  have hqpos : 0 < orderStatisticBenchmark rank laws := by
    have hsize : (0 : ℝ) < prophetBlockSize N t.1 := by
      exact_mod_cast Nat.mul_pos hN (pow_pos (by omega : 0 < 2) t.1)
    exact lt_of_lt_of_le (by positivity :
      0 < 3 * kappa * (prophetBlockSize N t.1 : ℝ)) hqLower
  have hupper : prophetExpectedReward policy laws ≤
      C * orderStatisticBenchmark rank laws := by
    simpa [C, rank, laws] using ht
  have hmul : alpha * orderStatisticBenchmark rank laws ≤
      C * orderStatisticBenchmark rank laws := hguarantee.trans hupper
  nlinarith

end

end MomentAmbiguity
