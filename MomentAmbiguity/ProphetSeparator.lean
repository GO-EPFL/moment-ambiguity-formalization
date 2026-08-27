import MomentAmbiguity.BinarySeparator
import MomentAmbiguity.ProphetHardFamily
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The binary separator as an order-statistic prophet block

This module proves the internal construction used in `cor:order-stat-separator`.  In
particular, it extracts the binomial event at the distinguished atom of the concrete binary
separator; no probabilistic lower bound is imported from the literature.
-/

open scoped ENNReal NNReal ProbabilityTheory unitInterval BigOperators

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-! ## Exact atom-count probabilities -/

/-- The probability of one atom, bundled as a unit-interval parameter. -/
def atomParameter (mu : Distribution) (a : ℝ≥0) : Set.Icc (0 : ℝ) 1 :=
  ⟨(mu : Measure ℝ≥0).real {a}, measureReal_nonneg, measureReal_le_one⟩

theorem map_atomPredicate_eq_bernoulli (mu : Distribution) (a : ℝ≥0) :
    Measure.map (fun y : ℝ≥0 ↦ y = a) (mu : Measure ℝ≥0) =
      ProbabilityTheory.bernoulliMeasure True False (atomParameter mu a) := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have hbEq : b = True := propext ⟨fun _ ↦ trivial, fun _ ↦ hb⟩
    rw [hbEq]
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton True)]
    have hpre : (fun y : ℝ≥0 ↦ y = a) ⁻¹' ({True} : Set Prop) = {a} := by
      ext y
      simp
    rw [hpre]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
    simp [atomParameter, ProbabilityTheory.bernoulliMeasure_def,
      MeasureTheory.measureReal_def]
  · have hbEq : b = False := propext ⟨fun h ↦ (hb h).elim, fun h ↦ False.elim h⟩
    rw [hbEq]
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton False)]
    have hpre : (fun y : ℝ≥0 ↦ y = a) ⁻¹' ({False} : Set Prop) = {a}ᶜ := by
      ext y
      simp
    rw [hpre]
    rw [measure_compl (MeasurableSet.singleton a) (measure_ne_top _ _)]
    rw [measure_univ]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le
      ((measure_mono (Set.subset_univ {a})).trans_eq measure_univ) (by finiteness)]
    simp [atomParameter, ProbabilityTheory.bernoulliMeasure_def,
      MeasureTheory.measureReal_def]

/-- Coordinates equal to a prescribed atom. -/
def pivotSet {n : ℕ} (a : ℝ≥0) (x : Fin n → ℝ≥0) : Set (Fin n) := {i | x i = a}

theorem measurable_pivotSet {n : ℕ} (a : ℝ≥0) : Measurable (pivotSet (n := n) a) := by
  change Measurable (fun x : Fin n → ℝ≥0 ↦ fun i ↦ x i = a)
  rw [measurable_pi_iff]
  intro i
  fun_prop

theorem map_pivotSet_eq_setBernoulli {n : ℕ} (mu : Distribution) (a : ℝ≥0) :
    Measure.map (pivotSet a) (Measure.pi (fun _ : Fin n ↦ (mu : Measure ℝ≥0))) =
      ProbabilityTheory.setBernoulli Set.univ (atomParameter mu a) := by
  let p := atomParameter mu a
  let coin : Measure Prop := ProbabilityTheory.bernoulliMeasure True False p
  have hcoord (i : Fin n) : MeasurePreserving (fun y : ℝ≥0 ↦ y = a)
      (mu : Measure ℝ≥0) coin := by
    refine ⟨by fun_prop, ?_⟩
    simpa [coin, p] using map_atomPredicate_eq_bernoulli mu a
  have hpi := MeasureTheory.measurePreserving_pi
    (fun _ : Fin n ↦ (mu : Measure ℝ≥0)) (fun _ : Fin n ↦ coin) hcoord
  calc
    Measure.map (pivotSet a) (Measure.pi (fun _ : Fin n ↦ (mu : Measure ℝ≥0))) =
        Measure.map MeasurableEquiv.setOf
          (Measure.map (fun x : Fin n → ℝ≥0 ↦ fun i ↦ x i = a)
            (Measure.pi (fun _ : Fin n ↦ (mu : Measure ℝ≥0)))) := by
      rw [Measure.map_map MeasurableEquiv.setOf.measurable hpi.measurable]
      rfl
    _ = Measure.map MeasurableEquiv.setOf (Measure.pi (fun _ : Fin n ↦ coin)) := by
      rw [hpi.map_eq]
    _ = ProbabilityTheory.setBernoulli Set.univ (atomParameter mu a) := by
      rw [ProbabilityTheory.setBernoulli_eq_map, Measure.infinitePi_eq_pi]
      congr 2

/-- Number of coordinates equal to the pivot. -/
def pivotCount {n : ℕ} (a : ℝ≥0) (x : Fin n → ℝ≥0) : ℕ :=
  (pivotSet a x).ncard

theorem measurable_pivotCount {n : ℕ} (a : ℝ≥0) :
    Measurable (pivotCount (n := n) a) :=
  measurable_ncard.comp (measurable_pivotSet a)

/-- Exact binomial probability of seeing the pivot exactly `r` times. -/
theorem pivotCount_probability_exact {n r : ℕ} (mu : Distribution) (a : ℝ≥0) :
    ((independentValues (fun _ : Fin n ↦ mu) : ProbabilityMeasure (ProphetPath n)) :
        Measure (ProphetPath n)).real
        {x | pivotCount a x = r} =
      (n.choose r : ℝ) * (atomParameter mu a : ℝ) ^ r *
        (1 - (atomParameter mu a : ℝ)) ^ (n - r) := by
  rw [independentValues, ProbabilityMeasure.toMeasure_pi]
  let P : Measure (Fin n → ℝ≥0) := Measure.pi (fun _ : Fin n ↦ (mu : Measure ℝ≥0))
  let p := atomParameter mu a
  have hmap : Measure.map (pivotCount a) P =
      (ProbabilityTheory.setBernoulli (Set.univ : Set (Fin n)) p).map Set.ncard := by
    calc
      Measure.map (pivotCount a) P =
          Measure.map Set.ncard (Measure.map (pivotSet a) P) := by
        rw [Measure.map_map measurable_ncard (measurable_pivotSet a)]
        rfl
      _ = _ := by rw [map_pivotSet_eq_setBernoulli]
  calc
    P.real {x | pivotCount a x = r} = (Measure.map (pivotCount a) P).real {r} := by
      rw [MeasureTheory.map_measureReal_apply (measurable_pivotCount a) (by measurability)]
      rfl
    _ = ((ProbabilityTheory.setBernoulli (Set.univ : Set (Fin n)) p).map Set.ncard).real
        {r} := by rw [hmap]
    _ = (((Set.univ : Set (Fin n)).ncard.choose r : ℕ) : ℝ) * (p : ℝ) ^ r *
        (1 - (p : ℝ)) ^ ((Set.univ : Set (Fin n)).ncard - r) := by
      exact ProbabilityTheory.map_ncard_setBernoulli_real_singleton Set.finite_univ p r
    _ = _ := by simp [P, p]

/-! ## Explicit binomial lower bound -/

/-- The manuscript's explicit constant in `cor:order-stat-separator`. -/
def orderStatisticKappa (r : ℕ) : ℝ :=
  Real.exp (-(1 : ℝ) / 4) / ((8 : ℝ) ^ r * (r.factorial : ℝ))

theorem choose_lower_half {n r : ℕ} (hn : 2 * r ≤ n) :
    ((n : ℝ) / 2) ^ r / (r.factorial : ℝ) ≤ (n.choose r : ℝ) := by
  have hrn : r ≤ n + 1 := by omega
  have hbaseNat : n ≤ 2 * (n + 1 - r) := by omega
  have hbase : (n : ℝ) / 2 ≤ (n + 1 - r : ℕ) := by
    have hcast : (n : ℝ) ≤ 2 * (n + 1 - r : ℕ) := by exact_mod_cast hbaseNat
    linarith
  have hpow : ((n : ℝ) / 2) ^ r ≤ ((n + 1 - r : ℕ) : ℝ) ^ r :=
    pow_le_pow_left₀ (by positivity) hbase r
  calc
    ((n : ℝ) / 2) ^ r / (r.factorial : ℝ) ≤
        (((n + 1 - r : ℕ) : ℝ) ^ r) / (r.factorial : ℝ) := by
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ (n.choose r : ℝ) := Nat.pow_le_choose r n

theorem binomialKernel_hasDeriv {n r : ℕ} (hr : 1 ≤ r) (hnr : 1 ≤ n - r) (x : ℝ) :
    HasDerivAt (fun z : ℝ ↦ z ^ r * (1 - z) ^ (n - r))
      (x ^ (r - 1) * (1 - x) ^ (n - r - 1) * ((r : ℝ) - n * x)) x := by
  have hpow1 : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hpow2 : n - r - 1 + 1 = n - r := Nat.sub_add_cancel hnr
  convert ((hasDerivAt_id x).pow r).mul
    (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).pow (n - r)) using 1 <;> try rfl
  simp only [id_eq, Pi.pow_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply,
    one_mul, zero_sub]
  rw [show x ^ r = x ^ (r - 1) * x by rw [← pow_succ, hpow1],
    show (1 - x) ^ (n - r) = (1 - x) ^ (n - r - 1) * (1 - x) by
      rw [← pow_succ, hpow2]]
  rw [Nat.cast_sub (by omega : r ≤ n)]
  ring

theorem binomialKernel_mono {n r : ℕ} (hr : 1 ≤ r) (hn : 2 * r ≤ n)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1 / (n : ℝ)) :
    p ^ r * (1 - p) ^ (n - r) ≤ q ^ r * (1 - q) ^ (n - r) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2 * r) hn)
  have hnr : 1 ≤ n - r := by omega
  let f : ℝ → ℝ := fun z ↦ z ^ r * (1 - z) ^ (n - r)
  have hmono : MonotoneOn f (Set.Icc 0 (1 / (n : ℝ))) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / (n : ℝ)))
    · fun_prop
    · intro x hx
      exact (binomialKernel_hasDeriv hr hnr x).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := hx.1.le
      have hx1 : x ≤ 1 / (n : ℝ) := hx.2.le
      have hone : 0 ≤ 1 - x := by
        have : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one₀ hnpos]
          exact_mod_cast (show 1 ≤ n by omega)
        linarith
      have hbracket : 0 ≤ (r : ℝ) - n * x := by
        have hnx : (n : ℝ) * x ≤ 1 := by
          have := (le_div_iff₀ hnpos).mp hx1
          nlinarith
        have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
        linarith
      positivity
  apply hmono
  · exact ⟨hp, hpq.trans hq⟩
  · exact ⟨hp.trans hpq, hq⟩
  · exact hpq

theorem binomialSurvival_lower {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n) :
    Real.exp (-(1 : ℝ) / 4) ≤ (1 - 1 / (4 * (n : ℝ))) ^ (n - r) := by
  let x : ℝ := 1 / (4 * (n : ℝ))
  let y : ℝ := 1 - x
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxlt : x < 1 := by
    dsimp [x]
    rw [div_lt_one₀ (by positivity : (0 : ℝ) < 4 * n)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hypos : 0 < y := by dsimp [y]; linarith
  have hlog : -x / y ≤ Real.log y := by
    have h := Real.one_sub_inv_le_log_of_pos hypos
    have hid : -x / y = 1 - y⁻¹ := by
      have hne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hxlt)
      dsimp [y]
      rw [div_eq_iff hne]
      field_simp [hne]
      ring
    rw [hid]
    exact h
  have hratio : ((n - r : ℕ) : ℝ) * (x / y) ≤ 1 / 4 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : (0 : ℝ) < 4 * n - 1 := by nlinarith
    have hxy : x / y = 1 / (4 * (n : ℝ) - 1) := by
      dsimp [x, y]
      field_simp
    rw [hxy, mul_one_div]
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
    norm_num
    have hkNat : n - r ≤ n - 1 := by omega
    have hk : ((n - r : ℕ) : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hkNat
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast] at hk
    nlinarith
  have hexpArg : -(1 : ℝ) / 4 ≤ ((n - r : ℕ) : ℝ) * Real.log y := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (n - r : ℕ))
    have hneg : -(1 : ℝ) / 4 ≤ ((n - r : ℕ) : ℝ) * (-x / y) := by
      calc
        -(1 : ℝ) / 4 = -(1 / 4) := by ring
        _ ≤ -(((n - r : ℕ) : ℝ) * (x / y)) := neg_le_neg hratio
        _ = ((n - r : ℕ) : ℝ) * (-x / y) := by ring
    exact hneg.trans hmul
  calc
    Real.exp (-(1 : ℝ) / 4) ≤ Real.exp (((n - r : ℕ) : ℝ) * Real.log y) :=
      (Real.exp_le_exp).2 hexpArg
    _ = Real.exp (Real.log y) ^ (n - r) := Real.exp_nat_mul _ _
    _ = y ^ (n - r) := by rw [Real.exp_log hypos]
    _ = (1 - 1 / (4 * (n : ℝ))) ^ (n - r) := rfl

/-! ## The gap below the first tail atom -/

theorem measurableSet_evenSupport (n B : ℕ) :
    MeasurableSet (BinarySeparator.evenSupport n B) :=
  ((Set.countable_range (BinarySeparator.nodeNN n B)).mono (by
    rintro x ⟨j, _hj, rfl⟩
    exact ⟨j, rfl⟩)).measurableSet

theorem measurableSet_oddSupport (n B : ℕ) :
    MeasurableSet (BinarySeparator.oddSupport n B) :=
  ((Set.countable_range (BinarySeparator.nodeNN n B)).mono (by
    rintro x ⟨j, _hj, rfl⟩
    exact ⟨j, rfl⟩)).measurableSet

theorem nuLaw_ae_mem_evenSupport {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    ∀ᵐ x ∂(BinarySeparator.nuLaw n B hn hB : Measure ℝ≥0),
      x ∈ BinarySeparator.evenSupport n B := by
  exact (mem_ae_iff_prob_eq_one (measurableSet_evenSupport n B)).2
    (BinarySeparator.nuLaw_support hn hB)

theorem muLaw_ae_mem_oddSupport {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    ∀ᵐ x ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0),
      x ∈ BinarySeparator.oddSupport n B := by
  exact (mem_ae_iff_prob_eq_one (measurableSet_oddSupport n B)).2
    (BinarySeparator.muLaw_support hn hB)

/-- The `ν` non-tail gap in `cor:order-stat-separator`. -/
theorem nuLaw_gap_below_node_three {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    ∀ᵐ x ∂(BinarySeparator.nuLaw n B hn hB : Measure ℝ≥0),
      x < BinarySeparator.nodeNN n B 3 → x ≤ BinarySeparator.nodeNN n B 2 := by
  filter_upwards [nuLaw_ae_mem_evenSupport hn hB] with x hx
  rintro hbelow
  rcases hx with ⟨j, _hj, rfl⟩
  have hj : j < 3 := by
    apply (BinarySeparator.node_strictMono hn hB).lt_iff_lt.mp
    exact_mod_cast hbelow
  have hmono := (BinarySeparator.node_strictMono hn hB).monotone (show j ≤ 2 by omega)
  exact_mod_cast hmono

/-- The `μ` non-tail gap in `cor:order-stat-separator`. -/
theorem muLaw_gap_below_node_three {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    ∀ᵐ x ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0),
      x < BinarySeparator.nodeNN n B 3 → x ≤ BinarySeparator.nodeNN n B 1 := by
  filter_upwards [muLaw_ae_mem_oddSupport hn hB] with x hx
  rintro hbelow
  rcases hx with ⟨j, hjodd, rfl⟩
  have hj : j < 3 := by
    apply (BinarySeparator.node_strictMono hn hB).lt_iff_lt.mp
    exact_mod_cast hbelow
  rcases hjodd with ⟨k, hk⟩
  have hjeq : j = 1 := by omega
  rw [hjeq]

/-! ## The explicit `6/n` tail bound -/

theorem tsum_inv_node_tail_le {n B q : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hq : 2 ≤ q) :
    (∑' r : ℕ, 1 / BinarySeparator.node n B (q + r)) ≤
      2 / BinarySeparator.node n B q := by
  have hsum : Summable (fun r : ℕ ↦ 1 / BinarySeparator.node n B (q + r)) := by
    have h := (BinarySeparator.summable_inv_node hn hB).comp_injective
      (add_right_injective q)
    simpa only [Function.comp_def] using h
  apply le_of_tendsto hsum.tendsto_sum_tsum_nat
  exact Filter.Eventually.of_forall fun K ↦
    BinarySeparator.sum_inv_node_tail_le hn hB hq

theorem nuPMF_toReal_le_abs_limitWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (j : ℕ) :
    (BinarySeparator.nuPMF n B hn hB j).toReal ≤
      |BinarySeparator.limitWeight n B j| / BinarySeparator.normalizer n B := by
  rw [BinarySeparator.nuPMF_toReal]
  apply div_le_div_of_nonneg_right _ (BinarySeparator.normalizer_pos hn hB).le
  rcases Nat.even_or_odd j with hj | hj
  · rw [BinarySeparator.evenWeight_of_even hj,
      abs_of_nonneg (BinarySeparator.limitWeight_nonneg_of_even hn hB hj)]
  · simp [BinarySeparator.evenWeight_of_odd hj]

theorem muPMF_toReal_le_abs_limitWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (j : ℕ) :
    (BinarySeparator.muPMF n B hn hB j).toReal ≤
      |BinarySeparator.limitWeight n B j| / BinarySeparator.normalizer n B := by
  rw [BinarySeparator.muPMF_toReal]
  apply div_le_div_of_nonneg_right _ (BinarySeparator.normalizer_pos hn hB).le
  rcases Nat.even_or_odd j with hj | hj
  · simp [BinarySeparator.oddWeight_of_even hj]
  · rw [BinarySeparator.oddWeight_of_odd hj,
      abs_of_nonpos (BinarySeparator.limitWeight_nonpos_of_odd hn hB hj)]

/-- Common tail-series estimate for either parity-normalized PMF. -/
theorem canonical_tail_tsum_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (p : PMF ℕ)
    (hmass : ∀ j, (p j).toReal ≤
      |BinarySeparator.limitWeight n B j| / BinarySeparator.normalizer n B) :
    (∑' j : ℕ, (p j).toReal *
        upperTailValue (BinarySeparator.nodeNN n B 3) (BinarySeparator.nodeNN n B j)) ≤
      16 * (n * B : ℝ) ^ 2 /
        ((n : ℝ) * BinarySeparator.node n B 3) := by
  let A : ℝ := 8 * (n * B : ℝ) ^ 2 / (n : ℝ)
  let term : ℕ → ℝ := fun j ↦ (p j).toReal *
    upperTailValue (BinarySeparator.nodeNN n B 3) (BinarySeparator.nodeNN n B j)
  let major : ℕ → ℝ := fun j ↦ A * (1 / BinarySeparator.node n B j)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmajorSum : Summable major :=
    (BinarySeparator.summable_inv_node hn hB).mul_left A
  have htermNonneg : ∀ j, 0 ≤ term j := fun j ↦ by
    dsimp only [term]
    exact mul_nonneg ENNReal.toReal_nonneg
      (upperTailValue_nonneg _ _)
  have htermMajor : ∀ j, term j ≤ major j := by
    intro j
    let x : ℝ := BinarySeparator.node n B j
    let W : ℝ := BinarySeparator.normalizer n B
    let w : ℝ := |BinarySeparator.limitWeight n B j|
    have hx : 0 < x := BinarySeparator.node_pos hn hB j
    have hWn : (n : ℝ) ≤ W := BinarySeparator.n_le_normalizer hn hB
    have hW : 0 < W := BinarySeparator.normalizer_pos hn hB
    have hp0 : 0 ≤ (p j).toReal := ENNReal.toReal_nonneg
    have htail0 : 0 ≤ upperTailValue (BinarySeparator.nodeNN n B 3)
        (BinarySeparator.nodeNN n B j) := upperTailValue_nonneg _ _
    have htail : upperTailValue (BinarySeparator.nodeNN n B 3)
        (BinarySeparator.nodeNN n B j) ≤ x := by
      simpa only [x, BinarySeparator.node] using
        upperTailValue_le_cast (BinarySeparator.nodeNN n B 3)
          (BinarySeparator.nodeNN n B j)
    have hp : (p j).toReal ≤ w / W := by simpa only [w, W] using hmass j
    have hrecip : w / W ≤ w / (n : ℝ) := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) hnpos hWn
    have hw : w ≤ 8 * (n * B : ℝ) ^ 2 / x ^ 2 := by
      simpa only [w, x] using BinarySeparator.limitWeight_decay_two
        (n := n) (B := B) (j := j) hn hB
    calc
      term j ≤ (w / W) * x := by
        dsimp only [term]
        exact mul_le_mul hp htail htail0 (div_nonneg (abs_nonneg _) hW.le)
      _ ≤ (w / (n : ℝ)) * x :=
        mul_le_mul_of_nonneg_right hrecip hx.le
      _ ≤ ((8 * (n * B : ℝ) ^ 2 / x ^ 2) / (n : ℝ)) * x := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hw hnpos.le) hx.le
      _ = major j := by
        dsimp only [major, A, x]
        field_simp [ne_of_gt hx, ne_of_gt hnpos]
  have htermSum : Summable term :=
    hmajorSum.of_nonneg_of_le htermNonneg htermMajor
  have hsplit := htermSum.sum_add_tsum_nat_add 3
  have hprefix : (∑ j ∈ Finset.range 3, term j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j < 3 := Finset.mem_range.mp hj
    have hnot : ¬ BinarySeparator.nodeNN n B 3 ≤ BinarySeparator.nodeNN n B j := by
      exact not_le_of_gt (by
        exact_mod_cast (BinarySeparator.node_strictMono hn hB hjlt))
    dsimp only [term]
    rw [upperTailValue, if_neg hnot]
    simp
  have htailMajor : (∑' r : ℕ, term (r + 3)) ≤
      ∑' r : ℕ, major (r + 3) := by
    exact (htermSum.comp_injective
      (show Function.Injective (fun r : ℕ ↦ r + 3) from
        fun _ _ hab ↦ Nat.add_right_cancel hab)).tsum_le_tsum
      (fun r ↦ htermMajor (r + 3))
      (hmajorSum.comp_injective
        (show Function.Injective (fun r : ℕ ↦ r + 3) from
          fun _ _ hab ↦ Nat.add_right_cancel hab))
  calc
    (∑' j : ℕ, (p j).toReal *
        upperTailValue (BinarySeparator.nodeNN n B 3)
          (BinarySeparator.nodeNN n B j)) = ∑' j, term j := rfl
    _ = ∑' r : ℕ, term (r + 3) := by rw [← hsplit, hprefix, zero_add]
    _ ≤ ∑' r : ℕ, major (r + 3) := htailMajor
    _ = A * (∑' r : ℕ, 1 / BinarySeparator.node n B (3 + r)) := by
      rw [tsum_mul_left]
      apply congrArg
      apply tsum_congr
      intro r
      rw [add_comm]
    _ ≤ A * (2 / BinarySeparator.node n B 3) := by
      exact mul_le_mul_of_nonneg_left (tsum_inv_node_tail_le hn hB (by omega)) hA
    _ = 16 * (n * B : ℝ) ^ 2 /
        ((n : ℝ) * BinarySeparator.node n B 3) := by
      dsimp only [A]
      field_simp [ne_of_gt hnpos, ne_of_gt (BinarySeparator.node_pos hn hB 3)]
      ring

theorem nuLaw_tailIntegral_eq_tsum {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
        ∂(BinarySeparator.nuLaw n B hn hB : Measure ℝ≥0)) =
      ∑' j : ℕ, (BinarySeparator.nuPMF n B hn hB j).toReal *
        upperTailValue (BinarySeparator.nodeNN n B 3) (BinarySeparator.nodeNN n B j) := by
  let f := upperTailValue (BinarySeparator.nodeNN n B 3)
  have hf : StronglyMeasurable f :=
    (measurable_upperTailValue (BinarySeparator.nodeNN n B 3)).stronglyMeasurable
  have hfi : Integrable (f ∘ BinarySeparator.nodeNN n B)
      (BinarySeparator.nuPMF n B hn hB).toMeasure := by
    have hmap : Integrable f
        (Measure.map (BinarySeparator.nodeNN n B)
          (BinarySeparator.nuPMF n B hn hB).toMeasure) := by
      rw [PMF.toMeasure_map (BinarySeparator.nodeNN n B)
        (BinarySeparator.nuPMF n B hn hB) (BinarySeparator.measurable_nodeNN n B)]
      exact integrable_upperTailValue _
        (BinarySeparator.hasFiniteMoments_nuLaw hn hB 1)
    exact (integrable_map_measure hf.aestronglyMeasurable
      (BinarySeparator.measurable_nodeNN n B).aemeasurable).mp hmap
  simpa only [f, smul_eq_mul, BinarySeparator.nuLaw] using
    integral_atomicLaw_eq_tsum (BinarySeparator.nuPMF n B hn hB)
      (BinarySeparator.nodeNN n B) f (BinarySeparator.measurable_nodeNN n B) hf hfi

theorem muLaw_tailIntegral_eq_tsum {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
        ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0)) =
      ∑' j : ℕ, (BinarySeparator.muPMF n B hn hB j).toReal *
        upperTailValue (BinarySeparator.nodeNN n B 3) (BinarySeparator.nodeNN n B j) := by
  let f := upperTailValue (BinarySeparator.nodeNN n B 3)
  have hf : StronglyMeasurable f :=
    (measurable_upperTailValue (BinarySeparator.nodeNN n B 3)).stronglyMeasurable
  have hfi : Integrable (f ∘ BinarySeparator.nodeNN n B)
      (BinarySeparator.muPMF n B hn hB).toMeasure := by
    have hmap : Integrable f
        (Measure.map (BinarySeparator.nodeNN n B)
          (BinarySeparator.muPMF n B hn hB).toMeasure) := by
      rw [PMF.toMeasure_map (BinarySeparator.nodeNN n B)
        (BinarySeparator.muPMF n B hn hB) (BinarySeparator.measurable_nodeNN n B)]
      exact integrable_upperTailValue _
        (BinarySeparator.hasFiniteMoments_muLaw hn hB 1)
    exact (integrable_map_measure hf.aestronglyMeasurable
      (BinarySeparator.measurable_nodeNN n B).aemeasurable).mp hmap
  simpa only [f, smul_eq_mul, BinarySeparator.muLaw] using
    integral_atomicLaw_eq_tsum (BinarySeparator.muPMF n B hn hB)
      (BinarySeparator.nodeNN n B) f (BinarySeparator.measurable_nodeNN n B) hf hfi

/-- One-coordinate tail estimate, before specializing `B=3`. -/
theorem nuLaw_tailIntegral_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
        ∂(BinarySeparator.nuLaw n B hn hB : Measure ℝ≥0)) ≤
      16 * (n * B : ℝ) ^ 2 /
        ((n : ℝ) * BinarySeparator.node n B 3) := by
  rw [nuLaw_tailIntegral_eq_tsum hn hB]
  exact canonical_tail_tsum_le hn hB (BinarySeparator.nuPMF n B hn hB)
    (nuPMF_toReal_le_abs_limitWeight hn hB)

/-- One-coordinate tail estimate, before specializing `B=3`. -/
theorem muLaw_tailIntegral_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
        ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0)) ≤
      16 * (n * B : ℝ) ^ 2 /
        ((n : ℝ) * BinarySeparator.node n B 3) := by
  rw [muLaw_tailIntegral_eq_tsum hn hB]
  exact canonical_tail_tsum_le hn hB (BinarySeparator.muPMF n B hn hB)
    (muPMF_toReal_le_abs_limitWeight hn hB)

theorem totalTail_le_six_of_integral_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    {tailIntegral : ℝ}
    (hI : tailIntegral ≤ 16 * (n * B : ℝ) ^ 2 /
      ((n : ℝ) * BinarySeparator.node n B 3)) :
    (n : ℝ) * tailIntegral ≤ 6 / (n : ℝ) := by
  let x : ℝ := (n : ℝ) * B
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hxpos : 0 < x := mul_pos hnpos hBpos
  have hxone : 1 ≤ x := by
    dsimp only [x]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
    nlinarith
  have hpow : x ^ 3 ≤ x ^ B := pow_le_pow_right₀ hxone hB
  calc
    (n : ℝ) * tailIntegral ≤ (n : ℝ) *
        (16 * (n * B : ℝ) ^ 2 /
          ((n : ℝ) * BinarySeparator.node n B 3)) :=
      mul_le_mul_of_nonneg_left hI hnpos.le
    _ = 16 * x ^ 2 / x ^ B := by
      rw [BinarySeparator.node_three]
      dsimp only [x]
      field_simp [ne_of_gt hnpos]
    _ ≤ 16 * x ^ 2 / x ^ 3 := by
      exact div_le_div_of_nonneg_left (by positivity)
        (pow_pos hxpos 3) hpow
    _ = 16 / x := by field_simp [ne_of_gt hxpos] <;> ring
    _ ≤ 6 / (n : ℝ) := by
      rw [div_le_div_iff₀ hxpos hnpos]
      dsimp only [x]
      have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
      nlinarith

/-- First explicit tail inequality in `cor:order-stat-separator`. -/
theorem nuLaw_totalTail_le_six {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (n : ℝ) *
        (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
          ∂(BinarySeparator.nuLaw n B hn hB : Measure ℝ≥0)) ≤
      6 / (n : ℝ) :=
  totalTail_le_six_of_integral_le hn hB (nuLaw_tailIntegral_le hn hB)

/-- Second explicit tail inequality in `cor:order-stat-separator`. -/
theorem muLaw_totalTail_le_six {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (n : ℝ) *
        (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
          ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0)) ≤
      6 / (n : ℝ) :=
  totalTail_le_six_of_integral_le hn hB (muLaw_tailIntegral_le hn hB)

/-- The explicit `6/n` upper-tail bound for the `ν` law at base `B=3`. -/
theorem nuLaw_three_totalTail_le {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) *
        (∫ x, upperTailValue (BinarySeparator.nodeNN n 3 3) x
          ∂(BinarySeparator.nuLaw n 3 hn (by norm_num) : Measure ℝ≥0)) ≤
      6 / (n : ℝ) := by
  exact nuLaw_totalTail_le_six hn (by norm_num)

/-- The explicit `6/n` upper-tail bound for the `μ` law at base `B=3`. -/
theorem muLaw_three_totalTail_le {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) *
        (∫ x, upperTailValue (BinarySeparator.nodeNN n 3 3) x
          ∂(BinarySeparator.muLaw n 3 hn (by norm_num) : Measure ℝ≥0)) ≤
      6 / (n : ℝ) := by
  exact muLaw_totalTail_le_six hn (by norm_num)

/-! ## The iid order-statistic lower bound -/

/-- If exactly `r` coordinates equal `a`, then the `r`-th largest coordinate is at least
`a`.  Multiplicity is retained because the selected object is a finset of indices. -/
theorem le_descendingOrderStatistic_of_pivotCount_eq {n r : ℕ}
    (rank : ValidRank n) (hrank : rank.1 = r) (a : ℝ≥0) (x : ProphetPath n)
    (hcount : pivotCount a x = r) :
    a ≤ descendingOrderStatistic rank x := by
  let s : Finset (Fin n) := Finset.univ.filter fun i ↦ x i = a
  have hset : (s : Set (Fin n)) = pivotSet a x := by
    ext i
    simp [s, pivotSet]
  have hcard : s.card = r := by
    rw [← Set.ncard_coe_finset, hset]
    exact hcount
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hsrank : s ∈ rankSubsets rank := by
    rw [rankSubsets, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ s, by simpa [hrank] using hcard⟩
  have hminimum : a ≤ subsetMinimum x s := by
    rw [subsetMinimum, dif_pos hsne]
    apply Finset.le_inf'
    intro i hi
    have hia : x i = a := (Finset.mem_filter.mp hi).2
    exact hia.ge
  rw [descendingOrderStatistic]
  exact hminimum.trans (Finset.le_sup' _ hsrank)

/-- The distinguished `ν` atom has probability in the interval used by the binomial
calculation. -/
theorem nuLaw_three_pivot_probability_bounds {n : ℕ} (hn : 3 ≤ n) :
    1 / (4 * (n : ℝ)) ≤
        (atomParameter (BinarySeparator.nuLaw n 3 hn (by norm_num))
          (BinarySeparator.nodeNN n 3 2) : ℝ) ∧
      (atomParameter (BinarySeparator.nuLaw n 3 hn (by norm_num))
          (BinarySeparator.nodeNN n 3 2) : ℝ) ≤ 1 / (n : ℝ) := by
  change 1 / (4 * (n : ℝ)) ≤
      (((BinarySeparator.nuLaw n 3 hn (by norm_num) : Distribution) : Measure ℝ≥0)
        {BinarySeparator.nodeNN n 3 2}).toReal ∧
    (((BinarySeparator.nuLaw n 3 hn (by norm_num) : Distribution) : Measure ℝ≥0)
        {BinarySeparator.nodeNN n 3 2}).toReal ≤ 1 / (n : ℝ)
  constructor
  · exact BinarySeparator.nuLaw_atom_two_lower hn (by norm_num)
  · rw [BinarySeparator.nuLaw_atom_even hn (by norm_num) (show Even 2 by decide),
      BinarySeparator.limitWeight_two hn (by norm_num)]
    exact one_div_le_one_div_of_le
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)
      (BinarySeparator.n_le_normalizer hn (by norm_num))

/-- The exact-count event has the explicit probability `κ_r`. -/
theorem nuLaw_three_pivotCount_probability_lower {n r : ℕ}
    (hr : 1 ≤ r) (hn : max 6 (2 * r) ≤ n) :
    orderStatisticKappa r ≤
      ((independentValues
          (fun _ : Fin n ↦ BinarySeparator.nuLaw n 3 (by omega) (by norm_num)) :
          ProbabilityMeasure (ProphetPath n)) : Measure (ProphetPath n)).real
        {x | pivotCount (BinarySeparator.nodeNN n 3 2) x = r} := by
  have hn3 : 3 ≤ n := by omega
  have h2r : 2 * r ≤ n := by omega
  have hrn : r ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let p : ℝ := (atomParameter (BinarySeparator.nuLaw n 3 hn3 (by norm_num))
    (BinarySeparator.nodeNN n 3 2) : ℝ)
  let q : ℝ := 1 / (4 * (n : ℝ))
  have hpbounds := nuLaw_three_pivot_probability_bounds hn3
  have hqp : q ≤ p := by simpa only [p, q] using hpbounds.1
  have hpupper : p ≤ 1 / (n : ℝ) := by simpa only [p] using hpbounds.2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hp0 : 0 ≤ p := hq0.trans hqp
  have honep : 0 ≤ 1 - p := by
    have hinv : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one₀ hnpos]
      exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have honeq : 0 ≤ 1 - q := by
    have hqle := hqp.trans hpupper
    have hinv : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one₀ hnpos]
      exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hkernel := binomialKernel_mono hr h2r hq0 hqp hpupper
  have hchoose := choose_lower_half (n := n) (r := r) h2r
  have hsurvival := binomialSurvival_lower (n := n) (r := r) (by omega) hr hrn
  have hbase : orderStatisticKappa r ≤
      (((n : ℝ) / 2) ^ r / (r.factorial : ℝ)) *
        (q ^ r * (1 - q) ^ (n - r)) := by
    calc
      orderStatisticKappa r =
          (((n : ℝ) / 2) ^ r / (r.factorial : ℝ)) *
            (q ^ r * Real.exp (-(1 : ℝ) / 4)) := by
        dsimp [orderStatisticKappa, q]
        field_simp [ne_of_gt hnpos]
        rw [← mul_pow]
        rw [← mul_pow]
        congr 1
        field_simp [ne_of_gt hnpos]
        norm_num
      _ ≤ (((n : ℝ) / 2) ^ r / (r.factorial : ℝ)) *
            (q ^ r * (1 - q) ^ (n - r)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsurvival (pow_nonneg hq0 r))
          (div_nonneg (pow_nonneg (by positivity) r) (by positivity))
  rw [pivotCount_probability_exact]
  change orderStatisticKappa r ≤ (n.choose r : ℝ) * p ^ r * (1 - p) ^ (n - r)
  calc
    orderStatisticKappa r ≤
        (((n : ℝ) / 2) ^ r / (r.factorial : ℝ)) *
          (q ^ r * (1 - q) ^ (n - r)) := hbase
    _ ≤ (n.choose r : ℝ) * (p ^ r * (1 - p) ^ (n - r)) := by
      exact mul_le_mul hchoose hkernel
        (mul_nonneg (pow_nonneg hq0 r) (pow_nonneg honeq (n - r)))
        (by positivity)
    _ = (n.choose r : ℝ) * p ^ r * (1 - p) ^ (n - r) := by ring

/-- Iid `ν` has the order-statistic benchmark claimed in
`cor:order-stat-separator`, at the exact manuscript constant. -/
theorem nuLaw_three_orderStatisticBenchmark_lower {n r : ℕ}
    (hr : 1 ≤ r) (hn : max 6 (2 * r) ≤ n) :
    3 * orderStatisticKappa r * (n : ℝ) ≤
      orderStatisticBenchmark (⟨r, hr, by omega⟩ : ValidRank n)
        (fun _ : Fin n ↦ BinarySeparator.nuLaw n 3 (by omega) (by norm_num)) := by
  let rank : ValidRank n := ⟨r, hr, by omega⟩
  let nu : Distribution := BinarySeparator.nuLaw n 3 (by omega) (by norm_num)
  let a : ℝ≥0 := BinarySeparator.nodeNN n 3 2
  let event : Set (ProphetPath n) := {x | pivotCount a x = r}
  let laws : Fin n → Distribution := fun _ ↦ nu
  let productMeasure : Measure (ProphetPath n) := independentValues laws
  have hevent : MeasurableSet event := by
    exact (measurable_pivotCount a) (measurableSet_singleton r)
  have hfirst : HasFiniteFirstMoments laws := fun _ ↦
    BinarySeparator.hasFiniteMoments_nuLaw (by omega) (by norm_num) 1
  have hstatInt : Integrable
      (fun x : ProphetPath n ↦ (descendingOrderStatistic rank x : ℝ)) productMeasure := by
    exact integrable_descendingOrderStatistic rank laws hfirst
  have hindInt : Integrable (event.indicator (fun _ : ProphetPath n ↦ (a : ℝ)))
      productMeasure := (integrable_const (a : ℝ)).indicator hevent
  have hpoint : ∀ x : ProphetPath n,
      event.indicator (fun _ : ProphetPath n ↦ (a : ℝ)) x ≤
        (descendingOrderStatistic rank x : ℝ) := by
    intro x
    by_cases hx : x ∈ event
    · rw [Set.indicator_of_mem hx]
      have hcount : pivotCount a x = r := hx
      exact_mod_cast le_descendingOrderStatistic_of_pivotCount_eq rank rfl a x hcount
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hintegral : productMeasure.real event * (a : ℝ) ≤
      ∫ x : ProphetPath n, (descendingOrderStatistic rank x : ℝ) ∂productMeasure := by
    have hmono := integral_mono hindInt hstatInt hpoint
    rw [integral_indicator_const (a : ℝ) hevent, smul_eq_mul] at hmono
    exact hmono
  have hprob : orderStatisticKappa r ≤ productMeasure.real event := by
    simpa only [productMeasure, laws, nu, a, event] using
      nuLaw_three_pivotCount_probability_lower hr hn
  have ha0 : (0 : ℝ) ≤ a := by positivity
  calc
    3 * orderStatisticKappa r * (n : ℝ) = orderStatisticKappa r * (a : ℝ) := by
      dsimp only [a]
      simp [BinarySeparator.nodeNN]
      ring
    _ ≤ productMeasure.real event * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hprob ha0
    _ ≤ ∫ x : ProphetPath n, (descendingOrderStatistic rank x : ℝ) ∂productMeasure :=
      hintegral
    _ = orderStatisticBenchmark (⟨r, hr, by omega⟩ : ValidRank n)
        (fun _ : Fin n ↦ BinarySeparator.nuLaw n 3 (by omega) (by norm_num)) := by
      rfl

/-- General-base pivot probability bounds used in `cor:order-stat-separator`. -/
theorem nuLaw_pivot_probability_bounds {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    1 / (4 * (n : ℝ)) ≤
        (atomParameter (BinarySeparator.nuLaw n B hn hB)
          (BinarySeparator.nodeNN n B 2) : ℝ) ∧
      (atomParameter (BinarySeparator.nuLaw n B hn hB)
          (BinarySeparator.nodeNN n B 2) : ℝ) ≤ 1 / (n : ℝ) := by
  change 1 / (4 * (n : ℝ)) ≤
      (((BinarySeparator.nuLaw n B hn hB : Distribution) : Measure ℝ≥0)
        {BinarySeparator.nodeNN n B 2}).toReal ∧
    (((BinarySeparator.nuLaw n B hn hB : Distribution) : Measure ℝ≥0)
        {BinarySeparator.nodeNN n B 2}).toReal ≤ 1 / (n : ℝ)
  constructor
  · exact BinarySeparator.nuLaw_atom_two_lower hn hB
  · rw [BinarySeparator.nuLaw_atom_even hn hB (show Even 2 by decide),
      BinarySeparator.limitWeight_two hn hB]
    exact one_div_le_one_div_of_le
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)
      (BinarySeparator.n_le_normalizer hn hB)

/-- Analytic binomial estimate after the atom probability has been bounded. -/
theorem binomial_exact_mass_lower {n r : ℕ} (hr : 1 ≤ r) (h2r : 2 * r ≤ n)
    {p : ℝ} (hp0 : 0 ≤ p) (hlower : 1 / (4 * (n : ℝ)) ≤ p)
    (hupper : p ≤ 1 / (n : ℝ)) :
    orderStatisticKappa r ≤
      (n.choose r : ℝ) * p ^ r * (1 - p) ^ (n - r) := by
  have hrn : r ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2 * r) h2r)
  let q : ℝ := 1 / (4 * (n : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have honeq : 0 ≤ 1 - q := by
    have hqleone : q ≤ 1 := by
      dsimp only [q]
      rw [div_le_one₀ (by positivity : (0 : ℝ) < 4 * n)]
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith
    linarith
  have hkernel := binomialKernel_mono hr h2r hq0 hlower hupper
  have hchoose := choose_lower_half (n := n) (r := r) h2r
  have hsurvival := binomialSurvival_lower (n := n) (r := r) (by omega) hr hrn
  calc
    orderStatisticKappa r =
        (((n : ℝ) / 2) ^ r / (r.factorial : ℝ)) *
          (q ^ r * Real.exp (-(1 : ℝ) / 4)) := by
      dsimp [orderStatisticKappa, q]
      field_simp [ne_of_gt hnpos]
      rw [← mul_pow, ← mul_pow]
      congr 1
      field_simp [ne_of_gt hnpos]
      norm_num
    _ ≤ (((n : ℝ) / 2) ^ r / (r.factorial : ℝ)) *
          (q ^ r * (1 - q) ^ (n - r)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsurvival (pow_nonneg hq0 r))
        (div_nonneg (pow_nonneg (by positivity) r) (by positivity))
    _ ≤ (n.choose r : ℝ) * (p ^ r * (1 - p) ^ (n - r)) := by
      exact mul_le_mul hchoose hkernel
        (mul_nonneg (pow_nonneg hq0 r) (pow_nonneg honeq (n - r)))
        (by positivity)
    _ = (n.choose r : ℝ) * p ^ r * (1 - p) ^ (n - r) := by ring

/-- Exact-count probability for the general-base separator. -/
theorem nuLaw_pivotCount_probability_lower {n B r : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hr : 1 ≤ r) (h2r : 2 * r ≤ n) :
    orderStatisticKappa r ≤
      ((independentValues (fun _ : Fin n ↦ BinarySeparator.nuLaw n B hn hB) :
          ProbabilityMeasure (ProphetPath n)) : Measure (ProphetPath n)).real
        {x | pivotCount (BinarySeparator.nodeNN n B 2) x = r} := by
  let p : ℝ := (atomParameter (BinarySeparator.nuLaw n B hn hB)
    (BinarySeparator.nodeNN n B 2) : ℝ)
  have hp := nuLaw_pivot_probability_bounds hn hB
  have hp0 : 0 ≤ p := measureReal_nonneg
  rw [pivotCount_probability_exact]
  change orderStatisticKappa r ≤ (n.choose r : ℝ) * p ^ r * (1 - p) ^ (n - r)
  exact binomial_exact_mass_lower hr h2r hp0 (by simpa only [p] using hp.1)
    (by simpa only [p] using hp.2)

/-- First conclusion of `cor:order-stat-separator` at arbitrary manuscript base `B`. -/
theorem nuLaw_orderStatisticBenchmark_lower {n B r : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hr : 1 ≤ r) (h2r : 2 * r ≤ n) :
    orderStatisticKappa r * ((n : ℝ) * B) ≤
      orderStatisticBenchmark (⟨r, hr, by omega⟩ : ValidRank n)
        (fun _ : Fin n ↦ BinarySeparator.nuLaw n B hn hB) := by
  let rank : ValidRank n := ⟨r, hr, by omega⟩
  let nu : Distribution := BinarySeparator.nuLaw n B hn hB
  let a : ℝ≥0 := BinarySeparator.nodeNN n B 2
  let event : Set (ProphetPath n) := {x | pivotCount a x = r}
  let laws : Fin n → Distribution := fun _ ↦ nu
  let productMeasure : Measure (ProphetPath n) := independentValues laws
  have hevent : MeasurableSet event :=
    (measurable_pivotCount a) (measurableSet_singleton r)
  have hfirst : HasFiniteFirstMoments laws := fun _ ↦
    BinarySeparator.hasFiniteMoments_nuLaw hn hB 1
  have hstatInt : Integrable
      (fun x : ProphetPath n ↦ (descendingOrderStatistic rank x : ℝ)) productMeasure :=
    integrable_descendingOrderStatistic rank laws hfirst
  have hindInt : Integrable (event.indicator (fun _ : ProphetPath n ↦ (a : ℝ)))
      productMeasure := (integrable_const (a : ℝ)).indicator hevent
  have hpoint : ∀ x : ProphetPath n,
      event.indicator (fun _ : ProphetPath n ↦ (a : ℝ)) x ≤
        (descendingOrderStatistic rank x : ℝ) := by
    intro x
    by_cases hx : x ∈ event
    · rw [Set.indicator_of_mem hx]
      exact_mod_cast le_descendingOrderStatistic_of_pivotCount_eq rank rfl a x hx
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hintegral : productMeasure.real event * (a : ℝ) ≤
      ∫ x : ProphetPath n, (descendingOrderStatistic rank x : ℝ) ∂productMeasure := by
    have hmono := integral_mono hindInt hstatInt hpoint
    rw [integral_indicator_const (a : ℝ) hevent, smul_eq_mul] at hmono
    exact hmono
  have hprob : orderStatisticKappa r ≤ productMeasure.real event := by
    simpa only [productMeasure, laws, nu, a, event] using
      nuLaw_pivotCount_probability_lower hn hB hr h2r
  calc
    orderStatisticKappa r * ((n : ℝ) * B) = orderStatisticKappa r * (a : ℝ) := by
      dsimp only [a]
      simp [BinarySeparator.nodeNN]
    _ ≤ productMeasure.real event * (a : ℝ) :=
      mul_le_mul_of_nonneg_right hprob (by positivity)
    _ ≤ ∫ x : ProphetPath n, (descendingOrderStatistic rank x : ℝ) ∂productMeasure :=
      hintegral
    _ = orderStatisticBenchmark (⟨r, hr, by omega⟩ : ValidRank n)
        (fun _ : Fin n ↦ BinarySeparator.nuLaw n B hn hB) := rfl

/-- A coordinatewise gap bounds every order statistic by one cap plus the sum of upper-tail
values.  The corollary uses this only at rank one. -/
theorem descendingOrderStatistic_le_cap_add_tail {n : ℕ} (rank : ValidRank n)
    (cap threshold : ℝ≥0) (x : ProphetPath n)
    (hgap : ∀ i, x i < threshold → x i ≤ cap) :
    (descendingOrderStatistic rank x : ℝ) ≤
      (cap : ℝ) + ∑ i : Fin n, upperTailValue threshold (x i) := by
  let tailNN : Fin n → ℝ≥0 := fun i ↦ if threshold ≤ x i then x i else 0
  have hnn : descendingOrderStatistic rank x ≤ cap + ∑ i : Fin n, tailNN i := by
    rw [descendingOrderStatistic, Finset.sup'_le_iff]
    intro s hs
    have hcard : s.card = rank.1 := (Finset.mem_powersetCard.mp hs).2
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hsne
    have hminimum : subsetMinimum x s ≤ x i := by
      rw [subsetMinimum, dif_pos (show s.Nonempty from ⟨i, hi⟩)]
      exact Finset.inf'_le _ hi
    have htailSum : tailNN i ≤ ∑ j : Fin n, tailNN j := by
      exact Finset.single_le_sum (fun j _ ↦ bot_le) (Finset.mem_univ i)
    refine hminimum.trans ?_
    by_cases htail : threshold ≤ x i
    · have hxi : x i = tailNN i := by simp [tailNN, htail]
      rw [hxi]
      exact htailSum.trans (le_add_of_nonneg_left bot_le)
    · have hbelow : x i < threshold := lt_of_not_ge htail
      exact (hgap i hbelow).trans (le_add_of_nonneg_right bot_le)
  calc
    (descendingOrderStatistic rank x : ℝ) ≤
        ((cap + ∑ i : Fin n, tailNN i : ℝ≥0) : ℝ) := by exact_mod_cast hnn
    _ = (cap : ℝ) + ∑ i : Fin n, upperTailValue threshold (x i) := by
      simp only [NNReal.coe_add, NNReal.coe_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      by_cases htail : threshold ≤ x i <;>
        simp [tailNN, upperTailValue, htail]

/-- Second benchmark conclusion of `cor:order-stat-separator`. -/
theorem muLaw_maximumBenchmark_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    orderStatisticBenchmark (⟨1, by omega, by omega⟩ : ValidRank n)
        (fun _ : Fin n ↦ BinarySeparator.muLaw n B hn hB) ≤ 2 * (B : ℝ) := by
  let rank : ValidRank n := ⟨1, by omega, by omega⟩
  let mu : Distribution := BinarySeparator.muLaw n B hn hB
  let laws : Fin n → Distribution := fun _ ↦ mu
  let threshold : ℝ≥0 := BinarySeparator.nodeNN n B 3
  let cap : ℝ≥0 := BinarySeparator.nodeNN n B 1
  let productMeasure : Measure (ProphetPath n) := independentValues laws
  have hfirst : HasFiniteFirstMoments laws := fun _ ↦
    BinarySeparator.hasFiniteMoments_muLaw hn hB 1
  have hgapLaw : ∀ᵐ y ∂(mu : Measure ℝ≥0), y < threshold → y ≤ cap := by
    simpa only [mu, threshold, cap] using muLaw_gap_below_node_three hn hB
  have hgapProduct : ∀ᵐ x ∂productMeasure, ∀ i, x i < threshold → x i ≤ cap := by
    apply Filter.eventually_all.mpr
    intro i
    dsimp only [productMeasure, laws]
    rw [independentValues, ProbabilityMeasure.toMeasure_pi]
    exact (MeasureTheory.measurePreserving_eval
      (fun _ : Fin n ↦ (mu : Measure ℝ≥0)) i).quasiMeasurePreserving.ae hgapLaw
  have hstatInt : Integrable
      (fun x : ProphetPath n ↦ (descendingOrderStatistic rank x : ℝ)) productMeasure :=
    integrable_descendingOrderStatistic rank laws hfirst
  have htailLaw : Integrable (upperTailValue threshold) (mu : Measure ℝ≥0) :=
    integrable_upperTailValue threshold
      (BinarySeparator.hasFiniteMoments_muLaw hn hB 1)
  have htailCoord (i : Fin n) : Integrable
      (fun x : ProphetPath n ↦ upperTailValue threshold (x i)) productMeasure := by
    dsimp only [productMeasure, laws]
    rw [independentValues, ProbabilityMeasure.toMeasure_pi]
    exact MeasureTheory.integrable_comp_eval htailLaw
  have htailSum : Integrable
      (fun x : ProphetPath n ↦ ∑ i : Fin n, upperTailValue threshold (x i))
      productMeasure := integrable_finset_sum _ fun i _ ↦ htailCoord i
  have hrhsInt : Integrable
      (fun x : ProphetPath n ↦ (cap : ℝ) +
        ∑ i : Fin n, upperTailValue threshold (x i)) productMeasure :=
    (integrable_const (cap : ℝ)).add htailSum
  have hmono :
      (∫ x : ProphetPath n, (descendingOrderStatistic rank x : ℝ) ∂productMeasure) ≤
        ∫ x : ProphetPath n, ((cap : ℝ) +
          ∑ i : Fin n, upperTailValue threshold (x i)) ∂productMeasure := by
    apply integral_mono_ae hstatInt hrhsInt
    exact hgapProduct.mono fun x hx ↦
      descendingOrderStatistic_le_cap_add_tail rank cap threshold x hx
  calc
    orderStatisticBenchmark (⟨1, by omega, by omega⟩ : ValidRank n)
        (fun _ : Fin n ↦ BinarySeparator.muLaw n B hn hB) =
        ∫ x : ProphetPath n, (descendingOrderStatistic rank x : ℝ) ∂productMeasure := rfl
    _ ≤ ∫ x : ProphetPath n, ((cap : ℝ) +
        ∑ i : Fin n, upperTailValue threshold (x i)) ∂productMeasure := hmono
    _ = (cap : ℝ) + ∑ i : Fin n,
        ∫ x : ProphetPath n, upperTailValue threshold (x i) ∂productMeasure := by
      rw [integral_add (integrable_const (cap : ℝ)) htailSum,
        integral_finset_sum Finset.univ (fun i _ ↦ htailCoord i)]
      simp
    _ = (B : ℝ) + (n : ℝ) *
        (∫ y, upperTailValue (BinarySeparator.nodeNN n B 3) y
          ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0)) := by
      have hcoord (i : Fin n) :
          (∫ x : ProphetPath n, upperTailValue threshold (x i) ∂productMeasure) =
            ∫ y, upperTailValue threshold y ∂(mu : Measure ℝ≥0) := by
        dsimp only [productMeasure]
        exact integral_coordinate_upperTailValue laws i threshold
      rw [Finset.sum_congr rfl (fun i _ ↦ hcoord i)]
      simp [cap, threshold, laws, mu, BinarySeparator.nodeNN]
    _ ≤ (B : ℝ) + 6 / (n : ℝ) := by
      gcongr
      exact muLaw_totalTail_le_six hn hB
    _ ≤ 2 * (B : ℝ) := by
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
      have hnpos : (0 : ℝ) < n := by positivity
      have hsmall : 6 / (n : ℝ) ≤ (B : ℝ) := by
        rw [div_le_iff₀ hnpos]
        nlinarith
      linarith

/-- `cor:order-stat-separator`, `sections/prophet.tex`: bundled literal quantifier order and
all four conclusions.  The iid expectations are represented by product-measure benchmarks;
the two displayed tail expectations reduce to `n` times the one-coordinate tail integral. -/
theorem order_stat_separator (r : ℕ) (hr : 1 ≤ r) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (B n : ℕ) (hB : 3 ≤ B) (hn : 3 ≤ n)
        (hsize : max (2 * B) (2 * r) ≤ n),
        kappa * ((n : ℝ) * B) ≤
            orderStatisticBenchmark (⟨r, hr, by omega⟩ : ValidRank n)
              (fun _ : Fin n ↦ BinarySeparator.nuLaw n B hn hB) ∧
          orderStatisticBenchmark (⟨1, by omega, by omega⟩ : ValidRank n)
              (fun _ : Fin n ↦ BinarySeparator.muLaw n B hn hB) ≤ 2 * (B : ℝ) ∧
          (n : ℝ) *
              (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
                ∂(BinarySeparator.nuLaw n B hn hB : Measure ℝ≥0)) ≤ 6 / (n : ℝ) ∧
          (n : ℝ) *
              (∫ x, upperTailValue (BinarySeparator.nodeNN n B 3) x
                ∂(BinarySeparator.muLaw n B hn hB : Measure ℝ≥0)) ≤ 6 / (n : ℝ) := by
  refine ⟨orderStatisticKappa r, ?_, ?_⟩
  · unfold orderStatisticKappa
    positivity
  intro B n hB hn hsize
  have h2r : 2 * r ≤ n := (le_max_right (2 * B) (2 * r)).trans hsize
  exact ⟨nuLaw_orderStatisticBenchmark_lower hn hB hr h2r,
    muLaw_maximumBenchmark_le hn hB,
    nuLaw_totalTail_le_six hn hB,
    muLaw_totalTail_le_six hn hB⟩

/-! ## Concrete hard block -/

/-- The moment-equivalent pair supplied to one prophet block. -/
noncomputable def binaryProphetBlockPair (n : ℕ) (hn : 3 ≤ n) : ProphetBlockPair where
  mu := BinarySeparator.muLaw n 3 hn (by norm_num)
  nu := BinarySeparator.nuLaw n 3 hn (by norm_num)
  momentEquivalent := BinarySeparator.momentEquivalent_muLaw_nuLaw hn (by norm_num)

/-- `cor:order-stat-separator`, specialized to `B=3`, packaged in the exact interface used
by the internal hard-family argument. -/
noncomputable def binaryProphetHardBlock (r n : ℕ) (hr : 1 ≤ r)
    (hn : max 6 (2 * r) ≤ n) :
    ProphetHardBlock r n (orderStatisticKappa r) where
  pair := binaryProphetBlockPair n (by omega)
  hr := hr
  hrn := by omega
  threshold := BinarySeparator.nodeNN n 3 3
  nu_gap := by
    simpa only [binaryProphetBlockPair, BinarySeparator.nodeNN, Nat.cast_mul,
      Nat.cast_ofNat, Nat.mul_comm, pow_zero, pow_one] using
      nuLaw_gap_below_node_three (n := n) (B := 3) (by omega) (by norm_num)
  mu_gap := by
    simpa only [binaryProphetBlockPair, BinarySeparator.nodeNN, Nat.cast_ofNat] using
      muLaw_gap_below_node_three (n := n) (B := 3) (by omega) (by norm_num)
  nu_tail := by
    simpa only [binaryProphetBlockPair] using nuLaw_three_totalTail_le (n := n) (by omega)
  mu_tail := by
    simpa only [binaryProphetBlockPair] using muLaw_three_totalTail_le (n := n) (by omega)
  rank_lower := by
    simpa only [binaryProphetBlockPair] using
      nuLaw_three_orderStatisticBenchmark_lower (r := r) (n := n) hr hn

/-- Existence form of the `B=3` block, convenient for theorem-level traceability. -/
theorem exists_binaryProphetHardBlock (r n : ℕ) (hr : 1 ≤ r)
    (hn : max 6 (2 * r) ≤ n) :
    Nonempty (ProphetHardBlock r n (orderStatisticKappa r)) :=
  ⟨binaryProphetHardBlock r n hr hn⟩

end

end MomentAmbiguity
