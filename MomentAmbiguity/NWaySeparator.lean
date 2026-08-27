import MomentAmbiguity.Basic
import MomentAmbiguity.Discrete
import MomentAmbiguity.NWayCoefficients

/-!
# The `N`-way residue-class separator

This module isolates the measure-theoretic normalization step from the analytic coefficient
construction.  `ResidueWeightCertificate` is not an external assumption: the intended
certificate is supplied by `NWayCoefficients`; spelling out the interface makes every
summability and positivity obligation visible to Lean.
-/

open scoped BigOperators ENNReal NNReal

namespace MomentAmbiguity

open MeasureTheory Set

noncomputable section

/-- The geometric support node `B^j`. -/
def nwayNode (B j : ℕ) : ℝ≥0 := (B : ℝ≥0) ^ j

@[simp] theorem nwayNode_zero (B : ℕ) : nwayNode B 0 = 1 := by simp [nwayNode]

theorem nwayNode_injective {B : ℕ} (hB : 2 ≤ B) :
    Function.Injective (nwayNode B) := by
  exact pow_right_injective₀ (show (0 : ℝ≥0) < B by positivity)
    (by exact_mod_cast (show B ≠ 1 by omega))

/-- A residue-class event in the geometric support. -/
def nwaySupportClass (B N h : ℕ) : Set ℝ≥0 :=
  {x | ∃ j : ℕ, j % N = h ∧ x = nwayNode B j}

theorem nwaySupportClass_countable (B N h : ℕ) :
    (nwaySupportClass B N h).Countable := by
  apply (Set.countable_range (nwayNode B)).mono
  rintro x ⟨j, -, rfl⟩
  exact mem_range_self j

theorem measurableSet_nwaySupportClass (B N h : ℕ) :
    MeasurableSet (nwaySupportClass B N h) :=
  (nwaySupportClass_countable B N h).measurableSet

theorem nwaySupportClass_disjoint {B N h h' : ℕ} (hB : 2 ≤ B) (hN : 1 ≤ N)
    (hne : h ≠ h') : Disjoint (nwaySupportClass B N h) (nwaySupportClass B N h') := by
  rw [Set.disjoint_left]
  rintro x ⟨i, hi, hxi⟩ ⟨j, hj, hxj⟩
  have hij : i = j := nwayNode_injective hB (hxi.symm.trans hxj)
  exact hne (hi.symm.trans (hij ▸ hj))

/-- All analytic facts required to turn nonnegative weights into the manuscript's laws.

The coefficient module proves this structure for its concrete `w_j/W`.  Its fields explicitly
record probability normalization, finite moments, residue equality, and support; none of those
facts are smuggled into the definition of a distribution.
-/
structure ResidueWeightCertificate (B N : ℕ) where
  mass : Fin N → ℕ → ℝ≥0∞
  mass_ne_top : ∀ h j, mass h j ≠ ∞
  mass_hasSum : ∀ h, HasSum (mass h) 1
  supported : ∀ h j, mass h j ≠ 0 → j % N = h
  moment_summable : ∀ (h : Fin N) (t : ℕ),
    Summable (fun j ↦ (mass h j).toReal * (B : ℝ) ^ (t * j))
  moment_tsum_eq : ∀ (h h' : Fin N) (t : ℕ),
    (∑' j, (mass h j).toReal * (B : ℝ) ^ (t * j)) =
      ∑' j, (mass h' j).toReal * (B : ℝ) ^ (t * j)

/-! ### Concrete coefficient certificate -/

/-- Enumeration of the exponents in residue class `h`. -/
def nwayExponentEmbedding (N : ℕ) (h : Fin N) (m : ℕ) : ℕ := h.val + N * m

theorem nwayExponentEmbedding_injective {N : ℕ} (hN : 1 ≤ N) (h : Fin N) :
    Function.Injective (nwayExponentEmbedding N h) := by
  intro a b hab
  exact Nat.mul_left_cancel (by omega) (Nat.add_left_cancel hab)

/-- The normalized manuscript coefficient `w_j/W`, packaged as a nonnegative real. -/
def nwayNormalizedCoeff (B N : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N)
    (j : ℕ) : ℝ≥0 :=
  ⟨nwayCoeff B N j / nwayNormalizer B N,
    div_nonneg (nwayCoeff_nonneg B N j hB hN)
      (le_of_lt (nwayNormalizer_pos B N hB hN))⟩

/-- The normalized coefficient on one residue class, and zero off that class. -/
noncomputable def nwayMassNN (B N : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N)
    (h : Fin N) (j : ℕ) : ℝ≥0 := by
  classical
  exact if j ∈ Set.range (nwayExponentEmbedding N h) then
    nwayNormalizedCoeff B N hB hN j else 0

theorem nwayResidueCoeff_hasSum (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    HasSum (fun m : ℕ => nwayCoeff B N (nwayExponentEmbedding N h m))
      (nwayNormalizer B N) := by
  have hs := (summable_nwayResidueMoment B N 0 hB hN (h : ZMod N)).hasSum
  rw [show nwayNormalizer B N = nwayResidueMoment B N 0 (h : ZMod N) from
    nwayNormalizer_eq_residue B N hB hN (h : ZMod N)]
  rw [nwayResidueMoment_zero_eq_coeff_tsum]
  simpa [nwayExponentEmbedding, nwayMomentTerm, Nat.mod_eq_of_lt h.isLt] using hs

/-- On the zero residue class, the quadratic exponent is at least the block number. -/
theorem nwayExponent_mul_ge (N k : ℕ) (hN : 2 ≤ N) :
    k ≤ nwayExponent N (N * k) := by
  by_cases hk : k = 0
  · subst k
    simp
  have hgap := nway_index_sub_exponent_le N (N * k) hN
  have hprod : (0 : ℤ) ≤ ((N : ℤ) - 1) * ((k : ℤ) - 1) :=
    mul_nonneg (by omega) (by omega)
  have hNsub : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  push_cast at hgap
  rw [hNsub] at hgap
  exact_mod_cast (show (k : ℤ) ≤ nwayExponent N (N * k) by nlinarith)

/-- Zero-residue coefficients are dominated by a geometric series with ratio `2^N/B`. -/
theorem nwayCoeff_zeroResidue_le_geometric (B N k : ℕ)
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayCoeff B N (N * k) ≤ (((2 : ℝ) ^ N) / B) ^ k := by
  have he : k ≤ nwayExponent N (N * k) := nwayExponent_mul_ge N k hN
  have hz : (B : ℝ) ^ (-(nwayExponent N (N * k) : ℤ)) ≤
      (B : ℝ) ^ (-(k : ℤ)) := by
    apply zpow_le_zpow_right₀ (by exact_mod_cast (show 1 ≤ B by omega))
    exact neg_le_neg (by exact_mod_cast he)
  calc
    nwayCoeff B N (N * k) ≤ (2 : ℝ) ^ (N * k) *
        (B : ℝ) ^ (-(nwayExponent N (N * k) : ℤ)) :=
      nwayCoeff_upper_bound B N (N * k) hB hN
    _ ≤ (2 : ℝ) ^ (N * k) * (B : ℝ) ^ (-(k : ℤ)) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = (((2 : ℝ) ^ N) / B) ^ k := by
      rw [zpow_neg, zpow_natCast]
      simp only [div_pow, pow_mul]
      ring

/-- A quantitative normalization bound used for first-atom concentration.  For
`B ≥ 2^(N+1)`, the entire zero-residue tail is bounded by a geometric series. -/
theorem nwayNormalizer_le_geometric (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (hBN : 2 ^ (N + 1) ≤ B) :
    nwayNormalizer B N ≤ (1 - ((2 : ℝ) ^ N) / B)⁻¹ := by
  let q : ℝ := ((2 : ℝ) ^ N) / B
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < B)]
    have hp : (2 : ℝ) ^ N * 2 ≤ B := by
      exact_mod_cast (show 2 ^ N * 2 ≤ B by simpa [pow_succ] using hBN)
    linarith
  have hq1 : q < 1 := hqhalf.trans_lt (by norm_num)
  let hzero : Fin N := ⟨0, by omega⟩
  have hs := nwayResidueCoeff_hasSum B N hB hN hzero
  have hs' : HasSum (fun k : ℕ ↦ nwayCoeff B N (N * k)) (nwayNormalizer B N) := by
    simpa [hzero, nwayExponentEmbedding] using hs
  calc
    nwayNormalizer B N = ∑' k : ℕ, nwayCoeff B N (N * k) := hs'.tsum_eq.symm
    _ ≤ ∑' k : ℕ, q ^ k := by
      exact hs'.summable.tsum_le_tsum
        (fun k ↦ nwayCoeff_zeroResidue_le_geometric B N k hB hN)
        (summable_geometric_of_lt_one hq0 hq1)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- A denominator-free form of the preceding estimate. -/
theorem one_sub_ratio_mul_nwayNormalizer_le_one (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (hBN : 2 ^ (N + 1) ≤ B) :
    (1 - ((2 : ℝ) ^ N) / B) * nwayNormalizer B N ≤ 1 := by
  let q : ℝ := ((2 : ℝ) ^ N) / B
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < B)]
    have hp : (2 : ℝ) ^ N * 2 ≤ B := by
      exact_mod_cast (show 2 ^ N * 2 ≤ B by simpa [pow_succ] using hBN)
    linarith
  have hpos : 0 < 1 - q := by linarith
  have hW := nwayNormalizer_le_geometric B N hB hN hBN
  change (1 - q) * nwayNormalizer B N ≤ 1
  calc
    (1 - q) * nwayNormalizer B N ≤ (1 - q) * (1 - q)⁻¹ :=
      mul_le_mul_of_nonneg_left hW hpos.le
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)

theorem nwayNormalizedCoeff_hasSum (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    HasSum (fun m : ℕ =>
      nwayNormalizedCoeff B N hB hN (nwayExponentEmbedding N h m)) 1 := by
  rw [← NNReal.hasSum_coe]
  have hs := (nwayResidueCoeff_hasSum B N hB hN h).div_const (nwayNormalizer B N)
  have hW0 := ne_of_gt (nwayNormalizer_pos B N hB hN)
  change HasSum (fun m : ℕ => nwayCoeff B N (nwayExponentEmbedding N h m) /
    nwayNormalizer B N) (1 : ℝ)
  simpa [hW0] using hs

theorem nwayMassNN_hasSum (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    HasSum (nwayMassNN B N hB hN h) 1 := by
  apply ((nwayExponentEmbedding_injective (by omega) h).hasSum_iff
    (f := nwayMassNN B N hB hN h)
    (fun j hj => by simp [nwayMassNN, hj])).mp
  convert nwayNormalizedCoeff_hasSum B N hB hN h using 1
  funext m
  simp [nwayMassNN]

theorem nwayMassNN_supported (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (j : ℕ)
    (hj : nwayMassNN B N hB hN h j ≠ 0) : j % N = h := by
  have hr : j ∈ Set.range (nwayExponentEmbedding N h) := by
    by_contra hn
    exact hj (by simp [nwayMassNN, hn])
  obtain ⟨m, rfl⟩ := hr
  simp [nwayExponentEmbedding, Nat.add_mod, Nat.mod_eq_of_lt h.isLt]

theorem nwayMassNN_moment_hasSum (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (t : ℕ) :
    HasSum (fun j : ℕ => (nwayMassNN B N hB hN h j : ℝ) *
      (B : ℝ) ^ (t * j))
      (nwayResidueMoment B N t (h : ZMod N) / nwayNormalizer B N) := by
  let f : ℕ → ℝ := fun j => (nwayMassNN B N hB hN h j : ℝ) *
    (B : ℝ) ^ (t * j)
  have hf0 : ∀ j ∉ Set.range (nwayExponentEmbedding N h), f j = 0 := by
    intro j hj
    simp [f, nwayMassNN, hj]
  apply ((nwayExponentEmbedding_injective (by omega) h).hasSum_iff hf0).mp
  have hs := (summable_nwayResidueMoment B N t hB hN (h : ZMod N)).hasSum.div_const
    (nwayNormalizer B N)
  apply hs.congr_fun
  intro m
  dsimp only [Function.comp_apply, f]
  rw [show nwayMassNN B N hB hN h (nwayExponentEmbedding N h m) =
      nwayNormalizedCoeff B N hB hN (nwayExponentEmbedding N h m) by
        simp [nwayMassNN]]
  have hval : (h : ZMod N).val = h.val := by
    simpa using Nat.mod_eq_of_lt h.isLt
  rw [hval]
  change (nwayCoeff B N (nwayExponentEmbedding N h m) / nwayNormalizer B N) *
    (B : ℝ) ^ (t * nwayExponentEmbedding N h m) =
    nwayMomentTerm B N t (h.val + N * m) / nwayNormalizer B N
  simp only [nwayMomentTerm, nwayExponentEmbedding]
  ring

/-- The concrete `ℝ≥0∞` weight used by the PMF constructor. -/
def nwayMass (B N : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N)
    (h : Fin N) (j : ℕ) : ℝ≥0∞ := nwayMassNN B N hB hN h j

/-- Concrete realization of the manuscript weights.  This is the certificate consumed by all
measure-theoretic laws below; it has no external hypotheses. -/
def nwayResidueWeightCertificate (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) : ResidueWeightCertificate B N where
  mass := nwayMass B N hB hN
  mass_ne_top := fun h j => ENNReal.coe_ne_top
  mass_hasSum := fun h => ENNReal.hasSum_coe.mpr (nwayMassNN_hasSum B N hB hN h)
  supported := fun h j hj => by
    apply nwayMassNN_supported B N hB hN h j
    simpa [nwayMass] using hj
  moment_summable := fun h t => by
    have hs := nwayMassNN_moment_hasSum B N hB hN h t
    apply hs.summable.congr
    intro j
    simp [nwayMass, ENNReal.coe_toReal]
  moment_tsum_eq := fun h h' t => by
    have hh := nwayMassNN_moment_hasSum B N hB hN h t
    have hh' := nwayMassNN_moment_hasSum B N hB hN h' t
    simp only [nwayMass, ENNReal.coe_toReal] at hh hh' ⊢
    rw [hh.tsum_eq, hh'.tsum_eq,
      nwayResidueMoment_eq_normalizer B N t hB hN (h : ZMod N),
      nwayResidueMoment_eq_normalizer B N t hB hN (h' : ZMod N)]

/-- On its designated residue class, the concrete ENNReal mass is exactly `w_j/W`.
This is the atom formula appearing in `prop:key-prop-2-ext`. -/
theorem nwayMass_toReal_of_modEq (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (j : ℕ)
    (hj : j % N = h.val) :
    (nwayMass B N hB hN h j).toReal =
      nwayCoeff B N j / nwayNormalizer B N := by
  have hr : j ∈ Set.range (nwayExponentEmbedding N h) := by
    refine ⟨j / N, ?_⟩
    rw [nwayExponentEmbedding, ← hj]
    exact Nat.mod_add_div j N
  simp only [nwayMass, nwayMassNN, hr, if_true, ENNReal.coe_toReal]
  rfl

/-- Off the designated residue class the concrete mass vanishes, so every atom is bounded by
the untruncated normalized coefficient. -/
theorem nwayMass_toReal_le (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (j : ℕ) :
    (nwayMass B N hB hN h j).toReal ≤
      nwayCoeff B N j / nwayNormalizer B N := by
  by_cases hr : j ∈ Set.range (nwayExponentEmbedding N h)
  · simp only [nwayMass, nwayMassNN, hr, if_true, ENNReal.coe_toReal]
    exact le_rfl
  · simp only [nwayMass, nwayMassNN, hr, if_false, ENNReal.coe_zero,
      ENNReal.toReal_zero]
    exact div_nonneg (nwayCoeff_nonneg B N j hB hN)
      (le_of_lt (nwayNormalizer_pos B N hB hN))

namespace ResidueWeightCertificate

/-- The PMF on exponents belonging to residue class `h`. -/
def exponentPMF {B N : ℕ} (C : ResidueWeightCertificate B N) (h : Fin N) : PMF ℕ :=
  ⟨C.mass h, C.mass_hasSum h⟩

@[simp] theorem exponentPMF_apply {B N : ℕ} (C : ResidueWeightCertificate B N)
    (h : Fin N) (j : ℕ) : C.exponentPMF h j = C.mass h j := rfl

/-- The normalized law on the geometric nodes `B^j`. -/
def law {B N : ℕ} (C : ResidueWeightCertificate B N) (h : Fin N) : Distribution :=
  atomicLaw (C.exponentPMF h) (nwayNode B)

theorem exponentPMF_support_subset {B N : ℕ} (C : ResidueWeightCertificate B N)
    (h : Fin N) : (C.exponentPMF h).support ⊆ {j | j % N = h} := by
  intro j hj
  exact C.supported h j ((PMF.mem_support_iff _ _).mp hj)

/-- Every law is concentrated on its designated residue class. -/
theorem law_support {B N : ℕ} (C : ResidueWeightCertificate B N) (h : Fin N) :
    ((C.law h : Distribution) : Measure ℝ≥0) (nwaySupportClass B N h) = 1 := by
  have himage := atomicLaw_toMeasure_image_support (C.exponentPMF h) (nwayNode B)
  apply le_antisymm
  · rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_le_coe.2 ((C.law h).apply_le_one (nwaySupportClass B N h))
  calc
    1 = ((C.law h : Distribution) : Measure ℝ≥0)
        (nwayNode B '' (C.exponentPMF h).support) := himage.symm
    _ ≤ ((C.law h : Distribution) : Measure ℝ≥0) (nwaySupportClass B N h) := by
      apply measure_mono
      rintro x ⟨j, hj, rfl⟩
      exact ⟨j, C.supported h j ((PMF.mem_support_iff _ _).mp hj), rfl⟩

private lemma exponentPMF_toMeasure_eq_sum_dirac {B N : ℕ}
    (C : ResidueWeightCertificate B N) (h : Fin N) :
    (C.exponentPMF h).toMeasure =
      Measure.sum (fun j : ℕ ↦ C.mass h j • Measure.dirac j) := by
  ext s hs
  rw [PMF.toMeasure_apply _ hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro j
  by_cases hj : j ∈ s
  · simp only [exponentPMF_apply, Set.indicator_of_mem hj]
    simp [Measure.smul_apply, hs, hj]
  · simp [exponentPMF_apply, hj, Measure.smul_apply, hs]

lemma integrable_exponentMoment {B N : ℕ} (C : ResidueWeightCertificate B N)
    (h : Fin N) (t : ℕ) :
    Integrable (fun j : ℕ ↦ (B : ℝ) ^ (t * j)) (C.exponentPMF h).toMeasure := by
  rw [exponentPMF_toMeasure_eq_sum_dirac C h]
  apply integrable_sum_dirac (C.mass_ne_top h)
  simpa only [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg B) _)] using
    C.moment_summable h t

/-- Every geometric law has every finite moment. -/
theorem law_hasFiniteMoments {B N : ℕ} (C : ResidueWeightCertificate B N) (h : Fin N) :
    HasFiniteMoments (C.law h) := by
  intro t
  rw [HasFiniteMoment]
  change Integrable (momentIntegrand t)
    (((atomicLaw (C.exponentPMF h) (nwayNode B) : Distribution) : Measure ℝ≥0))
  rw [coe_atomicLaw, ← PMF.toMeasure_map (nwayNode B) (C.exponentPMF h) (by fun_prop)]
  have hm : StronglyMeasurable (momentIntegrand t) := by
    unfold momentIntegrand
    fun_prop
  rw [integrable_map_measure hm.aestronglyMeasurable (by fun_prop)]
  simpa [momentIntegrand, Function.comp_def, nwayNode, ← pow_mul, Nat.mul_comm] using
    C.integrable_exponentMoment h t

/-- Moment evaluation as the absolutely convergent weighted series. -/
theorem law_moment_eq_tsum {B N : ℕ} (C : ResidueWeightCertificate B N)
    (h : Fin N) (t : ℕ) :
    moment (C.law h) t = ∑' j, (C.mass h j).toReal * (B : ℝ) ^ (t * j) := by
  unfold law
  rw [moment_atomicLaw_eq_tsum (C.exponentPMF h) (nwayNode B) (by fun_prop) t]
  · simp only [exponentPMF_apply, nwayNode, NNReal.coe_pow, NNReal.coe_natCast, ← pow_mul,
      Nat.mul_comm]
  · simpa [nwayNode, ← pow_mul, Nat.mul_comm] using C.integrable_exponentMoment h t

/-- `lem:N-class-all-moments`: all normalized residue laws have finite, equal moments. -/
theorem law_momentEquivalent {B N : ℕ} (C : ResidueWeightCertificate B N)
    (h h' : Fin N) : MomentEquivalent (C.law h) (C.law h') := by
  refine ⟨C.law_hasFiniteMoments h, C.law_hasFiniteMoments h', ?_⟩
  funext t
  simp only [momentSequence, C.law_moment_eq_tsum]
  exact C.moment_tsum_eq h h' t

/-- Pairwise residue separation witnesses maximal manuscript-normalized total variation. -/
theorem law_manuscriptTV_eq_one {B N : ℕ} (C : ResidueWeightCertificate B N)
    (hB : 2 ≤ B) (hN : 2 ≤ N) {h h' : Fin N} (hne : h ≠ h') :
    manuscriptTV (C.law h) (C.law h') = 1 := by
  have hmass : (C.law h) (nwaySupportClass B N h) = 1 := by
    have hs := C.law_support h
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hs
    exact ENNReal.coe_eq_one.mp hs
  apply manuscriptTV_eq_one_of_separating_set _ _
    (measurableSet_nwaySupportClass B N h) hmass
  have hdis := nwaySupportClass_disjoint hB (by omega : 1 ≤ N)
    (fun heq ↦ hne (Fin.ext heq))
  have hsubset : nwaySupportClass B N h ⊆ (nwaySupportClass B N h')ᶜ :=
    Set.disjoint_left.mp hdis
  apply (ProbabilityMeasure.null_iff_toMeasure_null _ _).2
  apply measure_mono_null hsubset
  rw [measure_compl (measurableSet_nwaySupportClass B N h')]
  · simp [C.law_support h']
  · exact measure_ne_top _ _

end ResidueWeightCertificate

/-! ### Concrete laws and the manuscript headline -/

/-- The `h`-th probability law in the concrete `N`-way construction. -/
noncomputable def nwayDistribution (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) : Distribution :=
  (nwayResidueWeightCertificate B N hB hN).law h

/-- The exact mass of the geometric atom `B^j`.  The equality is stated in ENNReal, the
codomain of a measure; `nwayMass_toReal_of_modEq` supplies its real-valued form. -/
theorem nwayDistribution_singleton (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (j : ℕ) :
    ((nwayDistribution B N hB hN h : Distribution) : Measure ℝ≥0) {nwayNode B j} =
      nwayMass B N hB hN h j := by
  exact atomicLaw_toMeasure_singleton_of_injective
    ((nwayResidueWeightCertificate B N hB hN).exponentPMF h)
    (nwayNode B) (by fun_prop) (nwayNode_injective hB) j

/-- Concrete finite-moment wrapper for `lem:N-class-all-moments`. -/
theorem nwayDistribution_hasFiniteMoments (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    HasFiniteMoments (nwayDistribution B N hB hN h) :=
  (nwayResidueWeightCertificate B N hB hN).law_hasFiniteMoments h

/-- `lem:N-class-all-moments`: every two concrete residue laws have all finite moments and
their complete moment sequences agree. -/
theorem nwayDistribution_momentEquivalent (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h h' : Fin N) :
    MomentEquivalent (nwayDistribution B N hB hN h)
      (nwayDistribution B N hB hN h') :=
  (nwayResidueWeightCertificate B N hB hN).law_momentEquivalent h h'

/-- Each concrete law is concentrated on exactly its designated residue-class support. -/
theorem nwayDistribution_support (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) :
    ((nwayDistribution B N hB hN h : Distribution) : Measure ℝ≥0)
      (nwaySupportClass B N h) = 1 :=
  (nwayResidueWeightCertificate B N hB hN).law_support h

/-- `cor:maximal-total-variation`: every distinct pair of concrete `N`-way laws has maximal
manuscript-normalized total variation. -/
theorem nwayDistribution_manuscriptTV_eq_one (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) {h h' : Fin N} (hne : h ≠ h') :
    manuscriptTV (nwayDistribution B N hB hN h)
      (nwayDistribution B N hB hN h') = 1 :=
  (nwayResidueWeightCertificate B N hB hN).law_manuscriptTV_eq_one hB hN hne

/-- The designated first exponent `h < N` has zero cost. -/
theorem nwayExponent_eq_zero_of_lt (N j : ℕ) (hN : 2 ≤ N) (hj : j < N) :
    nwayExponent N j = 0 := by
  by_cases hj' : j < N - 1
  · simp [nwayExponent, nwayLevel, nwayRemainder, Nat.div_eq_of_lt hj']
  · have hjeq : j = N - 1 := by omega
    subst j
    have hd : N - 1 ≠ 0 := by omega
    have hdiv : (N - 1) / (N - 1) = 1 := Nat.div_self (by omega : 0 < N - 1)
    simp [nwayExponent, nwayLevel, nwayRemainder, hd, hdiv]

/-- Quantitative first-atom estimate: once `B ≥ 2^(N+1)`, every designated atom has
probability at least `1 - 2^N/B`.  This is the denominator-free estimate used by the
secretary coupling. -/
theorem nwayFirstAtom_ge_one_sub_ratio (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (hBN : 2 ^ (N + 1) ≤ B) (h : Fin N) :
    1 - ((2 : ℝ) ^ N) / B ≤
      (((nwayDistribution B N hB hN h : Distribution) : Measure ℝ≥0)
        {nwayNode B h.val}).toReal := by
  rw [nwayDistribution_singleton B N hB hN h h.val,
    nwayMass_toReal_of_modEq B N hB hN h h.val (Nat.mod_eq_of_lt h.isLt)]
  have he : nwayExponent N h.val = 0 :=
    nwayExponent_eq_zero_of_lt N h.val hN h.isLt
  have hw : 1 ≤ nwayCoeff B N h.val := by
    simpa [he] using nwayCoeff_lower_bound B N h.val hB hN
  rw [le_div_iff₀ (nwayNormalizer_pos B N hB hN)]
  exact (one_sub_ratio_mul_nwayNormalizer_le_one B N hB hN hBN).trans hw

/-- Existential consequence of uniform first-atom concentration, convenient for constructing
one secretary hard family. -/
theorem first_atom_concentration_exists (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∀ ε : ℝ, 0 < ε → ∃ (B : ℕ) (hB : 2 ≤ B),
      ∀ h : Fin N,
        1 - ε <
          (((nwayDistribution B N hB hN h : Distribution) : Measure ℝ≥0)
            {nwayNode B h.val}).toReal := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (((2 : ℝ) ^ N) / ε)
  let B : ℕ := max (2 ^ (N + 1)) K
  have hBN : 2 ^ (N + 1) ≤ B := le_max_left _ _
  have hB : 2 ≤ B := by
    have hp : 2 ≤ 2 ^ (N + 1) := by
      have hm := pow_right_mono₀ (by simp : 1 ≤ (2 : ℕ))
        (Nat.le_add_left 1 N : 1 ≤ N + 1)
      simpa using hm
    exact hp.trans hBN
  have hKB : K ≤ B := le_max_right _ _
  have hratio : ((2 : ℝ) ^ N) / B < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < B)]
    have hK' : ((2 : ℝ) ^ N) / ε < B := hK.trans_le (by exact_mod_cast hKB)
    have hp : (2 : ℝ) ^ N < B * ε := (div_lt_iff₀ hε).mp hK'
    nlinarith
  refine ⟨B, hB, fun h ↦ ?_⟩
  exact (sub_lt_sub_left hratio 1).trans_le
    (nwayFirstAtom_ge_one_sub_ratio B N hB hN hBN h)

/-- `cor:first-atom-concentration`, `sections/secretary.tex`: exact eventual form of the
uniform-in-residue limit as the integer base `B → ∞`. For every error there is a threshold,
and every later admissible integer base works simultaneously for all residues. -/
theorem first_atom_concentration (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B → ∀ hB : 2 ≤ B,
      ∀ h : Fin N,
        1 - ε <
          (((nwayDistribution B N hB hN h : Distribution) : Measure ℝ≥0)
            {nwayNode B h.val}).toReal := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (((2 : ℝ) ^ N) / ε)
  let B₀ : ℕ := max (2 ^ (N + 1)) K
  refine ⟨B₀, ?_⟩
  intro B hB₀ hB h
  have hBN : 2 ^ (N + 1) ≤ B := (le_max_left _ _).trans hB₀
  have hKB : K ≤ B := (le_max_right _ _).trans hB₀
  have hratio : ((2 : ℝ) ^ N) / B < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < B)]
    have hK' : ((2 : ℝ) ^ N) / ε < B := hK.trans_le (by exact_mod_cast hKB)
    have hp : (2 : ℝ) ^ N < B * ε := (div_lt_iff₀ hε).mp hK'
    nlinarith
  exact (sub_lt_sub_left hratio 1).trans_le
    (nwayFirstAtom_ge_one_sub_ratio B N hB hN hBN h)

/-- A bundled form of the complete internal conclusion of the `N`-way separator. -/
structure NWaySeparatorConclusion (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) : Prop where
  normalizer_ge_one : 1 ≤ nwayNormalizer B N
  normalizer_lt_four : nwayNormalizer B N < 4
  finiteMoments : ∀ h : Fin N, HasFiniteMoments (nwayDistribution B N hB hN h)
  equalMoments : ∀ h h' : Fin N,
    MomentEquivalent (nwayDistribution B N hB hN h)
      (nwayDistribution B N hB hN h')
  residueSupport : ∀ h : Fin N,
    ((nwayDistribution B N hB hN h : Distribution) : Measure ℝ≥0)
      (nwaySupportClass B N h) = 1
  pairwiseTV : ∀ {h h' : Fin N}, h ≠ h' →
    manuscriptTV (nwayDistribution B N hB hN h)
      (nwayDistribution B N hB hN h') = 1
  coefficientBounds : ∀ j : ℕ,
    (B : ℝ) ^ (-(nwayExponent N j : ℤ)) ≤ nwayCoeff B N j ∧
      nwayCoeff B N j ≤ (2 : ℝ) ^ j * (B : ℝ) ^ (-(nwayExponent N j : ℤ))
  exponentGap : ∀ j : ℕ,
    (j : ℤ) - nwayExponent N j ≤ (N - 1 : ℕ)
  exponentEqualityRange : ∀ j : ℕ,
    ((j : ℤ) - nwayExponent N j = (N - 1 : ℕ) ↔
      N - 1 ≤ j ∧ j ≤ 2 * N - 2)

/-- `prop:key-prop-2-ext`, `sections/proofs.tex`: the extended `N`-way separator proposition,
including normalization, probability laws, moment matching, disjointness, and the quantitative
coefficient and exponent conclusions. -/
theorem key_prop_2_ext (B N : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N) :
    NWaySeparatorConclusion B N hB hN where
  normalizer_ge_one := nwayNormalizer_ge_one B N hB hN
  normalizer_lt_four := nwayNormalizer_lt_four B N hB hN
  finiteMoments := nwayDistribution_hasFiniteMoments B N hB hN
  equalMoments := nwayDistribution_momentEquivalent B N hB hN
  residueSupport := nwayDistribution_support B N hB hN
  pairwiseTV := fun hne ↦ nwayDistribution_manuscriptTV_eq_one B N hB hN hne
  coefficientBounds := fun j ↦
    ⟨nwayCoeff_lower_bound B N j hB hN, nwayCoeff_upper_bound B N j hB hN⟩
  exponentGap := fun j ↦ nway_index_sub_exponent_le N j hN
  exponentEqualityRange := fun j ↦ nway_index_sub_exponent_eq_iff N j hN

/-- `prop:key-prop-2` / `thm:nway-separator`, `sections/impossibility.tex`: the headline
separator theorem.  It is intentionally a separate declaration from the extended proposition
so both labeled manuscript environments have literal traceability. -/
theorem nway_separator (B N : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N) :
    NWaySeparatorConclusion B N hB hN :=
  key_prop_2_ext B N hB hN

end

end MomentAmbiguity
