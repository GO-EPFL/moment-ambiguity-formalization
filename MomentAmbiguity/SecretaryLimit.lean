import MomentAmbiguity.External.Secretary
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The classical secretary limit

This module discharges `External.ClassicalSecretaryLimit` from the exact finite formula in
`SecretaryDefs`.  The proof keeps the exceptional threshold `r = 1` separate.  For `r >= 2`,
the reciprocal block in `secretaryCandidate` is compared with the integral of `x |-> x⁻¹`.
After multiplication by `(r - 1) / m`, this gives a uniform error of at most `1 / m` from
`Real.negMulLog ((r - 1) / m)`.  The latter function has maximum `1 / exp 1`, and the threshold
`floor (m / exp 1) + 1` attains that maximum asymptotically.
-/

open scoped BigOperators Topology

namespace MomentAmbiguity

open Filter Set

noncomputable section

private lemma secretary_reciprocal_block_eq {m r : ℕ} (hr : 1 ≤ r) :
    (∑ t ∈ Finset.Icc r m, (((t - 1 : ℕ) : ℝ)⁻¹)) =
      ∑ k ∈ Finset.Ico (r - 1) m, ((k : ℝ)⁻¹) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have hshift := Finset.sum_Ico_add'
    (fun t : ℕ ↦ (((t - 1 : ℕ) : ℝ)⁻¹)) (r - 1) m 1
  simpa [Nat.sub_add_cancel hr] using hshift.symm

private lemma log_ratio_le_reciprocal_block {a m : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) :
    Real.log ((m : ℝ) / a) ≤ ∑ k ∈ Finset.Ico a m, ((k : ℝ)⁻¹) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt (ha.trans ham))
  calc
    Real.log ((m : ℝ) / a) = ∫ x : ℝ in (a : ℝ)..m, x⁻¹ := by
      rw [integral_inv_of_pos haR hmR]
    _ ≤ ∑ k ∈ Finset.Ico a m, ((k : ℝ)⁻¹) :=
      (inv_antitoneOn_Icc_right haR).integral_le_sum_Ico ham

private lemma reciprocal_block_le_inv_add_log_ratio {a m : ℕ}
    (ha : 1 ≤ a) (ham : a ≤ m) :
    (∑ k ∈ Finset.Ico a m, ((k : ℝ)⁻¹)) ≤
      (a : ℝ)⁻¹ + Real.log ((m : ℝ) / a) := by
  rcases ham.eq_or_lt with rfl | hamlt
  · simp
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hamlt, Finset.sum_insert (by simp)]
  have hsubset : Finset.Ico (a + 1) m ⊆ Finset.Ico (a + 1) (m + 1) :=
    Finset.Ico_subset_Ico le_rfl (Nat.le_succ m)
  calc
    (a : ℝ)⁻¹ + ∑ k ∈ Finset.Ico (a + 1) m, ((k : ℝ)⁻¹)
        ≤ (a : ℝ)⁻¹ + ∑ k ∈ Finset.Ico (a + 1) (m + 1), ((k : ℝ)⁻¹) := by
          exact add_le_add_right
            (Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
              intro i hi hnot
              exact inv_nonneg.mpr (show (0 : ℝ) ≤ (i : ℝ) by positivity)))
            ((a : ℝ)⁻¹)
    _ = (a : ℝ)⁻¹ + ∑ k ∈ Finset.Ico a m, (((k + 1 : ℕ) : ℝ)⁻¹) := by
      rw [Finset.sum_Ico_add' (fun k : ℕ ↦ ((k : ℝ)⁻¹)) a m 1]
    _ ≤ (a : ℝ)⁻¹ + ∫ x : ℝ in (a : ℝ)..m, x⁻¹ := by
      exact add_le_add_right
        ((inv_antitoneOn_Icc_right (show (0 : ℝ) < a by positivity)).sum_le_integral_Ico ham)
        ((a : ℝ)⁻¹)
    _ = (a : ℝ)⁻¹ + Real.log ((m : ℝ) / a) := by
      rw [integral_inv_of_pos (by exact_mod_cast Nat.zero_lt_of_lt ha)
        (by exact_mod_cast Nat.zero_lt_of_lt (ha.trans ham))]

private lemma scaled_log_ratio_eq_negMulLog {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    ((a : ℝ) / m) * Real.log ((m : ℝ) / a) =
      Real.negMulLog ((a : ℝ) / m) := by
  simp only [Real.negMulLog_def]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  ring

private lemma scaled_inv_eq_inv {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    ((a : ℝ) / m) * (a : ℝ)⁻¹ = (m : ℝ)⁻¹ := by
  field_simp

private lemma secretaryCandidate_lower {m r : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r)
    (hrm : r ≤ m) :
    Real.negMulLog (((r - 1 : ℕ) : ℝ) / m) ≤ secretaryCandidate m r := by
  have ha : 1 ≤ r - 1 := by omega
  have ham : r - 1 ≤ m := (Nat.sub_le r 1).trans hrm
  rw [secretaryCandidate, if_neg (by omega), secretary_reciprocal_block_eq (by omega)]
  rw [← scaled_log_ratio_eq_negMulLog ha hm]
  exact mul_le_mul_of_nonneg_left (log_ratio_le_reciprocal_block ha ham)
    (div_nonneg (by positivity) (by positivity))

private lemma secretaryCandidate_upper {m r : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r)
    (hrm : r ≤ m) :
    secretaryCandidate m r ≤
      Real.negMulLog (((r - 1 : ℕ) : ℝ) / m) + (m : ℝ)⁻¹ := by
  have ha : 1 ≤ r - 1 := by omega
  have ham : r - 1 ≤ m := (Nat.sub_le r 1).trans hrm
  rw [secretaryCandidate, if_neg (by omega), secretary_reciprocal_block_eq (by omega)]
  calc
    ((r - 1 : ℕ) : ℝ) / m * ∑ k ∈ Finset.Ico (r - 1) m, ((k : ℝ)⁻¹)
        ≤ ((r - 1 : ℕ) : ℝ) / m *
            (((r - 1 : ℕ) : ℝ)⁻¹ + Real.log ((m : ℝ) / (r - 1 : ℕ))) :=
      mul_le_mul_of_nonneg_left (reciprocal_block_le_inv_add_log_ratio ha ham)
        (div_nonneg (by positivity) (by positivity))
    _ = Real.negMulLog (((r - 1 : ℕ) : ℝ) / m) + (m : ℝ)⁻¹ := by
      rw [mul_add, scaled_inv_eq_inv ha hm, scaled_log_ratio_eq_negMulLog ha hm]
      ring

private lemma negMulLog_le_inv_exp_one {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x ≤ 1 / Real.exp 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Real.negMulLog_zero]
    exact div_nonneg zero_le_one (Real.exp_pos 1).le
  have h := Real.one_sub_inv_le_log_of_pos (mul_pos (Real.exp_pos 1) hx)
  rw [Real.log_mul (Real.exp_ne_zero 1) hx.ne', Real.log_exp] at h
  have hlog : -Real.log x ≤ (Real.exp 1 * x)⁻¹ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hx.le
  simp only [Real.negMulLog_def]
  calc
    -x * Real.log x = x * (-Real.log x) := by ring
    _ ≤ x * (Real.exp 1 * x)⁻¹ := hmul
    _ = 1 / Real.exp 1 := by field_simp

private lemma secretaryS_upper {m : ℕ} (hm : 1 ≤ m) :
    secretaryS m ≤ 1 / Real.exp 1 + (m : ℝ)⁻¹ := by
  rw [secretaryS_eq_max hm]
  refine Finset.sup'_le _ _ fun r hr ↦ ?_
  have hrange := Finset.mem_Icc.1 hr
  rcases eq_or_ne r 1 with rfl | hr1
  · rw [secretaryCandidate_one]
    exact le_add_of_nonneg_left (by positivity)
  · exact (secretaryCandidate_upper hm (by omega) hrange.2).trans
      (add_le_add (negMulLog_le_inv_exp_one
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl)

private def secretaryLimitThreshold (m : ℕ) : ℕ :=
  ⌊(Real.exp 1)⁻¹ * m⌋₊ + 1

private lemma eventually_secretaryLimitThreshold_admissible :
    ∀ᶠ m in atTop, 2 ≤ secretaryLimitThreshold m ∧ secretaryLimitThreshold m ≤ m := by
  have hqpos : 0 < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
  have hq_lt_one : (Real.exp 1)⁻¹ < 1 :=
    (inv_lt_one₀ (Real.exp_pos 1)).mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hfloor : Tendsto (fun m : ℕ ↦ ⌊(Real.exp 1)⁻¹ * m⌋₊) atTop atTop :=
    tendsto_nat_floor_mul_atTop _ hqpos
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with m hmFloor hm
  constructor
  · simpa [secretaryLimitThreshold] using Nat.add_le_add_right hmFloor 1
  · have hfloor_le : (⌊(Real.exp 1)⁻¹ * (m : ℝ)⌋₊ : ℝ) ≤
        (Real.exp 1)⁻¹ * m := Nat.floor_le (mul_nonneg hqpos.le (by positivity))
    have hmul_lt : (Real.exp 1)⁻¹ * (m : ℝ) < m := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hq_lt_one
        (show (0 : ℝ) < m by exact_mod_cast Nat.zero_lt_of_lt hm)
    have : ⌊(Real.exp 1)⁻¹ * (m : ℝ)⌋₊ < m := by exact_mod_cast hfloor_le.trans_lt hmul_lt
    simpa [secretaryLimitThreshold] using this

private lemma tendsto_secretaryLimitRatio :
    Tendsto (fun m : ℕ ↦ ((⌊(Real.exp 1)⁻¹ * m⌋₊ : ℝ) / m)) atTop
      (nhds ((Real.exp 1)⁻¹)) := by
  exact tendsto_nat_floor_mul_div_atTop (le_of_lt (inv_pos.mpr (Real.exp_pos 1)))
    |>.comp tendsto_natCast_atTop_atTop

private lemma negMulLog_inv_exp_one :
    Real.negMulLog ((Real.exp 1)⁻¹) = 1 / Real.exp 1 := by
  simp only [Real.negMulLog_def]
  rw [Real.log_inv, Real.log_exp]
  ring

private lemma tendsto_secretaryLimitLower :
    Tendsto
      (fun m : ℕ ↦ Real.negMulLog ((⌊(Real.exp 1)⁻¹ * m⌋₊ : ℝ) / m))
      atTop (nhds (1 / Real.exp 1)) := by
  rw [← negMulLog_inv_exp_one]
  exact Real.continuous_negMulLog.continuousAt.tendsto.comp tendsto_secretaryLimitRatio

private lemma tendsto_secretaryLimitUpper :
    Tendsto (fun m : ℕ ↦ 1 / Real.exp 1 + (m : ℝ)⁻¹) atTop
      (nhds (1 / Real.exp 1)) := by
  have hi : Tendsto (fun m : ℕ ↦ ((m : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.add hi

/-- The separate classical-value limit used by `cor:secretary-asymptotic`. -/
theorem classicalSecretaryLimit : External.ClassicalSecretaryLimit := by
  unfold External.ClassicalSecretaryLimit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_secretaryLimitLower tendsto_secretaryLimitUpper
  · filter_upwards [eventually_secretaryLimitThreshold_admissible] with m hm
    have hrOne : 1 ≤ secretaryLimitThreshold m := le_trans (by norm_num) hm.1
    have hmOne : 1 ≤ m := hrOne.trans hm.2
    have hle := Finset.le_sup' (secretaryCandidate m)
      (Finset.mem_Icc.2 ⟨hrOne, hm.2⟩)
    rw [← secretaryS_eq_max hmOne] at hle
    simpa only [secretaryLimitThreshold, Nat.add_sub_cancel] using
      (secretaryCandidate_lower hmOne hm.1 hm.2).trans hle
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact secretaryS_upper hm

#print axioms classicalSecretaryLimit

end

end MomentAmbiguity
