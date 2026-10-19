import MomentAmbiguity.Prophet.Blocks

/-!
# Dyadic averaging for prophet switch instances

The source averages switch points with weights proportional to `2⁻ᵗ`.  We work with the
unnormalized weights, which cancels the common normalizer and makes the zero-benchmark-safe
multiplication argument transparent.
-/

open scoped BigOperators

namespace MomentAmbiguity

open Finset

noncomputable section

/-- Zero-indexed version of the manuscript weight `2⁻ᵗ`, namely `2^{-(j+1)}`. -/
def dyadicSwitchWeight (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

theorem dyadicSwitchWeight_pos (j : ℕ) : 0 < dyadicSwitchWeight j := by
  unfold dyadicSwitchWeight
  positivity

theorem summable_dyadicSwitchWeight : Summable dyadicSwitchWeight := by
  have h := (summable_geometric_of_norm_lt_one (K := ℝ)
    (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_left (1 / 2 : ℝ)
  apply h.congr
  intro j
  simp [dyadicSwitchWeight, pow_succ, mul_comm]

theorem tsum_dyadicSwitchWeight : ∑' j : ℕ, dyadicSwitchWeight j = 1 := by
  rw [show dyadicSwitchWeight = fun j : ℕ ↦ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j by
    funext j
    simp [dyadicSwitchWeight, pow_succ, mul_comm]]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

theorem sum_dyadicSwitchWeight_le_one (L : ℕ) :
    (∑ j : Fin L, dyadicSwitchWeight j) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (∑ j ∈ range L, dyadicSwitchWeight j) ≤ ∑' j : ℕ, dyadicSwitchWeight j :=
      summable_dyadicSwitchWeight.sum_le_tsum _
        (fun j hj ↦ (dyadicSwitchWeight_pos j).le)
    _ = 1 := tsum_dyadicSwitchWeight

theorem dyadicSwitchWeight_mul_two_pow (j : ℕ) :
    dyadicSwitchWeight j * (2 : ℝ) ^ j = 1 / 2 := by
  unfold dyadicSwitchWeight
  rw [pow_succ]
  have htwo : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    (1 / 2 : ℝ) ^ j * (1 / 2) * 2 ^ j =
        ((1 / 2 : ℝ) ^ j * 2 ^ j) * (1 / 2) := by ring
    _ = 1 / 2 := by
      have hinv : (1 / (2 : ℝ) ^ j) * 2 ^ j = 1 := by
        rw [div_eq_mul_inv, one_mul]
        exact inv_mul_cancel₀ htwo
      rw [one_div_pow, hinv, one_mul]

private theorem sum_tail_eq_Ico {L : ℕ} (j : Fin L) :
    (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t else 0) =
      ∑ t ∈ Ico j.1 L, dyadicSwitchWeight t := by
  rw [show (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t else 0) =
      ∑ t ∈ range L, if j.1 ≤ t then dyadicSwitchWeight t else 0 by
    simpa using Fin.sum_univ_eq_sum_range
      (fun t : ℕ ↦ if j.1 ≤ t then dyadicSwitchWeight t else 0) L]
  rw [← sum_filter]
  apply sum_congr
  · ext t
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  · intro t ht
    rfl

/-- The remaining unnormalized mass after block `j` is at most `2⁻ʲ`. -/
theorem dyadicSwitchWeight_tail_le {L : ℕ} (j : Fin L) :
    (∑ t : Fin L, if j ≤ t then dyadicSwitchWeight t else 0) ≤
      (1 / 2 : ℝ) ^ j.1 := by
  rw [sum_tail_eq_Ico j, sum_Ico_eq_sum_range]
  have hfinite : (∑ k ∈ range (L - j.1), dyadicSwitchWeight k) ≤ 1 := by
    calc
      (∑ k ∈ range (L - j.1), dyadicSwitchWeight k) ≤
          ∑' k : ℕ, dyadicSwitchWeight k :=
        summable_dyadicSwitchWeight.sum_le_tsum _
          (fun k hk ↦ (dyadicSwitchWeight_pos k).le)
      _ = 1 := tsum_dyadicSwitchWeight
  calc
    (∑ k ∈ range (L - j.1), dyadicSwitchWeight (j.1 + k)) =
        (1 / 2 : ℝ) ^ j.1 *
          ∑ k ∈ range (L - j.1), dyadicSwitchWeight k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      simp only [dyadicSwitchWeight, ← pow_add]
      congr 1
    _ ≤ (1 / 2 : ℝ) ^ j.1 * 1 :=
      mul_le_mul_of_nonneg_left hfinite (pow_nonneg (by norm_num) _)
    _ = _ := mul_one _

/-- A positive weighted-average comparison has a pointwise witness. -/
theorem exists_pointwise_le_of_weighted_sum_le {L : ℕ} (hL : 1 ≤ L)
    (w R Q : Fin L → ℝ) (C : ℝ) (hw : ∀ t, 0 < w t)
    (hsum : (∑ t, w t * R t) ≤ C * ∑ t, w t * Q t) :
    ∃ t : Fin L, R t ≤ C * Q t := by
  letI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp (by omega)
  by_contra hnone
  push Not at hnone
  have hstrict : (∑ t, w t * (C * Q t)) < ∑ t, w t * R t := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro t ht
    exact mul_lt_mul_of_pos_left (hnone t) (hw t)
  have hleft : (∑ t, w t * (C * Q t)) = C * ∑ t, w t * Q t := by
    rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    ring
  rw [hleft] at hstrict
  linarith

/-- Weighted benchmark lower bound for exponentially growing block sizes. -/
theorem weighted_dyadic_benchmark_lower {L : ℕ} (N kappa : ℝ)
    (Q : Fin L → ℝ)
    (hQ : ∀ t, 3 * kappa * (N * (2 : ℝ) ^ t.1) ≤ Q t) :
    3 * kappa * N * (L : ℝ) / 2 ≤
      ∑ t : Fin L, dyadicSwitchWeight t * Q t := by
  calc
    3 * kappa * N * (L : ℝ) / 2 =
        ∑ _t : Fin L, (3 * kappa * N / 2) := by simp; ring
    _ = ∑ t : Fin L, dyadicSwitchWeight t *
        (3 * kappa * (N * (2 : ℝ) ^ t.1)) := by
      apply sum_congr rfl
      intro t ht
      rw [show dyadicSwitchWeight t.1 *
          (3 * kappa * (N * (2 : ℝ) ^ t.1)) =
          3 * kappa * N *
            (dyadicSwitchWeight t.1 * (2 : ℝ) ^ t.1) by ring,
        dyadicSwitchWeight_mul_two_pow]
      ring
    _ ≤ ∑ t : Fin L, dyadicSwitchWeight t * Q t := by
      apply sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hQ t) (dyadicSwitchWeight_pos t).le

/-- Geometric reciprocal block sizes give the manuscript's `12/N` tail sum. -/
theorem sum_six_div_prophetBlockSize_le {N L : ℕ} (hN : 0 < N) :
    (∑ j : Fin L, 6 / (prophetBlockSize N j.1 : ℝ)) ≤ 12 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (∑ j : Fin L, (1 / 2 : ℝ) ^ j.1) ≤ 2 := by
    calc
      (∑ j : Fin L, (1 / 2 : ℝ) ^ j.1) =
          2 * ∑ j : Fin L, dyadicSwitchWeight j.1 := by
        rw [mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [dyadicSwitchWeight, pow_succ]
        ring
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left
        (sum_dyadicSwitchWeight_le_one L) (by norm_num)
      _ = 2 := by ring
  calc
    (∑ j : Fin L, 6 / (prophetBlockSize N j.1 : ℝ)) =
        (6 / (N : ℝ)) * ∑ j : Fin L, (1 / 2 : ℝ) ^ j.1 := by
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [prophetBlockSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [one_div_pow]
      field_simp
    _ ≤ (6 / (N : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) hNR.le)
    _ = 12 / (N : ℝ) := by ring

end

end MomentAmbiguity
