import Mathlib

/-!
Elementary series and product estimates used by the `N`-way separator.

The indices in this file start at zero.  Thus `dyadicFactor m` is the
manuscript's factor `1 - 2⁻ᵐ` with manuscript index `m + 1`.
-/

open scoped BigOperators Topology

namespace MomentAmbiguity

open Filter Finset

noncomputable section

/-- The positive dyadic term `2^{-(m+1)}`. -/
def dyadicTerm (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (m + 1)

/-- A factor in the Euler product occurring in `lem:N-class-moment-matching`. -/
def dyadicFactor (m : ℕ) : ℝ := 1 - dyadicTerm m

lemma dyadicTerm_nonneg (m : ℕ) : 0 ≤ dyadicTerm m := by
  simp [dyadicTerm]

lemma dyadicTerm_le_one (m : ℕ) : dyadicTerm m ≤ 1 := by
  simp only [dyadicTerm]
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma dyadicFactor_nonneg (m : ℕ) : 0 ≤ dyadicFactor m := by
  exact sub_nonneg.mpr (dyadicTerm_le_one m)

/-- The elementary finite inequality behind the exact `9/32` bound. -/
lemma one_sub_sum_le_prod_one_sub {s : Finset ℕ} {a : ℕ → ℝ}
    (ha₀ : ∀ i ∈ s, 0 ≤ a i) (ha₁ : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [sum_insert hx, prod_insert hx]
      have hax₀ : 0 ≤ a x := ha₀ x (mem_insert_self x s)
      have hax₁ : a x ≤ 1 := ha₁ x (mem_insert_self x s)
      have htail := ih
        (fun i hi ↦ ha₀ i (mem_insert_of_mem hi))
        (fun i hi ↦ ha₁ i (mem_insert_of_mem hi))
      have hfac : 0 ≤ 1 - a x := sub_nonneg.mpr hax₁
      calc
        1 - (a x + ∑ i ∈ s, a i) ≤
            (1 - a x) * (1 - ∑ i ∈ s, a i) := by
              nlinarith [sum_nonneg fun i hi ↦ ha₀ i (mem_insert_of_mem hi)]
        _ ≤ (1 - a x) * (∏ i ∈ s, (1 - a i)) :=
          mul_le_mul_of_nonneg_left htail hfac

lemma summable_dyadicTerm : Summable dyadicTerm := by
  change Summable (fun m : ℕ ↦ (1 / 2 : ℝ) ^ (m + 1))
  simpa only [pow_succ, mul_comm] using
    summable_geometric_two.mul_left (1 / 2 : ℝ)

lemma summable_dyadic_tail : Summable (fun m : ℕ ↦ (1 / 2 : ℝ) ^ (m + 3)) := by
  simpa only [show ∀ m : ℕ, m + 3 = 3 + m by omega, pow_add, show (1 / 2 : ℝ) ^ 3 = 1 / 8 by norm_num]
    using summable_geometric_two.mul_left (1 / 8 : ℝ)

lemma tsum_dyadic_tail : ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 3) = 1 / 4 := by
  have hgeom : ∑' m : ℕ, (1 / 2 : ℝ) ^ m = 2 := by
    norm_num [tsum_geometric_of_norm_lt_one]
  calc
    ∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 3) =
        ∑' m : ℕ, (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ m := by
          congr with m
          rw [show m + 3 = 3 + m by omega, pow_add]
          norm_num
    _ = (1 / 8 : ℝ) * ∑' m : ℕ, (1 / 2 : ℝ) ^ m := tsum_mul_left
    _ = 1 / 4 := by rw [hgeom]; norm_num

lemma dyadic_tail_sum_le (M : ℕ) :
    ∑ m ∈ range M, (1 / 2 : ℝ) ^ (m + 3) ≤ 1 / 4 := by
  rw [← tsum_dyadic_tail]
  exact summable_dyadic_tail.sum_le_tsum (range M) (fun _ _ ↦ by positivity)

lemma dyadic_tail_product_ge (M : ℕ) :
    3 / 4 ≤ ∏ m ∈ range M, (1 - (1 / 2 : ℝ) ^ (m + 3)) := by
  have hprod := one_sub_sum_le_prod_one_sub
    (s := range M) (a := fun m : ℕ ↦ (1 / 2 : ℝ) ^ (m + 3))
    (fun _ _ ↦ by positivity)
    (fun m _ ↦ pow_le_one₀ (by norm_num) (by norm_num))
  linarith [dyadic_tail_sum_le M]

/-- `sections/proofs.tex`, proof of `lem:N-class-moment-matching`:
every finite partial product is at least `9/32`. -/
theorem dyadic_partial_product_ge_nine_thirty_two (M : ℕ) :
    9 / 32 ≤ ∏ m ∈ range M, dyadicFactor m := by
  by_cases hM : M < 2
  · interval_cases M <;> norm_num [dyadicFactor, dyadicTerm]
  · have htwo : 2 ≤ M := Nat.le_of_not_gt hM
    obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le htwo
    have htail := dyadic_tail_product_ge K
    rw [prod_range_add]
    have hprodEq :
        ∏ x ∈ range K, dyadicFactor (2 + x) =
          ∏ x ∈ range K, (1 - (1 / 2 : ℝ) ^ (x + 3)) := by
      apply prod_congr rfl
      intro x hx
      simp only [dyadicFactor, dyadicTerm]
      congr 2
      omega
    rw [hprodEq]
    norm_num [dyadicFactor, dyadicTerm] at ⊢
    nlinarith

/-- The dyadic Euler product is convergent. -/
theorem multipliable_dyadicFactor : Multipliable dyadicFactor := by
  have hnorm : Summable (fun m : ℕ ↦ ‖-(dyadicTerm m)‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg, dyadicTerm_nonneg] using summable_dyadicTerm
  change Multipliable (fun m : ℕ ↦ (1 : ℝ) + -(dyadicTerm m))
  exact multipliable_one_add_of_summable hnorm

/-- `sections/proofs.tex`, proof of `lem:N-class-moment-matching`:
the requested exact normalization-product lower bound
`\prod_{m\ge 1}(1-2^{-m}) \ge 9/32`. -/
theorem dyadic_infinite_product_ge_nine_thirty_two :
    9 / 32 ≤ ∏' m : ℕ, dyadicFactor m := by
  exact ge_of_tendsto' multipliable_dyadicFactor.hasProd.tendsto_prod_nat
    dyadic_partial_product_ge_nine_thirty_two

lemma dyadicTerm_le_half (m : ℕ) : dyadicTerm m ≤ 1 / 2 := by
  rw [dyadicTerm]
  simpa only [pow_one] using
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (by omega : 1 ≤ m + 1)

lemma dyadicFactor_pos (m : ℕ) : 0 < dyadicFactor m := by
  unfold dyadicFactor
  linarith [dyadicTerm_le_half m]

lemma dyadicFactor_inv_sub_one_nonneg (m : ℕ) :
    0 ≤ (dyadicFactor m)⁻¹ - 1 := by
  have hf : dyadicFactor m ≤ 1 := by simp [dyadicFactor, dyadicTerm_nonneg]
  exact sub_nonneg.mpr ((one_le_inv₀ (dyadicFactor_pos m)).2 hf)

lemma dyadicFactor_inv_sub_one_le (m : ℕ) :
    (dyadicFactor m)⁻¹ - 1 ≤ 2 * dyadicTerm m := by
  have ha := dyadicTerm_nonneg m
  have hf : (1 / 2 : ℝ) ≤ dyadicFactor m := by
    unfold dyadicFactor
    linarith [dyadicTerm_le_half m]
  have hid : (dyadicFactor m)⁻¹ - 1 = dyadicTerm m / dyadicFactor m := by
    field_simp [dyadicFactor_pos m |>.ne']
    simp [dyadicFactor]
  rw [hid]
  calc
    dyadicTerm m / dyadicFactor m ≤ dyadicTerm m / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left ha (by norm_num) hf
    _ = 2 * dyadicTerm m := by ring

/-- The reciprocal Euler product is convergent. -/
theorem multipliable_dyadicFactor_inv : Multipliable (fun m : ℕ ↦ (dyadicFactor m)⁻¹) := by
  have hnorm : Summable (fun m : ℕ ↦ ‖(dyadicFactor m)⁻¹ - 1‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
      (summable_dyadicTerm.mul_left 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (dyadicFactor_inv_sub_one_nonneg m)]
    exact dyadicFactor_inv_sub_one_le m
  have hm := multipliable_one_add_of_summable hnorm
  have heq : (fun m : ℕ ↦ (1 : ℝ) + ((dyadicFactor m)⁻¹ - 1)) =
      fun m : ℕ ↦ (dyadicFactor m)⁻¹ := by
    funext m
    ring
  rw [heq] at hm
  exact hm

theorem tprod_dyadicFactor_inv :
    (∏' m : ℕ, (dyadicFactor m)⁻¹) = (∏' m : ℕ, dyadicFactor m)⁻¹ := by
  have hmul := multipliable_dyadicFactor.tprod_mul multipliable_dyadicFactor_inv
  have hone : (∏' m : ℕ, dyadicFactor m * (dyadicFactor m)⁻¹) = 1 := by
    have hfun : (fun m : ℕ ↦ dyadicFactor m * (dyadicFactor m)⁻¹) = fun _ ↦ (1 : ℝ) := by
      funext m
      exact mul_inv_cancel₀ (dyadicFactor_pos m).ne'
    rw [hfun]
    simp
  exact eq_inv_of_mul_eq_one_right (hmul.symm.trans hone)

/-- `lem:N-class-moment-matching`: the exact companion upper bound
`\prod_{m\ge1}(1-2^{-m})^{-1} \le 32/9`. -/
theorem dyadic_reciprocal_infinite_product_le_thirty_two_nine :
    (∏' m : ℕ, (dyadicFactor m)⁻¹) ≤ 32 / 9 := by
  rw [tprod_dyadicFactor_inv]
  have hp : 0 < ∏' m : ℕ, dyadicFactor m :=
    (by norm_num : (0 : ℝ) < 9 / 32).trans_le
      dyadic_infinite_product_ge_nine_thirty_two
  have hconst : (9 / 32 : ℝ)⁻¹ = 32 / 9 := by norm_num
  rw [← hconst]
  exact (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 9 / 32)).2
    dyadic_infinite_product_ge_nine_thirty_two

theorem dyadic_reciprocal_infinite_product_lt_four :
    (∏' m : ℕ, (dyadicFactor m)⁻¹) < 4 :=
  dyadic_reciprocal_infinite_product_le_thirty_two_nine.trans_lt (by norm_num)

/-- Finite companion to the exact reciprocal-product bound. -/
theorem dyadic_reciprocal_partial_product_le_thirty_two_nine (M : ℕ) :
    (∏ m ∈ Finset.range M, (dyadicFactor m)⁻¹) ≤ 32 / 9 := by
  rw [Finset.prod_inv_distrib]
  have hp : 0 < ∏ m ∈ Finset.range M, dyadicFactor m :=
    Finset.prod_pos fun m hm ↦ dyadicFactor_pos m
  have hconst : (9 / 32 : ℝ)⁻¹ = 32 / 9 := by norm_num
  rw [← hconst]
  exact (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 9 / 32)).2
    (dyadic_partial_product_ge_nine_thirty_two M)

end
end MomentAmbiguity
