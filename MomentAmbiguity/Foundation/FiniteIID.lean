import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

/-!
# Finite i.i.d. sampling and permutation symmetrization

A uniformly sampled tuple is uniformly ordered conditional on its entries being distinct.
The proof below retains every label in the tuple: only the value-to-label assignment is
symmetrized. We provide both the simple `m^2 / k` collision estimate and the exact
birthday union bound `binom(m,2) / k`, obtained by counting each unordered pair once.
-/

open scoped BigOperators

namespace MomentAmbiguity

noncomputable section

/-- Average of a function over independent uniform choices of `m` indices from `Fin k`. -/
def finiteIIDAverage {m k : ℕ} (f : (Fin m → Fin k) → ℝ) : ℝ :=
  (Fintype.card (Fin m → Fin k) : ℝ)⁻¹ * ∑ a, f a

theorem finiteIIDAverage_eq_inv_card_sum {m k : ℕ} (f : (Fin m → Fin k) → ℝ) :
    finiteIIDAverage f =
      (Fintype.card (Fin m → Fin k) : ℝ)⁻¹ * ∑ a, f a := rfl

theorem finiteIIDAverage_eq_div_pow {m k : ℕ} (f : (Fin m → Fin k) → ℝ) :
    finiteIIDAverage f = (∑ a, f a) / (k : ℝ)^m := by
  simp [finiteIIDAverage, div_eq_mul_inv, mul_comm]

/-- Averaging over permutations uses the same normalization as uniform permutation measure. -/
theorem finite_permutation_average_eq {m : ℕ} (f : Equiv.Perm (Fin m) → ℝ) :
    (∑ φ, f φ) / (m.factorial : ℝ) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ * ∑ φ, f φ := by
  simp [Fintype.card_perm, div_eq_mul_inv, mul_comm]

/-- Removing one coordinate injects the tuples with a fixed collision into arbitrary
assignments to the remaining coordinates. -/
theorem card_collision_le {m k : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Fintype.card {a : Fin m → Fin k // a i = a j} ≤ k^(m - 1) := by
  classical
  let restriction : {a : Fin m → Fin k // a i = a j} →
      ({t : Fin m // t ≠ j} → Fin k) := fun a t ↦ a.val t.val
  have hr : Function.Injective restriction := by
    intro a b hab
    apply Subtype.ext
    funext t
    by_cases ht : t = j
    · subst t
      calc
        a.val j = a.val i := a.property.symm
        _ = b.val i := congrFun hab ⟨i, hij⟩
        _ = b.val j := b.property
    · exact congrFun hab ⟨t, ht⟩
  have hc : Fintype.card {t : Fin m // t ≠ j} = m - 1 := by
    simp [Fintype.card_subtype_compl]
  simpa [Fintype.card_fun, hc] using Fintype.card_le_of_injective restriction hr

/-- Indicator of a collision in a finite tuple. -/
def finiteCollision {m k : ℕ} (a : Fin m → Fin k) : ℝ :=
  if Function.Injective a then 0 else 1

/-- The union bound for collisions, proved by counting tied coordinates. -/
theorem sum_finiteCollision_le {m k : ℕ} :
    (∑ a : Fin m → Fin k, finiteCollision a) ≤
      (m : ℝ)^2 * (k : ℝ)^(m - 1) := by
  classical
  have pointwise (a : Fin m → Fin k) :
      finiteCollision a ≤ ∑ i : Fin m, ∑ j : Fin m,
        if i ≠ j ∧ a i = a j then (1 : ℝ) else 0 := by
    by_cases ha : Function.Injective a
    · simp only [finiteCollision, if_pos ha]
      positivity
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp ha
      simp only [finiteCollision, if_neg ha]
      calc
        (1 : ℝ) = if i ≠ j ∧ a i = a j then 1 else 0 := by simp [hne, heq]
        _ ≤ ∑ j' : Fin m, if i ≠ j' ∧ a i = a j' then 1 else 0 :=
          Finset.single_le_sum
            (f := fun j' : Fin m ↦ if i ≠ j' ∧ a i = a j' then (1 : ℝ) else 0)
            (fun _ _ ↦ by positivity) (Finset.mem_univ j)
        _ ≤ ∑ i' : Fin m, ∑ j' : Fin m,
            if i' ≠ j' ∧ a i' = a j' then 1 else 0 :=
          Finset.single_le_sum
            (f := fun i' : Fin m ↦ ∑ j' : Fin m,
              if i' ≠ j' ∧ a i' = a j' then (1 : ℝ) else 0)
            (fun _ _ ↦ by positivity) (Finset.mem_univ i)
  have pairwise (i j : Fin m) :
      (∑ a : Fin m → Fin k, if i ≠ j ∧ a i = a j then (1 : ℝ) else 0) ≤
        (k : ℝ)^(m - 1) := by
    by_cases hij : i = j
    · subst j
      simp
    · simpa [hij, Fintype.card_subtype, Nat.cast_pow] using
        (show (Fintype.card {a : Fin m → Fin k // a i = a j} : ℝ) ≤
          (k : ℝ)^(m - 1) by exact_mod_cast card_collision_le i j hij)
  calc
    (∑ a : Fin m → Fin k, finiteCollision a) ≤
        ∑ a : Fin m → Fin k, ∑ i : Fin m, ∑ j : Fin m,
          if i ≠ j ∧ a i = a j then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun a _ ↦ pointwise a)
    _ = ∑ i : Fin m, ∑ j : Fin m, ∑ a : Fin m → Fin k,
          if i ≠ j ∧ a i = a j then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, (k : ℝ)^(m - 1) := by
      exact Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ pairwise i j))
    _ = (m : ℝ)^2 * (k : ℝ)^(m - 1) := by simp; ring


/-- Precomposing all index tuples with a fixed label permutation preserves their sum. -/
theorem sum_comp_finite_permutation {m k : ℕ} (f : (Fin m → Fin k) → ℝ)
    (φ : Equiv.Perm (Fin m)) :
    (∑ a : Fin m → Fin k, f (a ∘ φ)) = ∑ a, f a := by
  classical
  let e : (Fin m → Fin k) ≃ (Fin m → Fin k) :=
    { toFun := fun a ↦ a ∘ φ
      invFun := fun a ↦ a ∘ φ.symm
      left_inv := fun a ↦ by funext i; simp
      right_inv := fun a ↦ by funext i; simp }
  exact e.sum_comp f

/-- The total over all tuples equals the total of their permutation averages. -/
theorem sum_permutation_average {m k : ℕ} (f : (Fin m → Fin k) → ℝ) :
    (∑ a : Fin m → Fin k,
      (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ)) = ∑ a, f a := by
  classical
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [sum_comp_finite_permutation, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero m)

/-- A label-sensitive bound for every distinct tuple, averaged only over its assignments,
transfers to independent sampling with replacement. -/
theorem finiteIIDAverage_le_of_permutation_average {m k : ℕ}
    (hm : 1 ≤ m) (hk : 0 < k) (f : (Fin m → Fin k) → ℝ)
    (hf : ∀ a, f a ≤ 1) {s : ℝ} (hs : 0 ≤ s)
    (hperm : ∀ a : Fin m → Fin k, Function.Injective a →
      (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) ≤ s) :
    finiteIIDAverage f ≤ s + (m : ℝ)^2 / k := by
  classical
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : (0 : ℝ) < (k : ℝ)^m := pow_pos hkp m
  have hlocal (a : Fin m → Fin k) :
      (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) ≤
        s + finiteCollision a := by
    by_cases ha : Function.Injective a
    · simpa [finiteCollision, ha] using hperm a ha
    · have hsum : (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) ≤
          (m.factorial : ℝ) := by
        calc
          _ ≤ ∑ _φ : Equiv.Perm (Fin m), (1 : ℝ) :=
            Finset.sum_le_sum (fun φ _ ↦ hf (a ∘ φ))
          _ = _ := by simp [Fintype.card_perm]
      have havg : (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) /
          (m.factorial : ℝ) ≤ 1 := (div_le_one hfact).2 hsum
      simp only [finiteCollision, if_neg ha]
      linarith
  have htotal : (∑ a : Fin m → Fin k, f a) ≤
      (k : ℝ)^m * s + (m : ℝ)^2 * (k : ℝ)^(m - 1) := by
    calc
      _ = ∑ a : Fin m → Fin k,
          (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) :=
        (sum_permutation_average f).symm
      _ ≤ ∑ a : Fin m → Fin k, (s + finiteCollision a) :=
        Finset.sum_le_sum (fun a _ ↦ hlocal a)
      _ = (k : ℝ)^m * s + ∑ a : Fin m → Fin k, finiteCollision a := by
        simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl sum_finiteCollision_le
  rw [finiteIIDAverage_eq_div_pow]
  apply (div_le_iff₀ hpow).2
  have hexp : (k : ℝ)^m = (k : ℝ)^(m - 1) * k := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  calc
    (∑ a : Fin m → Fin k, f a) ≤
        (k : ℝ)^m * s + (m : ℝ)^2 * (k : ℝ)^(m - 1) := htotal
    _ = (s + (m : ℝ)^2 / k) * (k : ℝ)^m := by
      rw [hexp]
      field_simp


/-- The number of unordered pairs of distinct coordinates, counted by their increasing order. -/
theorem sum_finite_lt_indicator (m : ℕ) :
    (∑ j : Fin m, ∑ i : Fin m, if i < j then (1 : ℝ) else 0) =
      (Nat.choose m 2 : ℝ) := by
  have hinner (j : Fin m) : (∑ i : Fin m, if i < j then (1 : ℝ) else 0) = j.val := by
    simp [Finset.filter_gt_eq_Iio]
  simp_rw [hinner]
  rw [← Nat.cast_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i), Finset.sum_range_id,
    ← Nat.choose_two_right]

/-- The birthday union bound counts each unordered colliding pair just once. -/
theorem sum_finiteCollision_le_choose {m k : ℕ} :
    (∑ a : Fin m → Fin k, finiteCollision a) ≤
      (Nat.choose m 2 : ℝ) * (k : ℝ)^(m - 1) := by
  classical
  have pointwise (a : Fin m → Fin k) :
      finiteCollision a ≤ ∑ j : Fin m, ∑ i : Fin m,
        if i < j ∧ a i = a j then (1 : ℝ) else 0 := by
    by_cases ha : Function.Injective a
    · simp only [finiteCollision, if_pos ha]
      positivity
    · obtain ⟨u, v, heq, hne⟩ := Function.not_injective_iff.mp ha
      have hex : ∃ i j, i < j ∧ a i = a j := by
        rcases lt_or_gt_of_ne hne with huv | hvu
        · exact ⟨u, v, huv, heq⟩
        · exact ⟨v, u, hvu, heq.symm⟩
      obtain ⟨i, j, hij, heq⟩ := hex
      simp only [finiteCollision, if_neg ha]
      calc
        (1 : ℝ) = if i < j ∧ a i = a j then 1 else 0 := by simp [hij, heq]
        _ ≤ ∑ i' : Fin m, if i' < j ∧ a i' = a j then 1 else 0 :=
          Finset.single_le_sum
            (f := fun i' : Fin m ↦ if i' < j ∧ a i' = a j then (1 : ℝ) else 0)
            (fun _ _ ↦ by positivity) (Finset.mem_univ i)
        _ ≤ ∑ j' : Fin m, ∑ i' : Fin m,
            if i' < j' ∧ a i' = a j' then 1 else 0 :=
          Finset.single_le_sum
            (f := fun j' : Fin m ↦ ∑ i' : Fin m,
              if i' < j' ∧ a i' = a j' then (1 : ℝ) else 0)
            (fun _ _ ↦ by positivity) (Finset.mem_univ j)
  have pairwise (i j : Fin m) :
      (∑ a : Fin m → Fin k, if i < j ∧ a i = a j then (1 : ℝ) else 0) ≤
        if i < j then (k : ℝ)^(m - 1) else 0 := by
    by_cases hij : i < j
    · simpa [hij, Fintype.card_subtype, Nat.cast_pow] using
        (show (Fintype.card {a : Fin m → Fin k // a i = a j} : ℝ) ≤
          (k : ℝ)^(m - 1) by exact_mod_cast card_collision_le i j (ne_of_lt hij))
    · simp [hij]
  calc
    (∑ a : Fin m → Fin k, finiteCollision a) ≤
        ∑ a : Fin m → Fin k, ∑ j : Fin m, ∑ i : Fin m,
          if i < j ∧ a i = a j then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun a _ ↦ pointwise a)
    _ = ∑ j : Fin m, ∑ i : Fin m, ∑ a : Fin m → Fin k,
          if i < j ∧ a i = a j then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ ≤ ∑ j : Fin m, ∑ i : Fin m,
        if i < j then (k : ℝ)^(m - 1) else 0 := by
      exact Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun i _ ↦ pairwise i j))
    _ = (∑ j : Fin m, ∑ i : Fin m, if i < j then (1 : ℝ) else 0) *
        (k : ℝ)^(m - 1) := by
      simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    _ = (Nat.choose m 2 : ℝ) * (k : ℝ)^(m - 1) := by
      rw [sum_finite_lt_indicator]

/-- Exact birthday-bound version of permutation symmetrization, matching the manuscript's
`binom(m,2)/k` collision error. -/
theorem finiteIIDAverage_le_of_permutation_average_choose {m k : ℕ}
    (hm : 1 ≤ m) (hk : 0 < k) (f : (Fin m → Fin k) → ℝ)
    (hf : ∀ a, f a ≤ 1) {s : ℝ} (hs : 0 ≤ s)
    (hperm : ∀ a : Fin m → Fin k, Function.Injective a →
      (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) ≤ s) :
    finiteIIDAverage f ≤ s + (Nat.choose m 2 : ℝ) / k := by
  classical
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : (0 : ℝ) < (k : ℝ)^m := pow_pos hkp m
  have hlocal (a : Fin m → Fin k) :
      (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) ≤
        s + finiteCollision a := by
    by_cases ha : Function.Injective a
    · simpa [finiteCollision, ha] using hperm a ha
    · have hsum : (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) ≤
          (m.factorial : ℝ) := by
        calc
          _ ≤ ∑ _φ : Equiv.Perm (Fin m), (1 : ℝ) :=
            Finset.sum_le_sum (fun φ _ ↦ hf (a ∘ φ))
          _ = _ := by simp [Fintype.card_perm]
      have havg : (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) /
          (m.factorial : ℝ) ≤ 1 := (div_le_one hfact).2 hsum
      simp only [finiteCollision, if_neg ha]
      linarith
  have htotal : (∑ a : Fin m → Fin k, f a) ≤
      (k : ℝ)^m * s + (Nat.choose m 2 : ℝ) * (k : ℝ)^(m - 1) := by
    calc
      _ = ∑ a : Fin m → Fin k,
          (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) :=
        (sum_permutation_average f).symm
      _ ≤ ∑ a : Fin m → Fin k, (s + finiteCollision a) :=
        Finset.sum_le_sum (fun a _ ↦ hlocal a)
      _ = (k : ℝ)^m * s + ∑ a : Fin m → Fin k, finiteCollision a := by
        simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl sum_finiteCollision_le_choose
  rw [finiteIIDAverage_eq_div_pow]
  apply (div_le_iff₀ hpow).2
  have hexp : (k : ℝ)^m = (k : ℝ)^(m - 1) * k := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  calc
    (∑ a : Fin m → Fin k, f a) ≤
        (k : ℝ)^m * s + (Nat.choose m 2 : ℝ) * (k : ℝ)^(m - 1) := htotal
    _ = (s + (Nat.choose m 2 : ℝ) / k) * (k : ℝ)^m := by
      rw [hexp]
      field_simp

end
end MomentAmbiguity
