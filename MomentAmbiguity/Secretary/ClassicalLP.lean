import MomentAmbiguity.Secretary.Model
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Finite linear-programming bound for the classical secretary problem

This module is deliberately independent of the policy implementation.  It proves the finite
optimization inequality needed by the classical-secretary bridge from nonnegative record-stop
masses and their adaptedness constraints.
-/

open scoped BigOperators

namespace MomentAmbiguity

noncomputable section

/-- The reciprocal tail `sum_{k = j}^{m-1} 1/k`. -/
private def secretaryReciprocalTail (m j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico j m, ((k : ℝ)⁻¹)

private lemma secretaryReciprocalTail_nonneg (m j : ℕ) :
    0 ≤ secretaryReciprocalTail m j := by
  exact Finset.sum_nonneg fun k hk ↦ inv_nonneg.mpr (Nat.cast_nonneg k)

private lemma secretaryReciprocalTail_antitone {m a b : ℕ} (hab : a ≤ b) :
    secretaryReciprocalTail m b ≤ secretaryReciprocalTail m a := by
  unfold secretaryReciprocalTail
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico hab le_rfl) (by
      intro k hk hnot
      exact inv_nonneg.mpr (Nat.cast_nonneg k))

private lemma secretaryReciprocalTail_eq_inv_add {m k : ℕ} (hk : k < m) :
    secretaryReciprocalTail m k = (k : ℝ)⁻¹ + secretaryReciprocalTail m (k + 1) := by
  unfold secretaryReciprocalTail
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hk, Finset.sum_insert (by simp)]

private lemma one_le_secretaryReciprocalTail_one {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ secretaryReciprocalTail m 1 := by
  unfold secretaryReciprocalTail
  have hmem : 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
  have hle : ((1 : ℕ) : ℝ)⁻¹ ≤ ∑ k ∈ Finset.Ico 1 m, ((k : ℝ)⁻¹) :=
    Finset.single_le_sum (f := fun k : ℕ ↦ ((k : ℝ)⁻¹))
      (fun k hk ↦ inv_nonneg.mpr (Nat.cast_nonneg k)) hmem
  norm_num at hle
  exact hle

private lemma exists_secretary_crossing {m : ℕ} (hm : 2 ≤ m) :
    ∃ j : ℕ, 1 ≤ j ∧ j < m ∧
      1 ≤ secretaryReciprocalTail m j ∧ secretaryReciprocalTail m (j + 1) ≤ 1 := by
  let s : Finset ℕ := (Finset.Icc 1 (m - 1)).filter
    (fun j ↦ 1 ≤ secretaryReciprocalTail m j)
  have h1 : 1 ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, by omega⟩, one_le_secretaryReciprocalTail_one hm⟩
  have hs : s.Nonempty := ⟨1, h1⟩
  let j := s.max' hs
  have hjmem : j ∈ s := Finset.max'_mem s hs
  have hjrange : 1 ≤ j ∧ j ≤ m - 1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hjmem).1)
  have hjtail : 1 ≤ secretaryReciprocalTail m j := (Finset.mem_filter.1 hjmem).2
  refine ⟨j, hjrange.1, by omega, hjtail, ?_⟩
  by_cases hjtop : j = m - 1
  · rw [hjtop, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    simp [secretaryReciprocalTail]
  · by_contra hnot
    have hnextTail : 1 ≤ secretaryReciprocalTail m (j + 1) := le_of_not_ge hnot
    have hnextMem : j + 1 ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hnextTail⟩
    have := Finset.le_max' s (j + 1) hnextMem
    exact (Nat.not_succ_le_self j) this

/-- Potential whose differences form the secretary LP dual certificate. -/
private def secretaryPotential (m k : ℕ) : ℝ :=
  (k : ℝ) * secretaryReciprocalTail m k

private lemma secretaryPotential_terminal (m : ℕ) : secretaryPotential m m = 0 := by
  simp [secretaryPotential, secretaryReciprocalTail]

private lemma secretaryPotential_diff {m k : ℕ} (hk1 : 1 ≤ k) (hkm : k < m) :
    secretaryPotential m k - secretaryPotential m (k + 1) =
      1 - secretaryReciprocalTail m (k + 1) := by
  rw [secretaryPotential, secretaryPotential,
    secretaryReciprocalTail_eq_inv_add hkm]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [mul_add, mul_inv_cancel₀ hk0]
  push_cast
  ring

private lemma sum_secretaryPotential_diff {m a : ℕ} (_ha : 1 ≤ a) (ham : a ≤ m) :
    (∑ k ∈ Finset.Ico a m,
      (secretaryPotential m k - secretaryPotential m (k + 1))) = secretaryPotential m a := by
  calc
    (∑ k ∈ Finset.Ico a m,
      (secretaryPotential m k - secretaryPotential m (k + 1))) =
        -∑ k ∈ Finset.Ico a m,
          (secretaryPotential m (k + 1) - secretaryPotential m k) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = -(secretaryPotential m m - secretaryPotential m a) := by
      rw [Finset.sum_Ico_sub (secretaryPotential m) ham]
    _ = secretaryPotential m a := by rw [secretaryPotential_terminal]; ring

private def secretaryDualWeight (m j k : ℕ) : ℝ :=
  if j ≤ k ∧ k < m then secretaryPotential m k - secretaryPotential m (k + 1) else 0

private lemma secretaryDualWeight_eq {m j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hkm : k < m) :
    secretaryDualWeight m j k = 1 - secretaryReciprocalTail m (k + 1) := by
  rw [secretaryDualWeight, if_pos ⟨hjk, hkm⟩]
  exact secretaryPotential_diff (hj.trans hjk) hkm

private lemma secretaryDualWeight_nonneg {m j k : ℕ} (hj : 1 ≤ j)
    (hjnext : secretaryReciprocalTail m (j + 1) ≤ 1) :
    0 ≤ secretaryDualWeight m j k := by
  by_cases hk : j ≤ k ∧ k < m
  · rw [secretaryDualWeight_eq hj hk.1 hk.2]
    exact sub_nonneg.mpr ((secretaryReciprocalTail_antitone (Nat.add_le_add_right hk.1 1)).trans
      hjnext)
  · simp [secretaryDualWeight, hk]

private lemma sum_secretaryDualWeight_Ico {m j a : ℕ} (hj : 1 ≤ j)
    (_hjm : j ≤ m) (hja : j ≤ a) (ham : a ≤ m) :
    (∑ k ∈ Finset.Ico a m, secretaryDualWeight m j k) = secretaryPotential m a := by
  calc
    (∑ k ∈ Finset.Ico a m, secretaryDualWeight m j k) =
        ∑ k ∈ Finset.Ico a m,
          (secretaryPotential m k - secretaryPotential m (k + 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [secretaryDualWeight, if_pos]
            exact ⟨hja.trans (Finset.mem_Ico.1 hk).1, (Finset.mem_Ico.1 hk).2⟩
    _ = secretaryPotential m a := sum_secretaryPotential_diff (hj.trans hja) ham

private lemma sum_secretaryDualWeight {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    (∑ k ∈ Finset.range m, secretaryDualWeight m j k) = secretaryPotential m j := by
  have hzero : ∑ k ∈ Finset.Ico 0 j, secretaryDualWeight m j k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [secretaryDualWeight, if_neg]
    exact fun h ↦ (not_le_of_gt (Finset.mem_Ico.1 hk).2) h.1
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (f := secretaryDualWeight m j)
    (show 0 ≤ j by omega) hjm, hzero, zero_add]
  exact sum_secretaryDualWeight_Ico hj hjm le_rfl hjm

private lemma sum_secretaryDualWeight_Ico_before {m j a : ℕ} (hj : 1 ≤ j)
    (haj : a ≤ j) (hjm : j ≤ m) :
    (∑ k ∈ Finset.Ico a m, secretaryDualWeight m j k) = secretaryPotential m j := by
  have hzero : ∑ k ∈ Finset.Ico a j, secretaryDualWeight m j k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [secretaryDualWeight, if_neg]
    exact fun h ↦ (not_le_of_gt (Finset.mem_Ico.1 hk).2) h.1
  rw [← Finset.sum_Ico_consecutive (f := secretaryDualWeight m j) haj hjm,
    hzero, zero_add]
  exact sum_secretaryDualWeight_Ico hj hjm le_rfl hjm

private lemma sum_fin_Ioi_eq_sum_Ico {m : ℕ} (f : ℕ → ℝ) (i : Fin m) :
    (∑ t ∈ Finset.Ioi i, f t.val) = ∑ k ∈ Finset.Ico (i.val + 1) m, f k := by
  refine Finset.sum_bij (fun t ht ↦ t.val) ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_Ico.2 ⟨by simpa using Finset.mem_Ioi.1 ht, t.isLt⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro k hk
    refine ⟨⟨k, (Finset.mem_Ico.1 hk).2⟩, ?_, rfl⟩
    exact Finset.mem_Ioi.2 ((Fin.mk_lt_mk).2 (by simpa using (Finset.mem_Ico.1 hk).1))
  · intro t ht
    rfl

private lemma secretaryDual_constraint {m j : ℕ} (hj : 1 ≤ j) (hjm : j < m)
    (hjtail : 1 ≤ secretaryReciprocalTail m j) (i : Fin m) :
    1 ≤ secretaryDualWeight m j i.val +
      (∑ t ∈ Finset.Ioi i, secretaryDualWeight m j t.val) /
        (((i.val + 1 : ℕ) : ℝ)) := by
  rw [sum_fin_Ioi_eq_sum_Ico]
  by_cases hik : j ≤ i.val
  · have hja : j ≤ i.val + 1 := by omega
    have ham : i.val + 1 ≤ m := by omega
    have hsum := sum_secretaryDualWeight_Ico hj hjm.le hja ham
    rw [hsum, secretaryDualWeight_eq hj hik i.isLt,
      secretaryPotential]
    have hden : (((i.val + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
    linarith
  · have hlt : i.val + 1 ≤ j := by omega
    have hsum := sum_secretaryDualWeight_Ico_before hj hlt hjm.le
    rw [hsum, secretaryDualWeight, if_neg (fun h ↦ hik h.1), secretaryPotential]
    have hdenpos : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by positivity
    simp only [zero_add]
    rw [le_div_iff₀ hdenpos]
    have hjcast : (((i.val + 1 : ℕ) : ℝ)) ≤ (j : ℝ) := by exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_left hjtail (Nat.cast_nonneg j)]

private lemma secretary_primal_le_dual {m : ℕ} (q y : Fin m → ℝ)
    (hq0 : ∀ t, 0 ≤ q t) (hy0 : ∀ t, 0 ≤ y t)
    (hcon : ∀ t, q t + ∑ i ∈ Finset.Iio t,
      q i / (((i.val + 1 : ℕ) : ℝ)) ≤ 1)
    (hdual : ∀ i, 1 ≤ y i +
      (∑ t ∈ Finset.Ioi i, y t) / (((i.val + 1 : ℕ) : ℝ))) :
    (∑ t, q t) ≤ ∑ t, y t := by
  have hIio (t : Fin m) : Finset.Iio t = Finset.univ.filter (fun i ↦ i < t) := by
    ext i
    simp
  have hIoi (i : Fin m) : Finset.Ioi i = Finset.univ.filter (fun t ↦ i < t) := by
    ext t
    simp
  have hFubini :
      (∑ t, y t * (q t + ∑ i ∈ Finset.Iio t,
        q i / (((i.val + 1 : ℕ) : ℝ)))) =
      ∑ i, q i * (y i +
        (∑ t ∈ Finset.Ioi i, y t) / (((i.val + 1 : ℕ) : ℝ))) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp_rw [hIio, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hIoi, Finset.sum_filter, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      split_ifs <;> ring
  calc
    (∑ t, q t) ≤ ∑ i, q i * (y i +
        (∑ t ∈ Finset.Ioi i, y t) / (((i.val + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdual i) (hq0 i)
    _ = ∑ t, y t * (q t + ∑ i ∈ Finset.Iio t,
        q i / (((i.val + 1 : ℕ) : ℝ))) := hFubini.symm
    _ ≤ ∑ t, y t := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcon t) (hy0 t)

private lemma secretaryCandidate_eq_potential {m j : ℕ} (hm : 1 ≤ m)
    (hj : 1 ≤ j) (_hjm : j < m) :
    (m : ℝ) * secretaryCandidate m (j + 1) = secretaryPotential m j := by
  rw [secretaryCandidate, if_neg (by omega)]
  have hshift := Finset.sum_Ico_add'
    (fun t : ℕ ↦ (((t - 1 : ℕ) : ℝ)⁻¹)) j m 1
  have hsum : (∑ t ∈ Finset.Icc (j + 1) m, (((t - 1 : ℕ) : ℝ)⁻¹)) =
      secretaryReciprocalTail m j := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa [secretaryReciprocalTail] using hshift.symm
  rw [hsum, secretaryPotential]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  field_simp

/-- Pure finite optimization bound for record-stop masses.  This is the bridge theorem: no
policy, probability, or measurability definitions occur in its hypotheses. -/
theorem classicalSecretaryLP_upper {m : ℕ} (hm : 1 ≤ m) (q : Fin m → ℝ)
    (hq0 : ∀ t, 0 ≤ q t)
    (hcon : ∀ t, q t + ∑ i ∈ Finset.Iio t,
      q i / (((i.val + 1 : ℕ) : ℝ)) ≤ 1) :
    (m : ℝ)⁻¹ * ∑ t, q t ≤ secretaryS m := by
  by_cases hm2 : 2 ≤ m
  · obtain ⟨j, hj, hjm, hjtail, hjnext⟩ := exists_secretary_crossing hm2
    let y : Fin m → ℝ := fun t ↦ secretaryDualWeight m j t.val
    have hy0 : ∀ t, 0 ≤ y t := fun t ↦ secretaryDualWeight_nonneg hj hjnext
    have hdual : ∀ i, 1 ≤ y i +
        (∑ t ∈ Finset.Ioi i, y t) / (((i.val + 1 : ℕ) : ℝ)) :=
      fun i ↦ secretaryDual_constraint hj hjm hjtail i
    have hp : (∑ t, q t) ≤ ∑ t, y t :=
      secretary_primal_le_dual q y hq0 hy0 hcon hdual
    have hySum : (∑ t, y t) = secretaryPotential m j := by
      calc
        (∑ t, y t) = ∑ k ∈ Finset.range m, secretaryDualWeight m j k := by
          simpa [y] using Fin.sum_univ_eq_sum_range (secretaryDualWeight m j) m
        _ = secretaryPotential m j := sum_secretaryDualWeight hj hjm.le
    rw [hySum] at hp
    have hscaled := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg m))
    have hpotential : (m : ℝ)⁻¹ * secretaryPotential m j =
        secretaryCandidate m (j + 1) := by
      rw [← secretaryCandidate_eq_potential hm hj hjm]
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hpotential] at hscaled
    have hmem : j + 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hcand := Finset.le_sup' (secretaryCandidate m) hmem
    rw [← secretaryS_eq_max hm] at hcand
    exact hscaled.trans hcand
  · have hmEq : m = 1 := by omega
    subst m
    have hc := hcon (0 : Fin 1)
    have hIio : Finset.Iio (0 : Fin 1) = ∅ := by
      ext i
      simp
    rw [hIio] at hc
    simpa using hc

#print axioms classicalSecretaryLP_upper

end


end MomentAmbiguity
