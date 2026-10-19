import MomentAmbiguity.Foundation.Discrete
import Mathlib.LinearAlgebra.Lagrange

/-!
The finite barycentric construction underlying `lem:finite-binary-vandermonde`.
-/

open scoped ENNReal NNReal Polynomial

namespace MomentAmbiguity

open MeasureTheory Set
open scoped BigOperators

/-- The barycentric weight at one of a finite family of nodes. -/
noncomputable def barycentricWeight {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : ℝ :=
  (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, (x i - x j))⁻¹

/-- Barycentric weights on an arbitrary finite set of natural-number indices.  This variant is
used for the finite-to-finite update identity in the binary separator. -/
noncomputable def barycentricWeightOn (x : ℕ → ℝ) (s : Finset ℕ) (i : ℕ) : ℝ :=
  (∏ j ∈ s.erase i, (x i - x j))⁻¹

/-- Normalize barycentric weights by the weight at a distinguished pivot. -/
noncomputable def normalizedBarycentricWeightOn
    (x : ℕ → ℝ) (s : Finset ℕ) (pivot i : ℕ) : ℝ :=
  barycentricWeightOn x s i / barycentricWeightOn x s pivot

theorem barycentricWeight_ne_zero {k : ℕ} {x : Fin k → ℝ}
    (hx : Function.Injective x) (i : Fin k) : barycentricWeight x i ≠ 0 := by
  rw [barycentricWeight]
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rcases Finset.mem_erase.mp hj with ⟨hji, -⟩
  exact sub_ne_zero.mpr fun h ↦ hji (hx h).symm

theorem barycentricWeightOn_ne_zero {x : ℕ → ℝ} {s : Finset ℕ}
    (hx : Set.InjOn x (s : Set ℕ)) {i : ℕ} (hi : i ∈ s) :
    barycentricWeightOn x s i ≠ 0 := by
  rw [barycentricWeightOn]
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rcases Finset.mem_erase.mp hj with ⟨hji, hjs⟩
  exact sub_ne_zero.mpr fun h ↦ hji (hx hi hjs h).symm

/-- Adding a fresh final node contributes exactly one new denominator factor. -/
theorem barycentricWeightOn_insert {x : ℕ → ℝ} {s : Finset ℕ} {a i : ℕ}
    (hi : i ∈ s) (ha : a ∉ s) :
    barycentricWeightOn x (insert a s) i =
      barycentricWeightOn x s i / (x i - x a) := by
  have hai : a ≠ i := fun h ↦ ha (h ▸ hi)
  simp [barycentricWeightOn, Finset.erase_insert_of_ne hai, ha, div_eq_mul_inv, mul_comm]

/-- Exact normalized update formula when one new node is appended. -/
theorem normalizedBarycentricWeightOn_insert {x : ℕ → ℝ} {s : Finset ℕ}
    {a pivot i : ℕ} (hpivot : pivot ∈ s) (hi : i ∈ s) (ha : a ∉ s)
    (hx : Set.InjOn x ((insert a s : Finset ℕ) : Set ℕ)) :
    normalizedBarycentricWeightOn x (insert a s) pivot i =
      normalizedBarycentricWeightOn x s pivot i *
        ((x pivot - x a) / (x i - x a)) := by
  have hs : Set.InjOn x (s : Set ℕ) := hx.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
  have hwi := barycentricWeightOn_ne_zero hs hi
  have hwp := barycentricWeightOn_ne_zero hs hpivot
  have hi_insert : i ∈ insert a s := Finset.mem_insert_of_mem hi
  have hpivot_insert : pivot ∈ insert a s := Finset.mem_insert_of_mem hpivot
  have ha_insert : a ∈ insert a s := Finset.mem_insert_self a s
  have hia_index : i ≠ a := fun h ↦ ha (h ▸ hi)
  have hpa_index : pivot ≠ a := fun h ↦ ha (h ▸ hpivot)
  have hia : x i - x a ≠ 0 :=
    sub_ne_zero.mpr (hx.ne hi_insert ha_insert hia_index)
  have hpa : x pivot - x a ≠ 0 :=
    sub_ne_zero.mpr (hx.ne hpivot_insert ha_insert hpa_index)
  rw [normalizedBarycentricWeightOn, normalizedBarycentricWeightOn,
    barycentricWeightOn_insert hi ha, barycentricWeightOn_insert hpivot ha]
  field_simp

/-- `eq:update-impossibility`: appending index `n` updates every old normalized barycentric
weight by `(x pivot-x n)/(x i-x n)`. -/
theorem barycentricWeight_normalized_succ (x : ℕ → ℝ) (n pivot i : ℕ)
    (hpivot : pivot < n) (hi : i < n)
    (hx : Set.InjOn x ((Finset.range (n + 1) : Finset ℕ) : Set ℕ)) :
    normalizedBarycentricWeightOn x (Finset.range (n + 1)) pivot i =
      normalizedBarycentricWeightOn x (Finset.range n) pivot i *
        ((x pivot - x n) / (x i - x n)) := by
  have hx' : Set.InjOn x
      (((insert n (Finset.range n) : Finset ℕ)) : Set ℕ) := by
    simpa only [← Finset.range_add_one] using hx
  rw [Finset.range_add_one]
  exact normalizedBarycentricWeightOn_insert (x := x) (s := Finset.range n) (a := n)
    (pivot := pivot) (i := i) (by simpa) (by simpa) (by simp) hx'

/-- Range-indexed version of the finite Vandermonde cancellation.  This is the bridge used by
the infinite binary construction, whose nodes are naturally indexed by `ℕ` rather than `Fin k`.
-/
theorem sum_barycentricWeightOn_range_mul_pow_eq_zero (k : ℕ) (hk : 2 ≤ k)
    (x : ℕ → ℝ) (hx : Set.InjOn x ((Finset.range k : Finset ℕ) : Set ℕ))
    (s : ℕ) (hs : s ≤ k - 2) :
    ∑ i ∈ Finset.range k, barycentricWeightOn x (Finset.range k) i * x i ^ s = 0 := by
  have hsk : s < k := by omega
  have hne : k - 1 ≠ s := by omega
  have hdeg : ((Polynomial.X : ℝ[X]) ^ s).degree <
      ((Finset.range k).card : WithBot ℕ) := by
    simpa [Polynomial.degree_X_pow] using hsk
  have hcoeff := Lagrange.coeff_eq_sum
    (s := Finset.range k) (v := x) (P := (Polynomial.X : ℝ[X]) ^ s) hx hdeg
  simpa [Polynomial.coeff_X_pow, hne, Polynomial.eval_X_pow, barycentricWeightOn,
    div_eq_mul_inv, mul_comm] using hcoeff.symm

/-- Normalized range-indexed cancellation.  Normalizing at any old pivot leaves all the
vanishing moment equations unchanged. -/
theorem sum_normalizedBarycentricWeightOn_range_mul_pow_eq_zero
    (k : ℕ) (hk : 2 ≤ k) (x : ℕ → ℝ) (pivot : ℕ) (hpivot : pivot < k)
    (hx : Set.InjOn x ((Finset.range k : Finset ℕ) : Set ℕ))
    (s : ℕ) (hs : s ≤ k - 2) :
    ∑ i ∈ Finset.range k,
        normalizedBarycentricWeightOn x (Finset.range k) pivot i * x i ^ s = 0 := by
  have hpivot_mem : pivot ∈ Finset.range k := Finset.mem_range.mpr hpivot
  have hpivot_ne : barycentricWeightOn x (Finset.range k) pivot ≠ 0 :=
    barycentricWeightOn_ne_zero hx hpivot_mem
  simp_rw [normalizedBarycentricWeightOn, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [sum_barycentricWeightOn_range_mul_pow_eq_zero k hk x hx s hs, zero_div]

/-- The same normalized cancellation with the finite range presented as `Fin k`. -/
theorem sum_normalizedBarycentricWeightOn_fin_mul_pow_eq_zero
    (k : ℕ) (hk : 2 ≤ k) (x : ℕ → ℝ) (pivot : ℕ) (hpivot : pivot < k)
    (hx : Set.InjOn x ((Finset.range k : Finset ℕ) : Set ℕ))
    (s : ℕ) (hs : s ≤ k - 2) :
    ∑ i : Fin k,
        normalizedBarycentricWeightOn x (Finset.range k) pivot i * x i ^ s = 0 := by
  simpa only [← Fin.sum_univ_eq_sum_range] using
    (sum_normalizedBarycentricWeightOn_range_mul_pow_eq_zero
      k hk x pivot hpivot hx s hs)

/-- For increasing nodes, the sign of a range barycentric weight is determined by the number
of later nodes. -/
theorem barycentricWeightOn_range_pos_of_even (x : ℕ → ℝ) (hx : StrictMono x)
    (k i : ℕ) (hi : i < k) (heven : Even (k - i - 1)) :
    0 < barycentricWeightOn x (Finset.range k) i := by
  let lower := Finset.range i
  let upper := Finset.Ioo i k
  have herase : (Finset.range k).erase i = lower ∪ upper := by
    ext j
    simp [lower, upper]
    omega
  have hdisjoint : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    simp [lower, upper]
    omega
  have hlower : 0 < ∏ j ∈ lower, (x i - x j) := by
    apply Finset.prod_pos
    intro j hj
    apply sub_pos.mpr
    apply hx
    simpa [lower] using hj
  have hupper : 0 < ∏ j ∈ upper, (x j - x i) := by
    apply Finset.prod_pos
    intro j hj
    apply sub_pos.mpr
    apply hx
    exact (Finset.mem_Ioo.mp hj).1
  have hupper_rewrite :
      (∏ j ∈ upper, (x i - x j)) =
        (-1 : ℝ) ^ (k - i - 1) * ∏ j ∈ upper, (x j - x i) := by
    calc
      (∏ j ∈ upper, (x i - x j)) = ∏ j ∈ upper, -(x j - x i) := by
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = (-1 : ℝ) ^ upper.card * ∏ j ∈ upper, (x j - x i) :=
        Finset.prod_neg (s := upper) (fun j ↦ x j - x i)
      _ = (-1 : ℝ) ^ (k - i - 1) * ∏ j ∈ upper, (x j - x i) := by
        simp [upper]
  rw [barycentricWeightOn, herase, Finset.prod_union hdisjoint, hupper_rewrite,
    heven.neg_one_pow]
  exact inv_pos.mpr (mul_pos hlower (by simpa using hupper))

/-- Oddly many later nodes give a negative barycentric weight. -/
theorem barycentricWeightOn_range_neg_of_odd (x : ℕ → ℝ) (hx : StrictMono x)
    (k i : ℕ) (hi : i < k) (hodd : Odd (k - i - 1)) :
    barycentricWeightOn x (Finset.range k) i < 0 := by
  let lower := Finset.range i
  let upper := Finset.Ioo i k
  have herase : (Finset.range k).erase i = lower ∪ upper := by
    ext j
    simp [lower, upper]
    omega
  have hdisjoint : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    simp [lower, upper]
    omega
  have hlower : 0 < ∏ j ∈ lower, (x i - x j) := by
    apply Finset.prod_pos
    intro j hj
    apply sub_pos.mpr
    apply hx
    simpa [lower] using hj
  have hupper : 0 < ∏ j ∈ upper, (x j - x i) := by
    apply Finset.prod_pos
    intro j hj
    apply sub_pos.mpr
    apply hx
    exact (Finset.mem_Ioo.mp hj).1
  have hupper_rewrite :
      (∏ j ∈ upper, (x i - x j)) =
        (-1 : ℝ) ^ (k - i - 1) * ∏ j ∈ upper, (x j - x i) := by
    calc
      (∏ j ∈ upper, (x i - x j)) = ∏ j ∈ upper, -(x j - x i) := by
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = (-1 : ℝ) ^ upper.card * ∏ j ∈ upper, (x j - x i) :=
        Finset.prod_neg (s := upper) (fun j ↦ x j - x i)
      _ = (-1 : ℝ) ^ (k - i - 1) * ∏ j ∈ upper, (x j - x i) := by
        simp [upper]
  rw [barycentricWeightOn, herase, Finset.prod_union hdisjoint, hupper_rewrite,
    hodd.neg_one_pow]
  exact inv_neg''.mpr (mul_neg_of_pos_of_neg hlower (by simpa using neg_neg_of_pos hupper))

/-- With pivot `2`, normalized barycentric signs agree with index parity. -/
theorem normalizedBarycentricWeightOn_pos_of_even (x : ℕ → ℝ) (hx : StrictMono x)
    (k j : ℕ) (hk : 2 < k) (hj : j < k) (heven : Even j) :
    0 < normalizedBarycentricWeightOn x (Finset.range k) 2 j := by
  rw [normalizedBarycentricWeightOn]
  obtain hpivotEven | hpivotOdd := Nat.even_or_odd (k - 2 - 1)
  · have hjEven : Even (k - j - 1) := by grind
    exact div_pos (barycentricWeightOn_range_pos_of_even x hx k j hj hjEven)
      (barycentricWeightOn_range_pos_of_even x hx k 2 hk hpivotEven)
  · have hjOdd : Odd (k - j - 1) := by grind
    exact div_pos_of_neg_of_neg (barycentricWeightOn_range_neg_of_odd x hx k j hj hjOdd)
      (barycentricWeightOn_range_neg_of_odd x hx k 2 hk hpivotOdd)

/-- With pivot `2`, odd normalized barycentric indices have negative weight. -/
theorem normalizedBarycentricWeightOn_neg_of_odd (x : ℕ → ℝ) (hx : StrictMono x)
    (k j : ℕ) (hk : 2 < k) (hj : j < k) (hodd : Odd j) :
    normalizedBarycentricWeightOn x (Finset.range k) 2 j < 0 := by
  rw [normalizedBarycentricWeightOn]
  obtain hpivotEven | hpivotOdd := Nat.even_or_odd (k - 2 - 1)
  · have hjOdd : Odd (k - j - 1) := by grind
    exact div_neg_of_neg_of_pos (barycentricWeightOn_range_neg_of_odd x hx k j hj hjOdd)
      (barycentricWeightOn_range_pos_of_even x hx k 2 hk hpivotEven)
  · have hjEven : Even (k - j - 1) := by grind
    exact div_neg_of_pos_of_neg (barycentricWeightOn_range_pos_of_even x hx k j hj hjEven)
      (barycentricWeightOn_range_neg_of_odd x hx k 2 hk hpivotOdd)

/-- `lem:finite-binary-vandermonde`: barycentric weights annihilate every monomial through
degree `k-2`. -/
theorem sum_barycentricWeight_mul_pow_eq_zero {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : Function.Injective x) (s : ℕ) (hs : s ≤ k - 2) :
    ∑ i : Fin k, barycentricWeight x i * x i ^ s = 0 := by
  have hsk : s < k := by omega
  have hne : k - 1 ≠ s := by omega
  have hdeg : ((Polynomial.X : ℝ[X]) ^ s).degree <
      ((Finset.univ : Finset (Fin k)).card : WithBot ℕ) := by
    simpa [Polynomial.degree_X_pow] using hsk
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin k))) (v := x)
    (P := (Polynomial.X : ℝ[X]) ^ s) hx.injOn hdeg
  simpa [Polynomial.coeff_X_pow, hne, Polynomial.eval_X_pow, barycentricWeight,
    div_eq_mul_inv, mul_comm] using hcoeff.symm

/-- Positive part of a barycentric weight. -/
noncomputable def positiveBarycentricWeight {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : ℝ≥0 :=
  Real.toNNReal (barycentricWeight x i)

/-- Negative part of a barycentric weight. -/
noncomputable def negativeBarycentricWeight {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : ℝ≥0 :=
  Real.toNNReal (-barycentricWeight x i)

noncomputable def positiveBarycentricMass {k : ℕ} (x : Fin k → ℝ) : ℝ≥0 :=
  ∑ i, positiveBarycentricWeight x i

noncomputable def negativeBarycentricMass {k : ℕ} (x : Fin k → ℝ) : ℝ≥0 :=
  ∑ i, negativeBarycentricWeight x i

theorem coe_positiveBarycentricWeight_sub_negative {k : ℕ} (x : Fin k → ℝ)
    (i : Fin k) :
    (positiveBarycentricWeight x i : ℝ) - (negativeBarycentricWeight x i : ℝ) =
      barycentricWeight x i := by
  rcases le_total 0 (barycentricWeight x i) with h | h
  · simp [positiveBarycentricWeight, negativeBarycentricWeight,
      Real.coe_toNNReal _ h, Real.toNNReal_of_nonpos (neg_nonpos.mpr h)]
  · have hn : 0 ≤ -barycentricWeight x i := neg_nonneg.mpr h
    simp [positiveBarycentricWeight, negativeBarycentricWeight,
      Real.toNNReal_of_nonpos h, Real.coe_toNNReal _ hn]

theorem positiveBarycentricMass_eq_negative {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : Function.Injective x) :
    positiveBarycentricMass x = negativeBarycentricMass x := by
  have hzero := sum_barycentricWeight_mul_pow_eq_zero hk x hx 0 (by omega)
  simp only [pow_zero, mul_one] at hzero
  apply NNReal.eq
  simp only [positiveBarycentricMass, negativeBarycentricMass, NNReal.coe_sum]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simpa only [coe_positiveBarycentricWeight_sub_negative] using hzero

theorem positiveBarycentricMass_pos {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : Function.Injective x) : 0 < positiveBarycentricMass x := by
  have hzero := sum_barycentricWeight_mul_pow_eq_zero hk x hx 0 (by omega)
  simp only [pow_zero, mul_one] at hzero
  have hnonzero : ∀ i : Fin k, barycentricWeight x i ≠ 0 := barycentricWeight_ne_zero hx
  have hex : ∃ i : Fin k, 0 < barycentricWeight x i := by
    by_contra h
    push Not at h
    let i0 : Fin k := ⟨0, by omega⟩
    have hi0 : barycentricWeight x i0 < 0 := lt_of_le_of_ne (h i0) (hnonzero i0)
    have hlt : (∑ i : Fin k, barycentricWeight x i) < ∑ _i : Fin k, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact h i
      · exact ⟨i0, Finset.mem_univ i0, hi0⟩
    simp [hzero] at hlt
  obtain ⟨i, hi⟩ := hex
  apply lt_of_lt_of_le (Real.toNNReal_pos.mpr hi)
  exact Finset.single_le_sum
    (f := fun j ↦ positiveBarycentricWeight x j)
    (fun j _ ↦ show 0 ≤ positiveBarycentricWeight x j from bot_le)
    (Finset.mem_univ i)

theorem negativeBarycentricMass_pos {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : Function.Injective x) : 0 < negativeBarycentricMass x := by
  rw [← positiveBarycentricMass_eq_negative hk x hx]
  exact positiveBarycentricMass_pos hk x hx

/-- The normalized positive part of the finite barycentric identity. -/
noncomputable def positiveBarycentricPMF {k : ℕ} (x : Fin k → ℝ)
    (hpos : positiveBarycentricMass x ≠ 0) : PMF (Fin k) :=
  pmfOfFintype (fun i ↦ positiveBarycentricWeight x i / positiveBarycentricMass x) (by
    rw [← Finset.sum_div]
    exact div_self hpos)

/-- The normalized negative part of the finite barycentric identity. -/
noncomputable def negativeBarycentricPMF {k : ℕ} (x : Fin k → ℝ)
    (hneg : negativeBarycentricMass x ≠ 0) : PMF (Fin k) :=
  pmfOfFintype (fun i ↦ negativeBarycentricWeight x i / negativeBarycentricMass x) (by
    rw [← Finset.sum_div]
    exact div_self hneg)

@[simp]
theorem positiveBarycentricPMF_apply {k : ℕ} (x : Fin k → ℝ)
    (hpos : positiveBarycentricMass x ≠ 0) (i : Fin k) :
    positiveBarycentricPMF x hpos i =
      (positiveBarycentricWeight x i / positiveBarycentricMass x : ℝ≥0) :=
  rfl

@[simp]
theorem negativeBarycentricPMF_apply {k : ℕ} (x : Fin k → ℝ)
    (hneg : negativeBarycentricMass x ≠ 0) (i : Fin k) :
    negativeBarycentricPMF x hneg i =
      (negativeBarycentricWeight x i / negativeBarycentricMass x : ℝ≥0) :=
  rfl

/-- The normalized positive and negative parts have the same moments through degree `k-2`. -/
theorem sum_positiveBarycentricPMF_mul_pow_eq_negative {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : Function.Injective x) (s : ℕ) (hs : s ≤ k - 2) :
    ∑ i : Fin k,
        ((positiveBarycentricWeight x i : ℝ) / (positiveBarycentricMass x : ℝ)) * x i ^ s =
      ∑ i : Fin k,
        ((negativeBarycentricWeight x i : ℝ) / (negativeBarycentricMass x : ℝ)) * x i ^ s := by
  have hraw :
      (∑ i : Fin k, (positiveBarycentricWeight x i : ℝ) * x i ^ s) =
        ∑ i : Fin k, (negativeBarycentricWeight x i : ℝ) * x i ^ s := by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    calc
      ∑ i : Fin k,
          ((positiveBarycentricWeight x i : ℝ) * x i ^ s -
            (negativeBarycentricWeight x i : ℝ) * x i ^ s) =
          ∑ i : Fin k, barycentricWeight x i * x i ^ s := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← sub_mul, coe_positiveBarycentricWeight_sub_negative]
      _ = 0 := sum_barycentricWeight_mul_pow_eq_zero hk x hx s hs
  have hmass : (positiveBarycentricMass x : ℝ) = (negativeBarycentricMass x : ℝ) := by
    exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ))
      (positiveBarycentricMass_eq_negative hk x hx)
  simp_rw [div_mul_eq_mul_div]
  calc
    (∑ i : Fin k,
        (positiveBarycentricWeight x i : ℝ) * x i ^ s /
          (positiveBarycentricMass x : ℝ)) =
        (∑ i : Fin k, (positiveBarycentricWeight x i : ℝ) * x i ^ s) /
          (positiveBarycentricMass x : ℝ) := by rw [Finset.sum_div]
    _ = (∑ i : Fin k, (negativeBarycentricWeight x i : ℝ) * x i ^ s) /
          (negativeBarycentricMass x : ℝ) := by rw [hraw, hmass]
    _ = ∑ i : Fin k,
        (negativeBarycentricWeight x i : ℝ) * x i ^ s /
          (negativeBarycentricMass x : ℝ) := by rw [Finset.sum_div]

/-- Measure-theoretic form of the finite moment identities. -/
theorem integral_positiveBarycentricPMF_eq_negative {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : Function.Injective x) (s : ℕ) (hs : s ≤ k - 2) :
    let hpos : positiveBarycentricMass x ≠ 0 :=
      ne_of_gt (positiveBarycentricMass_pos hk x hx)
    let hneg : negativeBarycentricMass x ≠ 0 :=
      ne_of_gt (negativeBarycentricMass_pos hk x hx)
    ∫ y, y ^ s ∂((atomicLaw (positiveBarycentricPMF x hpos) x :
        ProbabilityMeasure ℝ) : Measure ℝ) =
      ∫ y, y ^ s ∂((atomicLaw (negativeBarycentricPMF x hneg) x :
        ProbabilityMeasure ℝ) : Measure ℝ) := by
  dsimp only
  let hpos : positiveBarycentricMass x ≠ 0 :=
    ne_of_gt (positiveBarycentricMass_pos hk x hx)
  let hneg : negativeBarycentricMass x ≠ 0 :=
    ne_of_gt (negativeBarycentricMass_pos hk x hx)
  have hxmeas : Measurable x := measurable_of_finite x
  have hpow : StronglyMeasurable (fun y : ℝ ↦ y ^ s) := by fun_prop
  rw [integral_atomicLaw_eq_sum (positiveBarycentricPMF x hpos) x
      (fun y : ℝ ↦ y ^ s) hxmeas hpow,
    integral_atomicLaw_eq_sum (negativeBarycentricPMF x hneg) x
      (fun y : ℝ ↦ y ^ s) hxmeas hpow]
  simpa [hpos, hneg, NNReal.coe_div, smul_eq_mul] using
    (sum_positiveBarycentricPMF_mul_pow_eq_negative hk x hx s hs)

/-- Indices carrying the positive part of the signed barycentric vector. -/
def positiveBarycentricIndexSet {k : ℕ} (x : Fin k → ℝ) : Set (Fin k) :=
  {i | 0 < barycentricWeight x i}

/-- Indices carrying the negative part of the signed barycentric vector. -/
def negativeBarycentricIndexSet {k : ℕ} (x : Fin k → ℝ) : Set (Fin k) :=
  {i | barycentricWeight x i < 0}

/-- Actual nodes carrying the positive part of the signed barycentric vector. -/
def positiveBarycentricNodes {k : ℕ} (x : Fin k → ℝ) : Set ℝ :=
  x '' positiveBarycentricIndexSet x

/-- Actual nodes carrying the negative part of the signed barycentric vector. -/
def negativeBarycentricNodes {k : ℕ} (x : Fin k → ℝ) : Set ℝ :=
  x '' negativeBarycentricIndexSet x

theorem positiveBarycentricNodes_finite {k : ℕ} (x : Fin k → ℝ) :
    (positiveBarycentricNodes x).Finite := by
  exact (Set.finite_range x).subset (Set.image_subset_range x _)

theorem negativeBarycentricNodes_finite {k : ℕ} (x : Fin k → ℝ) :
    (negativeBarycentricNodes x).Finite := by
  exact (Set.finite_range x).subset (Set.image_subset_range x _)

/-- The positive and negative sign classes are disjoint after mapping to distinct nodes. -/
theorem positive_negative_barycentricNodes_disjoint {k : ℕ} (x : Fin k → ℝ)
    (hx : Function.Injective x) :
    Disjoint (positiveBarycentricNodes x) (negativeBarycentricNodes x) := by
  rw [Set.disjoint_left]
  rintro y ⟨i, hi, rfl⟩ ⟨j, hj, hij⟩
  have hji : j = i := hx hij
  subst j
  change 0 < barycentricWeight x i at hi
  change barycentricWeight x i < 0 at hj
  exact (not_lt_of_ge (le_of_lt hi)) hj

/-- The normalized positive PMF has no mass away from positive barycentric indices. -/
theorem positiveBarycentricPMF_support_subset {k : ℕ} (x : Fin k → ℝ)
    (hpos : positiveBarycentricMass x ≠ 0) :
    (positiveBarycentricPMF x hpos).support ⊆ positiveBarycentricIndexSet x := by
  intro i hi
  have hpi : positiveBarycentricPMF x hpos i ≠ 0 :=
    (PMF.mem_support_iff (positiveBarycentricPMF x hpos) i).mp hi
  change 0 < barycentricWeight x i
  by_contra hnpos
  have hw : positiveBarycentricWeight x i = 0 := by
    exact Real.toNNReal_of_nonpos (le_of_not_gt hnpos)
  apply hpi
  rw [positiveBarycentricPMF_apply, hw]
  simp

/-- The normalized negative PMF has no mass away from negative barycentric indices. -/
theorem negativeBarycentricPMF_support_subset {k : ℕ} (x : Fin k → ℝ)
    (hneg : negativeBarycentricMass x ≠ 0) :
    (negativeBarycentricPMF x hneg).support ⊆ negativeBarycentricIndexSet x := by
  intro i hi
  have hpi : negativeBarycentricPMF x hneg i ≠ 0 :=
    (PMF.mem_support_iff (negativeBarycentricPMF x hneg) i).mp hi
  change barycentricWeight x i < 0
  by_contra hnneg
  have hw : negativeBarycentricWeight x i = 0 := by
    exact Real.toNNReal_of_nonpos (neg_nonpos.mpr (le_of_not_gt hnneg))
  apply hpi
  rw [negativeBarycentricPMF_apply, hw]
  simp

theorem positiveBarycentricLaw_nodes_eq_one {k : ℕ} (x : Fin k → ℝ)
    (hpos : positiveBarycentricMass x ≠ 0) :
    ((atomicLaw (positiveBarycentricPMF x hpos) x : ProbabilityMeasure ℝ) : Measure ℝ)
        (positiveBarycentricNodes x) = 1 := by
  apply (PMF.toMeasure_apply_eq_one_iff ((positiveBarycentricPMF x hpos).map x)
    (positiveBarycentricNodes_finite x).measurableSet).2
  rw [PMF.support_map]
  exact Set.image_mono (positiveBarycentricPMF_support_subset x hpos)

theorem negativeBarycentricLaw_nodes_eq_one {k : ℕ} (x : Fin k → ℝ)
    (hneg : negativeBarycentricMass x ≠ 0) :
    ((atomicLaw (negativeBarycentricPMF x hneg) x : ProbabilityMeasure ℝ) : Measure ℝ)
        (negativeBarycentricNodes x) = 1 := by
  apply (PMF.toMeasure_apply_eq_one_iff ((negativeBarycentricPMF x hneg).map x)
    (negativeBarycentricNodes_finite x).measurableSet).2
  rw [PMF.support_map]
  exact Set.image_mono (negativeBarycentricPMF_support_subset x hneg)

theorem negativeBarycentricLaw_positiveNodes_eq_zero {k : ℕ} (x : Fin k → ℝ)
    (hx : Function.Injective x) (hneg : negativeBarycentricMass x ≠ 0) :
    ((atomicLaw (negativeBarycentricPMF x hneg) x : ProbabilityMeasure ℝ) : Measure ℝ)
        (positiveBarycentricNodes x) = 0 := by
  apply (PMF.toMeasure_apply_eq_zero_iff ((negativeBarycentricPMF x hneg).map x)
    (positiveBarycentricNodes_finite x).measurableSet).2
  rw [PMF.support_map]
  exact (positive_negative_barycentricNodes_disjoint x hx).symm.mono
    (Set.image_mono (negativeBarycentricPMF_support_subset x hneg)) Subset.rfl

/-- `lem:finite-binary-vandermonde`, `sections/impossibility.tex`: on any `k ≥ 2`
strictly ordered real nodes there are two distinct probability laws, carried by disjoint subsets
of those nodes, whose moments agree through degree `k-2`.

The phrase "supported on" is translated as full measure of the displayed finite carrier.  This
avoids importing topological-support machinery and is exactly the measure-theoretic property
used in the manuscript proof. -/
theorem finite_binary_vandermonde {k : ℕ} (hk : 2 ≤ k) (x : Fin k → ℝ)
    (hx : StrictMono x) :
    ∃ muPlus muMinus : ProbabilityMeasure ℝ,
      muPlus ≠ muMinus ∧
      ∃ supportPlus supportMinus : Set ℝ,
        supportPlus.Finite ∧
        supportMinus.Finite ∧
        supportPlus ⊆ Set.range x ∧
        supportMinus ⊆ Set.range x ∧
        Disjoint supportPlus supportMinus ∧
        ((muPlus : Measure ℝ) supportPlus = 1) ∧
        ((muMinus : Measure ℝ) supportMinus = 1) ∧
        ∀ s : ℕ, s ≤ k - 2 →
          ∫ y, y ^ s ∂(muPlus : Measure ℝ) =
            ∫ y, y ^ s ∂(muMinus : Measure ℝ) := by
  have hinj : Function.Injective x := hx.injective
  let hpos : positiveBarycentricMass x ≠ 0 :=
    ne_of_gt (positiveBarycentricMass_pos hk x hinj)
  let hneg : negativeBarycentricMass x ≠ 0 :=
    ne_of_gt (negativeBarycentricMass_pos hk x hinj)
  let muPlus : ProbabilityMeasure ℝ := atomicLaw (positiveBarycentricPMF x hpos) x
  let muMinus : ProbabilityMeasure ℝ := atomicLaw (negativeBarycentricPMF x hneg) x
  have hplus : (muPlus : Measure ℝ) (positiveBarycentricNodes x) = 1 := by
    exact positiveBarycentricLaw_nodes_eq_one x hpos
  have hminus : (muMinus : Measure ℝ) (negativeBarycentricNodes x) = 1 := by
    exact negativeBarycentricLaw_nodes_eq_one x hneg
  have hcross : (muMinus : Measure ℝ) (positiveBarycentricNodes x) = 0 := by
    exact negativeBarycentricLaw_positiveNodes_eq_zero x hinj hneg
  have hne : muPlus ≠ muMinus := by
    intro heq
    have happly := congrArg
      (fun mu : ProbabilityMeasure ℝ ↦ (mu : Measure ℝ) (positiveBarycentricNodes x)) heq
    rw [hplus, hcross] at happly
    exact one_ne_zero happly
  refine ⟨muPlus, muMinus, hne, positiveBarycentricNodes x,
    negativeBarycentricNodes x, positiveBarycentricNodes_finite x,
    negativeBarycentricNodes_finite x, Set.image_subset_range x _,
    Set.image_subset_range x _, positive_negative_barycentricNodes_disjoint x hinj,
    hplus, hminus, ?_⟩
  intro s hs
  exact integral_positiveBarycentricPMF_eq_negative hk x hinj s hs

/-- A real power is integrable under any probability law carried by a finite set.  This
records explicitly the finiteness that is automatic in the manuscript's finite-support
Vandermonde construction. -/
theorem integrable_pow_of_finite_carrier (mu : ProbabilityMeasure ℝ) (support : Set ℝ)
    (hsupport : support.Finite) (hmu : (mu : Measure ℝ) support = 1) (s : ℕ) :
    Integrable (fun y : ℝ ↦ y ^ s) (mu : Measure ℝ) := by
  have hrestricted : IntegrableOn (fun y : ℝ ↦ y ^ s) support (mu : Measure ℝ) :=
    IntegrableOn.of_finite hsupport
  have hindicator : Integrable (support.indicator (fun y : ℝ ↦ y ^ s))
      (mu : Measure ℝ) :=
    hrestricted.integrable_indicator hsupport.measurableSet
  have haesupport : ∀ᵐ y ∂(mu : Measure ℝ), y ∈ support := by
    apply (ae_mem_iff_measure_eq hsupport.measurableSet.nullMeasurableSet).2
    simpa using hmu
  exact hindicator.congr (haesupport.mono fun y hy ↦ by simp [hy])

/-- `lem:finite-binary-vandermonde`, `sections/impossibility.tex`: strengthened traceability
form exposing integrability of every polynomial moment of both finite-support laws, in
addition to the exact original support, distinctness, and matching conclusions. -/
theorem finite_binary_vandermonde_with_integrability {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℝ) (hx : StrictMono x) :
    ∃ muPlus muMinus : ProbabilityMeasure ℝ,
      muPlus ≠ muMinus ∧
      ∃ supportPlus supportMinus : Set ℝ,
        supportPlus.Finite ∧
        supportMinus.Finite ∧
        supportPlus ⊆ Set.range x ∧
        supportMinus ⊆ Set.range x ∧
        Disjoint supportPlus supportMinus ∧
        ((muPlus : Measure ℝ) supportPlus = 1) ∧
        ((muMinus : Measure ℝ) supportMinus = 1) ∧
        (∀ s : ℕ,
          Integrable (fun y : ℝ ↦ y ^ s) (muPlus : Measure ℝ) ∧
          Integrable (fun y : ℝ ↦ y ^ s) (muMinus : Measure ℝ)) ∧
        ∀ s : ℕ, s ≤ k - 2 →
          ∫ y, y ^ s ∂(muPlus : Measure ℝ) =
            ∫ y, y ^ s ∂(muMinus : Measure ℝ) := by
  obtain ⟨muPlus, muMinus, hne, supportPlus, supportMinus,
      hplusFinite, hminusFinite, hplusRange, hminusRange, hdisjoint,
      hplusMass, hminusMass, hmoments⟩ := finite_binary_vandermonde hk x hx
  refine ⟨muPlus, muMinus, hne, supportPlus, supportMinus,
    hplusFinite, hminusFinite, hplusRange, hminusRange, hdisjoint,
    hplusMass, hminusMass, ?_, hmoments⟩
  intro s
  exact ⟨integrable_pow_of_finite_carrier muPlus supportPlus hplusFinite hplusMass s,
    integrable_pow_of_finite_carrier muMinus supportMinus hminusFinite hminusMass s⟩

end MomentAmbiguity
