import MomentAmbiguity.Foundation.Basic
import MomentAmbiguity.Foundation.Discrete
import MomentAmbiguity.Construction.Vandermonde

/-!
# The binary moment separator

This file formalizes the binary construction in `sections/impossibility.tex` and every
labelled dependency in `sections/proofs.tex`.  The construction is kept canonical: the finite
weights are normalized barycentric weights, and the limiting weights are their actual limits.
-/

open scoped BigOperators ENNReal NNReal Topology

namespace MomentAmbiguity

open Filter MeasureTheory Set

noncomputable section

namespace BinarySeparator

/-- The support from `thm:binary-separator` / `prop:key-prop-1`.

The shifted recursive presentation is definitionally convenient in Lean and is exactly
`x_0=1`, `x_1=B`, and `x_j=(nB)^(B^(j-2))` for `j≥2`. -/
def nodeNN (n B : ℕ) : ℕ → ℝ≥0
  | 0 => 1
  | 1 => B
  | j + 2 => (n * B : ℝ≥0) ^ (B ^ j)

/-- The real-valued copy of the support, used in the barycentric algebra. -/
def node (n B j : ℕ) : ℝ := nodeNN n B j

@[simp] theorem nodeNN_zero (n B : ℕ) : nodeNN n B 0 = 1 := rfl
@[simp] theorem nodeNN_one (n B : ℕ) : nodeNN n B 1 = B := rfl
@[simp] theorem nodeNN_add_two (n B j : ℕ) :
    nodeNN n B (j + 2) = (n * B : ℝ≥0) ^ (B ^ j) := rfl

@[simp] theorem node_zero (n B : ℕ) : node n B 0 = 1 := rfl
@[simp] theorem node_one (n B : ℕ) : node n B 1 = B := by
  simp [node]
@[simp] theorem node_add_two (n B j : ℕ) :
    node n B (j + 2) = (n * B : ℝ) ^ (B ^ j) := by
  simp [node, nodeNN]

@[simp] theorem node_two (n B : ℕ) : node n B 2 = n * B := by
  simpa using node_add_two n B 0

@[simp] theorem node_three (n B : ℕ) : node n B 3 = (n * B : ℝ) ^ B := by
  simpa [Nat.add_assoc] using node_add_two n B 1

theorem one_lt_node_two {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    1 < node n B 2 := by
  rw [node_two]
  have hmul : 3 * 3 ≤ n * B := Nat.mul_le_mul hn hB
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3 * 3) hmul)

/-- The manuscript support is strictly increasing. -/
theorem node_strictMono {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    StrictMono (node n B) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rcases j with (_ | _ | j)
  · have h : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
    simpa [node] using h
  · have h : (B : ℝ) < n * B := by
      have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have hB' : (0 : ℝ) < B := by positivity
      nlinarith [mul_pos (sub_pos.mpr hn') hB']
    simpa [node] using h
  · have hpow : B ^ j < B ^ (j + 1) :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < B)).2 (by omega)
    have h := pow_lt_pow_right₀ (one_lt_node_two hn hB) hpow
    simpa only [show j + 1 + 1 = j + 2 by omega,
      show j + 1 + 1 + 1 = (j + 1) + 2 by omega, node_add_two, node_two,
      pow_zero, pow_one] using h

theorem node_injective {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Function.Injective (node n B) := (node_strictMono hn hB).injective

theorem node_pos {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    0 < node n B j := by
  exact lt_of_lt_of_le (show 0 < node n B 0 by simp)
    ((node_strictMono hn hB).monotone (Nat.zero_le j))

/-- The recurrence used throughout the decay estimates. -/
theorem node_succ_eq_pow {n B : ℕ} (j : ℕ) (hj : 2 ≤ j) :
    node n B (j + 1) = node n B j ^ B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only [show 2 + k = k + 2 by omega,
    show 2 + k + 1 = (k + 1) + 2 by omega, node_add_two]
  rw [pow_succ, pow_mul]

theorem two_le_node {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) {j : ℕ} (hj : 2 ≤ j) :
    (2 : ℝ) ≤ node n B j := by
  calc
    (2 : ℝ) ≤ node n B 2 := by
      rw [node_two]
      norm_num at hn hB ⊢
      exact_mod_cast (show 2 ≤ n * B by nlinarith)
    _ ≤ node n B j := (node_strictMono hn hB).monotone hj

theorem node_succ_ge_two_mul {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    {j : ℕ} (hj : 2 ≤ j) :
    2 * node n B j ≤ node n B (j + 1) := by
  rw [node_succ_eq_pow j hj]
  let x := node n B j
  have hx : 2 ≤ x := two_le_node hn hB hj
  calc
    2 * x ≤ x ^ 2 := by nlinarith
    _ ≤ x ^ B := pow_le_pow_right₀ (by linarith : 1 ≤ x) (by omega)

theorem node_ge_geometric {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    node n B 3 * 2 ^ j ≤ node n B (j + 3) := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        node n B 3 * 2 ^ (j + 1) = 2 * (node n B 3 * 2 ^ j) := by ring
        _ ≤ 2 * node n B (j + 3) := by gcongr
        _ ≤ node n B (j + 3 + 1) := node_succ_ge_two_mul hn hB (by omega)
        _ = node n B (j + 1 + 3) := by congr 1 <;> omega

theorem node_ge_geometric_from {n B q : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hq : 2 ≤ q) (r : ℕ) : node n B q * 2 ^ r ≤ node n B (q + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        node n B q * 2 ^ (r + 1) = 2 * (node n B q * 2 ^ r) := by ring
        _ ≤ 2 * node n B (q + r) := by gcongr
        _ ≤ node n B (q + r + 1) := node_succ_ge_two_mul hn hB (by omega)
        _ = node n B (q + (r + 1)) := by congr 1 <;> omega

/-- The elementary support summability used in all dominated-convergence arguments. -/
theorem summable_inv_node_sq {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (fun j : ℕ ↦ 1 / node n B j ^ 2) := by
  rw [← summable_nat_add_iff 3]
  have hgeom : Summable (fun j : ℕ ↦
      (1 / node n B 3 ^ 2) * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine hgeom.of_nonneg_of_le
    (fun j ↦ one_div_nonneg.mpr (sq_nonneg (node n B (j + 3)))) (fun j ↦ ?_)
  have hpos : 0 < node n B 3 := node_pos hn hB 3
  have hg := node_ge_geometric hn hB j
  have hsq : (node n B 3 * 2 ^ j) ^ 2 ≤ node n B (j + 3) ^ 2 := by
    gcongr
  calc
    1 / node n B (j + 3) ^ 2 ≤ 1 / (node n B 3 * 2 ^ j) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hsq
    _ = (1 / node n B 3 ^ 2) * (1 / 4 : ℝ) ^ j := by
      rw [mul_pow]
      simp only [one_div]
      rw [mul_inv_rev]
      rw [mul_comm (((2 : ℝ) ^ j) ^ 2)⁻¹ (node n B 3 ^ 2)⁻¹]
      congr 1
      rw [inv_pow, show (4 : ℝ) = 2 ^ 2 by norm_num]
      congr 1
      rw [← pow_mul, ← pow_mul, mul_comm]

/-- The reciprocal support series also converges; this is used only to establish the
pointwise infinite products in `lem:limit-weights-exist`. -/
theorem summable_inv_node {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (fun j : ℕ ↦ 1 / node n B j) := by
  rw [← summable_nat_add_iff 3]
  have hgeom : Summable (fun j : ℕ ↦
      (1 / node n B 3) * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine hgeom.of_nonneg_of_le
    (fun j ↦ one_div_nonneg.mpr (node_pos hn hB (j + 3)).le) (fun j ↦ ?_)
  have hg := node_ge_geometric hn hB j
  calc
    1 / node n B (j + 3) ≤ 1 / (node n B 3 * 2 ^ j) :=
      one_div_le_one_div_of_le
        (mul_pos (node_pos hn hB 3) (pow_pos (by norm_num) _)) hg
    _ = (1 / node n B 3) * (1 / 2 : ℝ) ^ j := by
      simp only [one_div, mul_inv_rev, inv_pow]
      ring

/-- Finite normalized barycentric weights from `prop:key-prop-1_extended`.

For indices outside the finite system the weight is set to zero. -/
def finiteWeight (n B K j : ℕ) : ℝ :=
  if hj : j < K + 3 then
    normalizedBarycentricWeightOn (node n B) (Finset.range (K + 3)) 2 j
  else 0

@[simp] theorem finiteWeight_eq_zero_of_ge {n B K j : ℕ} (hj : K + 3 ≤ j) :
    finiteWeight n B K j = 0 := by
  simp [finiteWeight, Nat.not_lt.mpr hj]

theorem finiteWeight_eq_product {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j < K + 3) :
    finiteWeight n B K j =
      (∏ i ∈ (Finset.range (K + 3)).erase 2, (node n B 2 - node n B i)) /
      (∏ i ∈ (Finset.range (K + 3)).erase j, (node n B j - node n B i)) := by
  have hx : Set.InjOn (node n B) (Finset.range (K + 3) : Set ℕ) :=
    (node_injective hn hB).injOn
  have hpivot : ∏ i ∈ (Finset.range (K + 3)).erase 2,
      (node n B 2 - node n B i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr ((node_injective hn hB).ne (Finset.mem_erase.mp hi).1.symm)
  have hjprod : ∏ i ∈ (Finset.range (K + 3)).erase j,
      (node n B j - node n B i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr ((node_injective hn hB).ne (Finset.mem_erase.mp hi).1.symm)
  simp only [finiteWeight, hj, dif_pos, normalizedBarycentricWeightOn,
    barycentricWeightOn]
  field_simp

/-- `prop:key-prop-1_extended`: the finite normalization is `w_2=1`. -/
theorem finiteWeight_two {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (K : ℕ) :
    finiteWeight n B K 2 = 1 := by
  have hx : Set.InjOn (node n B) (Finset.range (K + 3) : Set ℕ) :=
    (node_injective hn hB).injOn
  have hw := barycentricWeightOn_ne_zero hx (show 2 ∈ Finset.range (K + 3) by simp)
  simp [finiteWeight, normalizedBarycentricWeightOn, hw]

/-- `prop:key-prop-1_extended`: finite weights annihilate the powers through degree `K+1`. -/
theorem finiteWeight_moment_zero {n B K : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    {s : ℕ} (hs : s ≤ K + 1) :
    ∑ j : Fin (K + 3), finiteWeight n B K j * node n B j ^ s = 0 := by
  simpa only [finiteWeight, Fin.is_lt, dif_pos] using
    sum_normalizedBarycentricWeightOn_fin_mul_pow_eq_zero
      (K + 3) (by omega) (node n B) 2 (by omega)
      (node_injective hn hB).injOn s hs

/-- `prop:key-prop-1_extended` (finite-system uniqueness): any vector normalized by
`w₂ = 1` and annihilating the monomials of degrees `0,…,K+1` is the canonical
normalized barycentric vector.  The proof removes the pivot coordinate and applies the
square Vandermonde nonsingularity theorem to the remaining `K+2` distinct nodes. -/
theorem finiteWeight_unique {n B K : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (w : Fin (K + 3) → ℝ)
    (hnormalize : w ⟨2, by omega⟩ = 1)
    (hmoments : ∀ s : ℕ, s ≤ K + 1 →
      ∑ j : Fin (K + 3), w j * node n B j ^ s = 0) :
    w = fun j : Fin (K + 3) ↦ finiteWeight n B K (j : ℕ) := by
  let pivot : Fin (K + 3) := ⟨2, by omega⟩
  let difference : Fin (K + 3) → ℝ :=
    fun j ↦ w j - finiteWeight n B K j
  let reducedNode : Fin (K + 2) → ℝ :=
    fun i ↦ node n B (pivot.succAbove i)
  let reducedDifference : Fin (K + 2) → ℝ :=
    fun i ↦ difference (pivot.succAbove i)
  have hpivot : difference pivot = 0 := by
    dsimp only [difference, pivot]
    rw [hnormalize, finiteWeight_two hn hB K]
    exact sub_self 1
  have hdifferenceMoment (s : ℕ) (hs : s ≤ K + 1) :
      ∑ j : Fin (K + 3), difference j * node n B j ^ s = 0 := by
    calc
      ∑ j : Fin (K + 3), difference j * node n B j ^ s =
          (∑ j : Fin (K + 3), w j * node n B j ^ s) -
            ∑ j : Fin (K + 3), finiteWeight n B K j * node n B j ^ s := by
        simp only [difference, sub_mul, Finset.sum_sub_distrib]
      _ = 0 := by rw [hmoments s hs, finiteWeight_moment_zero hn hB hs, sub_zero]
  have hreducedNode : Function.Injective reducedNode := by
    intro i j hij
    apply Fin.succAbove_right_injective
    apply Fin.ext
    exact (node_injective hn hB) hij
  have hreducedMoments : ∀ s : Fin (K + 2),
      ∑ i : Fin (K + 2), reducedDifference i * reducedNode i ^ (s : ℕ) = 0 := by
    intro s
    have hfull := hdifferenceMoment (s : ℕ) (by omega)
    rw [Fin.sum_univ_succAbove
      (fun j : Fin (K + 3) ↦ difference j * node n B j ^ (s : ℕ)) pivot] at hfull
    rw [hpivot, zero_mul, zero_add] at hfull
    simpa only [reducedDifference, reducedNode] using hfull
  have hreducedZero : reducedDifference = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hreducedNode hreducedMoments
  funext j
  by_cases hj : j = pivot
  · subst j
    dsimp only [pivot] at hnormalize ⊢
    rw [hnormalize, finiteWeight_two hn hB K]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj
    have hzero := congrFun hreducedZero i
    simp only [Pi.zero_apply] at hzero
    dsimp only [reducedDifference, difference] at hzero
    rw [hi] at hzero
    exact sub_eq_zero.mp hzero

/-- `prop:key-prop-1_extended`: existence and uniqueness of the manuscript's finite
normalized annihilating vector. -/
theorem finiteWeight_existsUnique {n B K : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    ∃! w : Fin (K + 3) → ℝ,
      w ⟨2, by omega⟩ = 1 ∧
        ∀ s : ℕ, s ≤ K + 1 → ∑ j : Fin (K + 3), w j * node n B j ^ s = 0 := by
  let w : Fin (K + 3) → ℝ := fun j ↦ finiteWeight n B K (j : ℕ)
  refine ⟨w, ?_, ?_⟩
  · constructor
    · simpa only [w] using finiteWeight_two hn hB K
    · intro s hs
      simpa only [w] using finiteWeight_moment_zero (K := K) hn hB hs
  · intro v hv
    simpa only [w] using finiteWeight_unique hn hB v hv.1 hv.2

/-- `eq:update-impossibility`: adjoining one support point updates every existing normalized
barycentric weight by the displayed factor. -/
theorem finiteWeight_update {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : j < K + 3) :
    finiteWeight n B (K + 1) j = finiteWeight n B K j *
      ((node n B 2 - node n B (K + 3)) /
        (node n B j - node n B (K + 3))) := by
  simp only [finiteWeight, show j < K + 1 + 3 by omega, hj, dif_pos]
  exact barycentricWeight_normalized_succ (node n B) (K + 3) 2 j (by omega) hj
    (node_injective hn hB).injOn

/-- The positive form of the multiplicative update factor. -/
def updateFactor (n B j ell : ℕ) : ℝ :=
  (node n B ell - node n B 2) / (node n B ell - node n B j)

theorem updateFactor_eq {n B j ell : ℕ} :
    updateFactor n B j ell =
      (node n B 2 - node n B ell) / (node n B j - node n B ell) := by
  simp only [updateFactor]
  rw [show node n B 2 - node n B ell = -(node n B ell - node n B 2) by ring,
    show node n B j - node n B ell = -(node n B ell - node n B j) by ring]
  exact (neg_div_neg_eq _ _).symm

theorem updateFactor_pos {n B j ell : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j < ell) (hell : 2 < ell) : 0 < updateFactor n B j ell := by
  exact div_pos (sub_pos.mpr (node_strictMono hn hB hell))
    (sub_pos.mpr (node_strictMono hn hB hj))

theorem updateFactor_le_one_of_le_two {n B j ell : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j ≤ 2) (hell : 2 < ell) : updateFactor n B j ell ≤ 1 := by
  apply (div_le_one₀ (sub_pos.mpr (node_strictMono hn hB (lt_of_le_of_lt hj hell)))).2
  exact sub_le_sub_left ((node_strictMono hn hB).monotone hj) _

theorem one_le_updateFactor_of_two_le {n B j ell : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 2 ≤ j) (hell : j < ell) : 1 ≤ updateFactor n B j ell := by
  apply (one_le_div₀ (sub_pos.mpr (node_strictMono hn hB hell))).2
  exact sub_le_sub_left ((node_strictMono hn hB).monotone hj) _

theorem finiteWeight_updateFactor {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j < K + 3) :
    finiteWeight n B (K + 1) j = finiteWeight n B K j * updateFactor n B j (K + 3) := by
  rw [finiteWeight_update hn hB hj, updateFactor_eq]

/-- The `K=0` weight at the first support point, obtained from the two finite moment
equations. -/
theorem finiteWeight_zero_base {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    finiteWeight n B 0 0 =
      (node n B 2 - node n B 1) / (node n B 1 - node n B 0) := by
  have hzero := finiteWeight_moment_zero (K := 0) hn hB (s := 0) (by omega)
  have hone := finiteWeight_moment_zero (K := 0) hn hB (s := 1) (by omega)
  simp [Fin.sum_univ_succ, finiteWeight_two hn hB] at hzero hone
  have hden : node n B 1 - node n B 0 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (node_strictMono hn hB (by omega)))
  apply (eq_div_iff hden).2
  simp only [node_zero, node_one, node_two]
  nlinarith

/-- The `K=0` weight at the second support point. -/
theorem finiteWeight_one_base {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    finiteWeight n B 0 1 =
      -((node n B 2 - node n B 0) / (node n B 1 - node n B 0)) := by
  have hzero := finiteWeight_moment_zero (K := 0) hn hB (s := 0) (by omega)
  have hone := finiteWeight_moment_zero (K := 0) hn hB (s := 1) (by omega)
  simp [Fin.sum_univ_succ, finiteWeight_two hn hB] at hzero hone
  have hden : node n B 1 - node n B 0 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (node_strictMono hn hB (by omega)))
  rw [← neg_div]
  apply (eq_div_iff hden).2
  simp only [node_zero, node_one, node_two]
  nlinarith

/-- The uniform elementary bound for the first finite weight. -/
theorem abs_finiteWeight_zero_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (K : ℕ) :
    |finiteWeight n B K 0| ≤ 2 * n := by
  induction K with
  | zero =>
      rw [finiteWeight_zero_base hn hB, abs_of_pos (div_pos
        (sub_pos.mpr (node_strictMono hn hB (by omega)))
        (sub_pos.mpr (node_strictMono hn hB (by omega))))]
      simp only [node_zero, node_one, node_two]
      have hden : (0 : ℝ) < (B : ℝ) - 1 :=
        sub_pos.mpr (by exact_mod_cast (show 1 < B by omega))
      rw [div_le_iff₀ hden]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hBreal : (2 : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast (show 2 ≤ B by omega)
      have hBm2 : (0 : ℝ) ≤ (B : ℝ) - (2 : ℝ) := sub_nonneg.mpr hBreal
      nlinarith [mul_nonneg hn0 hBm2]
  | succ K ih =>
      rw [finiteWeight_updateFactor hn hB (by omega), abs_mul,
        abs_of_pos (updateFactor_pos hn hB (by omega) (by omega))]
      calc
        |finiteWeight n B K 0| * updateFactor n B 0 (K + 3) ≤
            |finiteWeight n B K 0| * 1 :=
          mul_le_mul_of_nonneg_left (updateFactor_le_one_of_le_two hn hB (by omega) (by omega))
            (abs_nonneg _)
        _ = |finiteWeight n B K 0| := mul_one _
        _ ≤ 2 * n := ih

/-- The uniform elementary bound for the second finite weight. -/
theorem abs_finiteWeight_one_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (K : ℕ) :
    |finiteWeight n B K 1| ≤ 2 * n := by
  induction K with
  | zero =>
      rw [finiteWeight_one_base hn hB, abs_neg, abs_of_pos (div_pos
        (sub_pos.mpr (node_strictMono hn hB (by omega)))
        (sub_pos.mpr (node_strictMono hn hB (by omega))))]
      simp only [node_zero, node_one, node_two]
      have hden : (0 : ℝ) < (B : ℝ) - 1 :=
        sub_pos.mpr (by exact_mod_cast (show 1 < B by omega))
      rw [div_le_iff₀ hden]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hBreal : (2 : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast (show 2 ≤ B by omega)
      have hBm2 : (0 : ℝ) ≤ (B : ℝ) - (2 : ℝ) := sub_nonneg.mpr hBreal
      nlinarith [mul_nonneg hn0 hBm2]
  | succ K ih =>
      rw [finiteWeight_updateFactor hn hB (by omega), abs_mul,
        abs_of_pos (updateFactor_pos hn hB (by omega) (by omega))]
      calc
        |finiteWeight n B K 1| * updateFactor n B 1 (K + 3) ≤
            |finiteWeight n B K 1| * 1 :=
          mul_le_mul_of_nonneg_left (updateFactor_le_one_of_le_two hn hB (by omega) (by omega))
            (abs_nonneg _)
        _ = |finiteWeight n B K 1| := mul_one _
        _ ≤ 2 * n := ih

/-- Finite normalized weights have the alternating positive sign asserted in
`prop:key-prop-1_extended`. -/
theorem finiteWeight_pos_of_even {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j < K + 3) (heven : Even j) : 0 < finiteWeight n B K j := by
  simp only [finiteWeight, hj, dif_pos]
  exact normalizedBarycentricWeightOn_pos_of_even (node n B) (node_strictMono hn hB)
    (K + 3) j (by omega) hj heven

/-- Finite normalized weights have the alternating negative sign asserted in
`prop:key-prop-1_extended`. -/
theorem finiteWeight_neg_of_odd {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j < K + 3) (hodd : Odd j) : finiteWeight n B K j < 0 := by
  simp only [finiteWeight, hj, dif_pos]
  exact normalizedBarycentricWeightOn_neg_of_odd (node n B) (node_strictMono hn hB)
    (K + 3) j (by omega) hj hodd

theorem finiteWeight_ne_zero {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : j < K + 3) : finiteWeight n B K j ≠ 0 := by
  rcases Nat.even_or_odd j with heven | hodd
  · exact ne_of_gt (finiteWeight_pos_of_even hn hB hj heven)
  · exact ne_of_lt (finiteWeight_neg_of_odd hn hB hj hodd)

/-- The eventual starting index used in `lem:limit-weights-exist`. -/
def startIndex (j : ℕ) : ℕ := max 0 (j - 2)

@[simp] theorem startIndex_eq (j : ℕ) : startIndex j = j - 2 := by
  simp [startIndex]

theorem lt_startIndex_add_three (j : ℕ) : j < startIndex j + 3 := by
  simp only [startIndex_eq]
  omega

theorem two_lt_startIndex_add_three (j : ℕ) : 2 < startIndex j + 3 := by
  omega

/-- Iterating `eq:update-impossibility` expresses a finite weight as its first defined value
times a partial product of positive update factors. -/
theorem finiteWeight_eq_initial_mul_prod {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (t : ℕ) :
    finiteWeight n B (startIndex j + t) j = finiteWeight n B (startIndex j) j *
      ∏ r ∈ Finset.range t, updateFactor n B j (startIndex j + 3 + r) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show startIndex j + (t + 1) = (startIndex j + t) + 1 by omega,
        finiteWeight_updateFactor hn hB (by
          have := lt_startIndex_add_three j
          omega), ih, Finset.prod_range_succ]
      ring

/-- The finite product cancellation underlying the tail estimate in
`lem:all-moment-weight-decay-uniform-K`.  This is the absolute-value form of the
manuscript's displayed barycentric formula at the first system containing index `j`. -/
theorem abs_finiteWeight_initial_formula {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 3 ≤ j) :
    |finiteWeight n B (j - 2) j| =
      ((node n B 2 - node n B 0) * (node n B 2 - node n B 1)) /
          ((node n B j - node n B 0) * (node n B j - node n B 1)) *
        (∏ m ∈ Finset.Ico 3 j,
          (node n B m - node n B 2) / (node n B j - node n B m)) := by
  have hjrange : j < (j - 2) + 3 := by omega
  rw [finiteWeight_eq_product hn hB hjrange, abs_div]
  let mid := Finset.Ico 3 j
  have hnum : (Finset.range ((j - 2) + 3)).erase 2 = ({0, 1} ∪ mid) ∪ {j} := by
    ext i
    simp [mid]
    omega
  have hden : (Finset.range ((j - 2) + 3)).erase j = ({0, 1, 2} ∪ mid) := by
    ext i
    simp [mid]
    omega
  rw [hnum, hden]
  have hd1 : Disjoint ({0, 1} : Finset ℕ) mid := by
    rw [Finset.disjoint_left]
    simp [mid]
  have hd2 : Disjoint (({0, 1} : Finset ℕ) ∪ mid) ({j} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    simp [mid]
    omega
  have hd3 : Disjoint ({0, 1, 2} : Finset ℕ) mid := by
    rw [Finset.disjoint_left]
    simp [mid]
  rw [Finset.prod_union hd2, Finset.prod_union hd1, Finset.prod_union hd3]
  simp only [Finset.prod_singleton, abs_mul, Finset.abs_prod]
  have hp01n : (∏ x ∈ ({0, 1} : Finset ℕ), |node n B 2 - node n B x|) =
      (node n B 2 - node n B 0) * (node n B 2 - node n B 1) := by
    rw [Finset.prod_pair (by omega),
      abs_of_pos (sub_pos.mpr (node_strictMono hn hB (by omega))),
      abs_of_pos (sub_pos.mpr (node_strictMono hn hB (by omega)))]
  have hp012d : (∏ x ∈ ({0, 1, 2} : Finset ℕ), |node n B j - node n B x|) =
      (node n B j - node n B 0) *
        ((node n B j - node n B 1) * (node n B j - node n B 2)) := by
    rw [Finset.prod_insert (by simp : 0 ∉ ({1, 2} : Finset ℕ)),
      Finset.prod_pair (by omega),
      abs_of_pos (sub_pos.mpr (node_strictMono hn hB (by omega))),
      abs_of_pos (sub_pos.mpr (node_strictMono hn hB (by omega))),
      abs_of_pos (sub_pos.mpr (node_strictMono hn hB (by omega)))]
  rw [hp01n, hp012d]
  have hnumMid : (∏ x ∈ mid, |node n B 2 - node n B x|) =
      ∏ x ∈ mid, (node n B x - node n B 2) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [abs_of_neg]
    · ring
    · exact sub_neg.mpr (node_strictMono hn hB (by
        have := (Finset.mem_Ico.mp hx).1
        omega))
  have hdenMid : (∏ x ∈ mid, |node n B j - node n B x|) =
      ∏ x ∈ mid, (node n B j - node n B x) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [abs_of_pos (sub_pos.mpr (node_strictMono hn hB (Finset.mem_Ico.mp hx).2))]
  rw [hnumMid, hdenMid,
    abs_of_neg (sub_neg.mpr (node_strictMono hn hB (by omega : 2 < j)))]
  dsimp only [mid]
  rw [Finset.prod_div_distrib]
  have hD : (node n B j - node n B 0) * (node n B j - node n B 1) ≠ 0 :=
    mul_ne_zero
      (sub_ne_zero.mpr ((node_injective hn hB).ne (by omega)))
      (sub_ne_zero.mpr ((node_injective hn hB).ne (by omega)))
  have hQ : (∏ x ∈ Finset.Ico 3 j, (node n B j - node n B x)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    exact sub_ne_zero.mpr
      ((node_injective hn hB).ne (Finset.mem_Ico.mp hx).2.ne.symm)
  have hj2 : node n B j - node n B 2 ≠ 0 :=
    sub_ne_zero.mpr ((node_injective hn hB).ne (by omega))
  field_simp
  ring

/-- Absolute-value version of the iterated update formula. -/
theorem abs_finiteWeight_eq_initial_mul_prod {n B K j : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hK : startIndex j ≤ K) :
    |finiteWeight n B K j| = |finiteWeight n B (startIndex j) j| *
      ∏ r ∈ Finset.range (K - startIndex j),
        updateFactor n B j (startIndex j + 3 + r) := by
  have hKsplit : startIndex j + (K - startIndex j) = K := Nat.add_sub_of_le hK
  conv_lhs => rw [← hKsplit, finiteWeight_eq_initial_mul_prod hn hB]
  rw [abs_mul, Finset.abs_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  rw [abs_of_pos]
  exact updateFactor_pos hn hB (by
    have := lt_startIndex_add_three j
    omega) (by omega)

theorem middleFactor_nonneg {n B j m : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hm : m ∈ Finset.Ico 3 j) :
    0 ≤ (node n B m - node n B 2) / (node n B j - node n B m) := by
  exact (div_pos (sub_pos.mpr (node_strictMono hn hB (by
      have := (Finset.mem_Ico.mp hm).1
      omega)))
    (sub_pos.mpr (node_strictMono hn hB (Finset.mem_Ico.mp hm).2))).le

theorem middleFactor_le_one {n B j m : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hm : m ∈ Finset.Ico 3 j) :
    (node n B m - node n B 2) / (node n B j - node n B m) ≤ 1 := by
  have hm3 : 2 ≤ m := by have := (Finset.mem_Ico.mp hm).1; omega
  have hmj : m + 1 ≤ j := by have := (Finset.mem_Ico.mp hm).2; omega
  have hdouble : 2 * node n B m ≤ node n B j :=
    (node_succ_ge_two_mul hn hB hm3).trans
      ((node_strictMono hn hB).monotone hmj)
  have hnumden : node n B m - node n B 2 ≤ node n B j - node n B m := by
    have hnode2 : 0 ≤ node n B 2 := (node_pos hn hB 2).le
    linarith
  exact (div_le_one₀ (sub_pos.mpr
    (node_strictMono hn hB (Finset.mem_Ico.mp hm).2))).2 hnumden

theorem middleProduct_nonneg {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    0 ≤ ∏ m ∈ Finset.Ico 3 j,
      (node n B m - node n B 2) / (node n B j - node n B m) := by
  exact Finset.prod_nonneg fun m hm ↦ middleFactor_nonneg hn hB hm

theorem middleProduct_le_one {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∏ m ∈ Finset.Ico 3 j,
      (node n B m - node n B 2) / (node n B j - node n B m)) ≤ 1 := by
  exact Finset.prod_le_one (fun m hm ↦ middleFactor_nonneg hn hB hm)
    (fun m hm ↦ middleFactor_le_one hn hB hm)

/-- A factor among the last indices before `j` gains the reciprocal-power decay used in
`lem:all-moment-weight-decay`. -/
theorem middleFactor_le_two_mul_prev_div {n B j m : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 4 ≤ j) (hm3 : 3 ≤ m) (hmj : m < j) :
    (node n B m - node n B 2) / (node n B j - node n B m) ≤
      2 * node n B (j - 1) / node n B j := by
  have hm2 : 2 ≤ m := by omega
  have hmjp : m + 1 ≤ j := by omega
  have hdouble : 2 * node n B m ≤ node n B j :=
    (node_succ_ge_two_mul hn hB hm2).trans
      ((node_strictMono hn hB).monotone hmjp)
  have hdenhalf : node n B j / 2 ≤ node n B j - node n B m := by linarith
  have hnum : node n B m - node n B 2 ≤ node n B (j - 1) := by
    have hmle : m ≤ j - 1 := by omega
    have hmmono := (node_strictMono hn hB).monotone hmle
    linarith [node_pos hn hB 2]
  have hdenpos : 0 < node n B j - node n B m :=
    sub_pos.mpr (node_strictMono hn hB hmj)
  have hhalfpos : 0 < node n B j / 2 := div_pos (node_pos hn hB j) (by norm_num)
  calc
    (node n B m - node n B 2) / (node n B j - node n B m) ≤
        node n B (j - 1) / (node n B j / 2) := by
      exact div_le_div₀ (node_pos hn hB (j - 1)).le hnum hhalfpos hdenhalf
    _ = 2 * node n B (j - 1) / node n B j := by field_simp

/-- Dropping the early factors, all of which lie in `[0,1]`, leaves only the final `L`
factors of the middle product. -/
theorem middleProduct_le_last {n B j L : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hLj : L + 3 ≤ j) :
    (∏ m ∈ Finset.Ico 3 j,
        (node n B m - node n B 2) / (node n B j - node n B m)) ≤
      ∏ m ∈ Finset.Ico (j - L) j,
        (node n B m - node n B 2) / (node n B j - node n B m) := by
  let f : ℕ → ℝ := fun m ↦
    (node n B m - node n B 2) / (node n B j - node n B m)
  have hsplit : 3 ≤ j - L := by omega
  have htail0 : 0 ≤ ∏ m ∈ Finset.Ico (j - L) j, f m := by
    exact Finset.prod_nonneg fun m hm ↦ middleFactor_nonneg hn hB (by
      exact Finset.mem_Ico.mpr ⟨hsplit.trans (Finset.mem_Ico.mp hm).1,
        (Finset.mem_Ico.mp hm).2⟩)
  have hearly : (∏ m ∈ Finset.Ico 3 (j - L), f m) ≤ 1 := by
    exact Finset.prod_le_one
      (fun m hm ↦ middleFactor_nonneg hn hB (by
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hm).1,
          (Finset.mem_Ico.mp hm).2.trans_le (Nat.sub_le _ _)⟩))
      (fun m hm ↦ middleFactor_le_one hn hB (by
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hm).1,
          (Finset.mem_Ico.mp hm).2.trans_le (Nat.sub_le _ _)⟩))
  change (∏ m ∈ Finset.Ico 3 j, f m) ≤ ∏ m ∈ Finset.Ico (j - L) j, f m
  rw [← Finset.prod_Ico_consecutive f hsplit (Nat.sub_le _ _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hearly htail0

/-- A deliberately simple (`L=2M`) version of the manuscript's last-factor estimate.  It is
used as a domination lemma while the sharper explicit `L_M` estimate below records the paper's
constant exactly. -/
theorem middleProduct_le_crude_power {n B M j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hM : 2 ≤ M) (hj : 2 * M + 3 ≤ j) :
    (∏ m ∈ Finset.Ico 3 j,
        (node n B m - node n B 2) / (node n B j - node n B m)) ≤
      (2 : ℝ) ^ (2 * M) / node n B j ^ (M - 2) := by
  let c : ℝ := 2 * node n B (j - 1) / node n B j
  have hj4 : 4 ≤ j := by omega
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact div_nonneg (mul_nonneg (by norm_num) (node_pos hn hB (j - 1)).le)
      (node_pos hn hB j).le
  have htail : (∏ m ∈ Finset.Ico (j - 2 * M) j,
      (node n B m - node n B 2) / (node n B j - node n B m)) ≤ c ^ (2 * M) := by
    calc
      (∏ m ∈ Finset.Ico (j - 2 * M) j,
          (node n B m - node n B 2) / (node n B j - node n B m)) ≤
          ∏ _m ∈ Finset.Ico (j - 2 * M) j, c := by
        apply Finset.prod_le_prod
        · intro m hm
          exact middleFactor_nonneg hn hB (by
            have hmem := Finset.mem_Ico.mp hm
            exact Finset.mem_Ico.mpr ⟨by omega, hmem.2⟩)
        · intro m hm
          apply middleFactor_le_two_mul_prev_div hn hB hj4
          · have := (Finset.mem_Ico.mp hm).1
            omega
          · exact (Finset.mem_Ico.mp hm).2
      _ = c ^ (2 * M) := by
        have hcard : j - (j - 2 * M) = 2 * M := by omega
        simp only [Finset.prod_const, Nat.card_Ico, hcard]
  have hBlin : B ≤ 2 * (B - 1) := by omega
  have hcond : B * (M - 2) ≤ (2 * M) * (B - 1) := by
    calc
      B * (M - 2) ≤ B * M := Nat.mul_le_mul_left B (Nat.sub_le M 2)
      _ ≤ (2 * M) * (B - 1) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          (Nat.mul_le_mul_right M hBlin)
  have hexp : 2 * M + B * (M - 2) ≤ B * (2 * M) := by
    calc
      2 * M + B * (M - 2) ≤ 2 * M + (2 * M) * (B - 1) :=
        Nat.add_le_add_left hcond (2 * M)
      _ = (2 * M) * (1 + (B - 1)) := by ring
      _ = (2 * M) * B := by congr 1 <;> omega
      _ = B * (2 * M) := by ring
  have hjpred : j - 1 + 1 = j := by omega
  have hrec : node n B j = node n B (j - 1) ^ B := by
    rw [← hjpred]
    exact node_succ_eq_pow (j - 1) (by omega)
  have hy1 : (1 : ℝ) ≤ node n B (j - 1) := by
    exact (show (1 : ℝ) ≤ node n B 0 by simp).trans
      ((node_strictMono hn hB).monotone (Nat.zero_le _))
  have hpowexp : node n B (j - 1) ^ (2 * M + B * (M - 2)) ≤
      node n B (j - 1) ^ (B * (2 * M)) :=
    pow_le_pow_right₀ hy1 hexp
  have hratio : c ^ (2 * M) ≤
      (2 : ℝ) ^ (2 * M) / node n B j ^ (M - 2) := by
    have hxpos : 0 < node n B j := node_pos hn hB j
    have hcpow : c ^ (2 * M) =
        (2 : ℝ) ^ (2 * M) * node n B (j - 1) ^ (2 * M) /
          node n B j ^ (2 * M) := by
      dsimp only [c]
      rw [div_pow]
      ring
    rw [hcpow, div_le_div_iff₀ (pow_pos hxpos _) (pow_pos hxpos _)]
    have hinner : node n B (j - 1) ^ (2 * M) * node n B j ^ (M - 2) ≤
        node n B j ^ (2 * M) := by
      rw [hrec]
      simpa only [← pow_mul, ← pow_add] using hpowexp
    calc
      (2 : ℝ) ^ (2 * M) * node n B (j - 1) ^ (2 * M) *
          node n B j ^ (M - 2) =
          (2 : ℝ) ^ (2 * M) *
            (node n B (j - 1) ^ (2 * M) * node n B j ^ (M - 2)) := by ring
      _ ≤ (2 : ℝ) ^ (2 * M) * node n B j ^ (2 * M) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
  exact (middleProduct_le_last hn hB hj).trans (htail.trans hratio)

theorem core_nonneg {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : 3 ≤ j) :
    0 ≤ ((node n B 2 - node n B 0) * (node n B 2 - node n B 1)) /
      ((node n B j - node n B 0) * (node n B j - node n B 1)) := by
  exact div_nonneg
    (mul_nonneg
      (sub_nonneg.mpr ((node_strictMono hn hB).monotone (by omega)))
      (sub_nonneg.mpr ((node_strictMono hn hB).monotone (by omega))))
    (mul_nonneg
      (sub_nonneg.mpr ((node_strictMono hn hB).monotone (by omega)))
      (sub_nonneg.mpr ((node_strictMono hn hB).monotone (by omega))))

theorem core_le_four_mul {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : 3 ≤ j) :
    ((node n B 2 - node n B 0) * (node n B 2 - node n B 1)) /
        ((node n B j - node n B 0) * (node n B j - node n B 1)) ≤
      4 * node n B 2 ^ 2 / node n B j ^ 2 := by
  have hx2 : 0 < node n B 2 := node_pos hn hB 2
  have hxj : 0 < node n B j := node_pos hn hB j
  have h2x0 : 0 < node n B 2 - node n B 0 :=
    sub_pos.mpr (node_strictMono hn hB (by omega))
  have h2x1 : 0 < node n B 2 - node n B 1 :=
    sub_pos.mpr (node_strictMono hn hB (by omega))
  have hnum : (node n B 2 - node n B 0) * (node n B 2 - node n B 1) ≤
      node n B 2 ^ 2 := by
    nlinarith [node_pos hn hB 0, node_pos hn hB 1]
  have htwoj : 2 * node n B 2 ≤ node n B j :=
    (node_succ_ge_two_mul hn hB (j := 2) (by omega)).trans
      ((node_strictMono hn hB).monotone (by omega : 3 ≤ j))
  have hj0 : node n B j / 2 ≤ node n B j - node n B 0 := by
    have h0le2 := (node_strictMono hn hB).monotone (by omega : 0 ≤ 2)
    linarith
  have hj1 : node n B j / 2 ≤ node n B j - node n B 1 := by
    have h1le2 := (node_strictMono hn hB).monotone (by omega : 1 ≤ 2)
    linarith
  have hden : (node n B j / 2) ^ 2 ≤
      (node n B j - node n B 0) * (node n B j - node n B 1) := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hj0) (sub_nonneg.mpr hj1)]
  calc
    ((node n B 2 - node n B 0) * (node n B 2 - node n B 1)) /
        ((node n B j - node n B 0) * (node n B j - node n B 1)) ≤
      node n B 2 ^ 2 / (node n B j / 2) ^ 2 := by
        exact div_le_div₀ (sq_nonneg (node n B 2)) hnum
          (sq_pos_of_pos (by positivity)) hden
    _ = 4 * node n B 2 ^ 2 / node n B j ^ 2 := by field_simp <;> ring

theorem abs_finiteWeight_initial_le {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 3 ≤ j) :
    |finiteWeight n B (j - 2) j| ≤ 4 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by
  rw [abs_finiteWeight_initial_formula hn hB hj]
  calc
    ((node n B 2 - node n B 0) * (node n B 2 - node n B 1)) /
          ((node n B j - node n B 0) * (node n B j - node n B 1)) *
        (∏ m ∈ Finset.Ico 3 j,
          (node n B m - node n B 2) / (node n B j - node n B m)) ≤
      (4 * node n B 2 ^ 2 / node n B j ^ 2) * 1 := by
        calc
          _ ≤ (4 * node n B 2 ^ 2 / node n B j ^ 2) *
              (∏ m ∈ Finset.Ico 3 j,
                (node n B m - node n B 2) / (node n B j - node n B m)) :=
            mul_le_mul_of_nonneg_right (core_le_four_mul hn hB hj)
              (middleProduct_nonneg hn hB)
          _ ≤ (4 * node n B 2 ^ 2 / node n B j ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (middleProduct_le_one hn hB) (by positivity)
    _ = 4 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by simp

theorem sum_inv_node_tail_le {n B q t : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hq : 2 ≤ q) :
    (∑ r ∈ Finset.range t, 1 / node n B (q + r)) ≤ 2 / node n B q := by
  calc
    (∑ r ∈ Finset.range t, 1 / node n B (q + r)) ≤
        ∑ r ∈ Finset.range t, (1 / node n B q) * (1 / 2 : ℝ) ^ r := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        1 / node n B (q + r) ≤ 1 / (node n B q * 2 ^ r) :=
          one_div_le_one_div_of_le
            (mul_pos (node_pos hn hB q) (pow_pos (by norm_num) _))
            (node_ge_geometric_from hn hB hq r)
        _ = (1 / node n B q) * (1 / 2 : ℝ) ^ r := by
          simp only [one_div, mul_inv_rev, inv_pow]
          ring
    _ = (1 / node n B q) * ∑ r ∈ Finset.range t, (1 / 2 : ℝ) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ (1 / node n B q) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le t)
        (one_div_nonneg.mpr (node_pos hn hB q).le)
    _ = 2 / node n B q := by ring

theorem updateFactor_sub_one_nonneg {n B j ell : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 2 ≤ j) (hell : j < ell) : 0 ≤ updateFactor n B j ell - 1 := by
  linarith [one_le_updateFactor_of_two_le hn hB hj hell]

theorem updateFactor_sub_one_le {n B j ell : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 2 ≤ j) (hell : j < ell) (htwo : 2 * node n B j ≤ node n B ell) :
    updateFactor n B j ell - 1 ≤ 2 * node n B j / node n B ell := by
  have hdenpos : 0 < node n B ell - node n B j :=
    sub_pos.mpr (node_strictMono hn hB hell)
  have hformula : updateFactor n B j ell - 1 =
      (node n B j - node n B 2) / (node n B ell - node n B j) := by
    have hden : node n B ell - node n B j ≠ 0 := ne_of_gt hdenpos
    simp only [updateFactor]
    field_simp
    ring
  rw [hformula]
  have hhalf : node n B ell / 2 ≤ node n B ell - node n B j := by linarith
  have hinv : 1 / (node n B ell - node n B j) ≤ 2 / node n B ell := by
    calc
      1 / (node n B ell - node n B j) ≤ 1 / (node n B ell / 2) :=
        one_div_le_one_div_of_le
          (div_pos (node_pos hn hB ell) (by norm_num)) hhalf
      _ = 2 / node n B ell := by field_simp
  have hnum : 0 ≤ node n B j - node n B 2 :=
    sub_nonneg.mpr ((node_strictMono hn hB).monotone hj)
  calc
    (node n B j - node n B 2) / (node n B ell - node n B j) =
        (node n B j - node n B 2) * (1 / (node n B ell - node n B j)) := by ring
    _ ≤ (node n B j - node n B 2) * (2 / node n B ell) :=
      mul_le_mul_of_nonneg_left hinv hnum
    _ ≤ node n B j * (2 / node n B ell) := by
      exact mul_le_mul_of_nonneg_right (sub_le_self _ (node_pos hn hB 2).le)
        (div_nonneg (by norm_num) (node_pos hn hB ell).le)
    _ = 2 * node n B j / node n B ell := by ring

theorem sum_updateFactor_sub_one_le {n B j t : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 3 ≤ j) :
    (∑ r ∈ Finset.range t, (updateFactor n B j (j + 1 + r) - 1)) ≤
      4 / node n B j ^ 2 := by
  have hpoint : ∀ r, updateFactor n B j (j + 1 + r) - 1 ≤
      2 * node n B j / node n B (j + 1 + r) := by
    intro r
    apply updateFactor_sub_one_le hn hB (by omega) (by omega)
    exact (node_succ_ge_two_mul hn hB (j := j) (by omega)).trans
      ((node_strictMono hn hB).monotone (by omega))
  calc
    (∑ r ∈ Finset.range t, (updateFactor n B j (j + 1 + r) - 1)) ≤
        ∑ r ∈ Finset.range t, 2 * node n B j / node n B (j + 1 + r) := by
      exact Finset.sum_le_sum fun r hr ↦ hpoint r
    _ = 2 * node n B j *
        (∑ r ∈ Finset.range t, 1 / node n B (j + 1 + r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ 2 * node n B j * (2 / node n B (j + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_inv_node_tail_le (q := j + 1) (t := t) hn hB (by omega))
        (mul_nonneg (by norm_num) (node_pos hn hB j).le)
    _ ≤ 4 / node n B j ^ 2 := by
      rw [node_succ_eq_pow j (by omega)]
      have hx : 1 ≤ node n B j := (two_le_node hn hB (by omega)).trans' (by norm_num)
      have hpow : node n B j ^ 3 ≤ node n B j ^ B :=
        pow_le_pow_right₀ hx (by omega)
      have hinv := one_div_le_one_div_of_le (pow_pos (node_pos hn hB j) 3) hpow
      have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 4 * node n B j)
      calc
        2 * node n B j * (2 / node n B j ^ B) =
            (4 * node n B j) * (1 / node n B j ^ B) := by ring
        _ ≤ (4 * node n B j) * (1 / node n B j ^ 3) := hmul
        _ = 4 / node n B j ^ 2 := by field_simp <;> ring

theorem tailUpdateProduct_lt_two {n B j t : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 3 ≤ j) :
    (∏ r ∈ Finset.range t, updateFactor n B j (j + 1 + r)) < 2 := by
  let delta : ℕ → ℝ := fun r ↦ updateFactor n B j (j + 1 + r) - 1
  have hdelta : ∀ r, 0 ≤ delta r := fun r ↦
    updateFactor_sub_one_nonneg hn hB (by omega) (by omega)
  have hsum0 : 0 ≤ ∑ r ∈ Finset.range t, delta r :=
    Finset.sum_nonneg fun r hr ↦ hdelta r
  have hsum : (∑ r ∈ Finset.range t, delta r) ≤ 4 / node n B j ^ 2 := by
    simpa only [delta] using sum_updateFactor_sub_one_le hn hB hj (t := t)
  have hxj4 : (4 : ℝ) ≤ node n B j := by
    exact (show (4 : ℝ) ≤ node n B 2 by
      rw [node_two]
      exact_mod_cast (show 4 ≤ n * B by nlinarith)).trans
        ((node_strictMono hn hB).monotone (by omega))
  have hquarter : 4 / node n B j ^ 2 ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos (node_pos hn hB j))]
    nlinarith [sq_nonneg (node n B j - 4)]
  have hprodexp := Real.prod_one_add_le_exp_sum (Finset.range t) hdelta
  have hexpquarter : Real.exp (1 / 4 : ℝ) < 2 := by
    have hb := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at hb ⊢
    linarith
  calc
    (∏ r ∈ Finset.range t, updateFactor n B j (j + 1 + r)) =
        ∏ r ∈ Finset.range t, (1 + delta r) := by
      apply Finset.prod_congr rfl
      intro r hr
      simp only [delta]
      ring
    _ ≤ Real.exp (∑ r ∈ Finset.range t, delta r) := hprodexp
    _ ≤ Real.exp (1 / 4) := Real.exp_monotone (hsum.trans hquarter)
    _ < 2 := hexpquarter

/-- The finite barycentric coefficient bound before discarding the middle product.  This is the
quantitative form used for every moment order in
`lem:all-moment-weight-decay-uniform-K`. -/
theorem finiteWeight_le_eight_mul_middle {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hj : 3 ≤ j) (hjK : j < K + 3) :
    |finiteWeight n B K j| ≤
      (8 * (n * B : ℝ) ^ 2 / node n B j ^ 2) *
        (∏ m ∈ Finset.Ico 3 j,
          (node n B m - node n B 2) / (node n B j - node n B m)) := by
  have hK : startIndex j ≤ K := by
    simp only [startIndex_eq]
    omega
  rw [abs_finiteWeight_eq_initial_mul_prod hn hB hK]
  have hstart : startIndex j = j - 2 := startIndex_eq j
  rw [hstart, abs_finiteWeight_initial_formula hn hB hj]
  let core : ℝ :=
    ((node n B 2 - node n B 0) * (node n B 2 - node n B 1)) /
      ((node n B j - node n B 0) * (node n B j - node n B 1))
  let mid : ℝ := ∏ m ∈ Finset.Ico 3 j,
    (node n B m - node n B 2) / (node n B j - node n B m)
  let tail : ℝ := ∏ r ∈ Finset.range (K - (j - 2)),
    updateFactor n B j (j - 2 + 3 + r)
  have hcore : core ≤ 4 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by
    dsimp only [core]
    simpa only [node_two] using core_le_four_mul hn hB hj
  have hcore0 : 0 ≤ core := by
    dsimp only [core]
    exact core_nonneg hn hB hj
  have hmid0 : 0 ≤ mid := by
    dsimp only [mid]
    exact middleProduct_nonneg hn hB
  have htail0 : 0 ≤ tail := by
    dsimp only [tail]
    exact Finset.prod_nonneg fun r hr ↦
      (updateFactor_pos hn hB (by omega) (by omega)).le
  have htail : tail < 2 := by
    dsimp only [tail]
    simpa only [show j - 2 + 3 = j + 1 by omega] using
      tailUpdateProduct_lt_two hn hB hj (t := K - (j - 2))
  change core * mid * tail ≤
    (8 * (n * B : ℝ) ^ 2 / node n B j ^ 2) * mid
  calc
    core * mid * tail ≤
        (4 * (n * B : ℝ) ^ 2 / node n B j ^ 2) * mid * 2 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hcore hmid0) htail.le htail0
        (mul_nonneg (by positivity) hmid0)
    _ = (8 * (n * B : ℝ) ^ 2 / node n B j ^ 2) * mid := by ring

/-- The `M=2` case of `lem:all-moment-weight-decay-uniform-K`, including the zero extension
outside the finite system. -/
theorem finiteWeight_decay_two {n B K j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    |finiteWeight n B K j| ≤ 8 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by
  by_cases hjrange : j < K + 3
  · by_cases hj0 : j = 0
    · subst j
      calc
        |finiteWeight n B K 0| ≤ 2 * n := abs_finiteWeight_zero_le hn hB K
        _ ≤ 8 * (n * B : ℝ) ^ 2 / node n B 0 ^ 2 := by
          simp only [node_zero, one_pow, div_one]
          have hn0 : (0 : ℝ) ≤ n := by positivity
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          have hB0 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
          have hnnB : (n : ℝ) ≤ n * B := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hB0 hn0
          have hnb0 : (0 : ℝ) ≤ n * B := by positivity
          have hnb1 : (1 : ℝ) ≤ n * B := hn1.trans hnnB
          have hnb_sq : (n * B : ℝ) ≤ (n * B : ℝ) ^ 2 := by
            rw [pow_two]
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hnb1 hnb0
          nlinarith [hnnB, hnb_sq]
    · by_cases hj1 : j = 1
      · subst j
        calc
        |finiteWeight n B K 1| ≤ 2 * n := abs_finiteWeight_one_le hn hB K
        _ ≤ 8 * (n * B : ℝ) ^ 2 / node n B 1 ^ 2 := by
          simp only [node_one]
          have hBne : (B : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by positivity)
          have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
          field_simp
          nlinarith
      · by_cases hj2 : j = 2
        · subst j
          rw [finiteWeight_two hn hB]
          simp only [abs_one, node_two]
          have hne : (n * B : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by positivity)
          field_simp
          norm_num
        · have hj3 : 3 ≤ j := by omega
          have hK : startIndex j ≤ K := by
            simp only [startIndex_eq]
            omega
          rw [abs_finiteWeight_eq_initial_mul_prod hn hB hK]
          have hstart : startIndex j = j - 2 := startIndex_eq j
          have htail : (∏ r ∈ Finset.range (K - startIndex j),
              updateFactor n B j (startIndex j + 3 + r)) < 2 := by
            simpa only [hstart, show j - 2 + 3 = j + 1 by omega] using
              tailUpdateProduct_lt_two hn hB hj3 (t := K - startIndex j)
          have hinitial : |finiteWeight n B (startIndex j) j| ≤
              4 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by
            simpa only [startIndex_eq] using abs_finiteWeight_initial_le hn hB hj3
          have hinit0 : 0 ≤ 4 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by positivity
          calc
            |finiteWeight n B (startIndex j) j| *
                (∏ r ∈ Finset.range (K - startIndex j),
                  updateFactor n B j (startIndex j + 3 + r)) ≤
              (4 * (n * B : ℝ) ^ 2 / node n B j ^ 2) * 2 := by
                exact mul_le_mul hinitial htail.le (Finset.prod_nonneg fun r hr ↦
                  (updateFactor_pos hn hB (by
                    have := lt_startIndex_add_three j
                    omega) (by omega)).le) hinit0
            _ = 8 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by ring
  · rw [finiteWeight_eq_zero_of_ge (Nat.le_of_not_gt hjrange), abs_zero]
    positivity

/-- A simple explicit domination constant.  Unlike the sharper manuscript constant `C_M`, this
one uses `2M` last factors; its sole purpose is to provide a compact summable majorant for the
dominated-limit construction. -/
def crudeDecayConstant (n B M : ℕ) : ℝ :=
  8 * (n * B : ℝ) ^ 2 *
    max (node n B (2 * M + 2) ^ (M - 2)) ((2 : ℝ) ^ (2 * M))

theorem crudeDecayConstant_nonneg (n B M : ℕ) :
    0 ≤ crudeDecayConstant n B M := by
  unfold crudeDecayConstant
  positivity

/-- Uniform-in-`K` all-order decay, with the auxiliary explicit domination constant above. -/
theorem finiteWeight_decay_crude {n B K j M : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hM : 2 ≤ M) :
    |finiteWeight n B K j| ≤ crudeDecayConstant n B M / node n B j ^ M := by
  let A : ℝ := 8 * (n * B : ℝ) ^ 2
  let L : ℕ := 2 * M
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hxpos : 0 < node n B j := node_pos hn hB j
  have hpowM : node n B j ^ M =
      node n B j ^ 2 * node n B j ^ (M - 2) := by
    rw [← pow_add]
    congr 1
    omega
  by_cases hjrange : j < K + 3
  · by_cases hjlarge : L + 3 ≤ j
    · have hj3 : 3 ≤ j := by omega
      have hraw := finiteWeight_le_eight_mul_middle hn hB hj3 hjrange
      have hmiddle := middleProduct_le_crude_power hn hB hM (by simpa only [L] using hjlarge)
      calc
        |finiteWeight n B K j| ≤
            (A / node n B j ^ 2) *
              (∏ m ∈ Finset.Ico 3 j,
                (node n B m - node n B 2) / (node n B j - node n B m)) := by
          simpa only [A] using hraw
        _ ≤ (A / node n B j ^ 2) *
              ((2 : ℝ) ^ L / node n B j ^ (M - 2)) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [L] using hmiddle) (by positivity)
        _ = (A * (2 : ℝ) ^ L) / node n B j ^ M := by
          rw [hpowM]
          field_simp
        _ ≤ (A * max (node n B (L + 2) ^ (M - 2)) ((2 : ℝ) ^ L)) /
              node n B j ^ M := by
          gcongr
          exact le_max_right _ _
        _ = crudeDecayConstant n B M / node n B j ^ M := by
          simp only [crudeDecayConstant, A, L]
    · have hjcut : j ≤ L + 2 := by omega
      have hnode : node n B j ≤ node n B (L + 2) :=
        (node_strictMono hn hB).monotone hjcut
      have hpow : node n B j ^ (M - 2) ≤ node n B (L + 2) ^ (M - 2) := by
        exact pow_le_pow_left₀ (node_pos hn hB j).le hnode (M - 2)
      calc
        |finiteWeight n B K j| ≤ A / node n B j ^ 2 := by
          simpa only [A] using finiteWeight_decay_two (n := n) (B := B) (K := K) (j := j) hn hB
        _ = (A * node n B j ^ (M - 2)) / node n B j ^ M := by
          rw [hpowM]
          field_simp
        _ ≤ (A * node n B (L + 2) ^ (M - 2)) / node n B j ^ M := by
          gcongr
        _ ≤ (A * max (node n B (L + 2) ^ (M - 2)) ((2 : ℝ) ^ L)) /
              node n B j ^ M := by
          gcongr
          exact le_max_left _ _
        _ = crudeDecayConstant n B M / node n B j ^ M := by
          simp only [crudeDecayConstant, A, L]
  · rw [finiteWeight_eq_zero_of_ge (Nat.le_of_not_gt hjrange), abs_zero]
    exact div_nonneg (crudeDecayConstant_nonneg n B M) (pow_nonneg hxpos.le _)

/-- The update factor is `1` plus the summable perturbation appearing in the manuscript's
infinite product. -/
theorem updateFactor_sub_one {n B j ell : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hjell : j < ell) :
    updateFactor n B j ell - 1 =
      (node n B j - node n B 2) / (node n B ell - node n B j) := by
  have hden : node n B ell - node n B j ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (node_strictMono hn hB hjell))
  simp only [updateFactor]
  field_simp
  ring

theorem two_mul_node_le_start {n B j r : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    2 * node n B j ≤ node n B (startIndex j + 3 + r) := by
  by_cases hj : j ≤ 2
  · calc
      2 * node n B j ≤ 2 * node n B 2 := by
        gcongr
        exact (node_strictMono hn hB).monotone hj
      _ ≤ node n B 3 := by
        simpa using node_succ_ge_two_mul hn hB (j := 2) (by omega)
      _ ≤ node n B (startIndex j + 3 + r) := by
        apply (node_strictMono hn hB).monotone
        omega
  · have hj2 : 2 ≤ j := by omega
    calc
      2 * node n B j ≤ node n B (j + 1) := node_succ_ge_two_mul hn hB hj2
      _ ≤ node n B (startIndex j + 3 + r) := by
        apply (node_strictMono hn hB).monotone
        simp only [startIndex_eq]
        omega

/-- The perturbations in the fixed-index update product are absolutely summable. -/
theorem summable_updateFactor_sub_one {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (fun r : ℕ ↦ updateFactor n B j (startIndex j + 3 + r) - 1) := by
  let c : ℝ := 2 * |node n B j - node n B 2|
  have htail : Summable (fun r : ℕ ↦ 1 / node n B (startIndex j + 3 + r)) := by
    have h := (summable_inv_node hn hB).comp_injective
      (add_left_injective (startIndex j + 3))
    simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using h
  apply (htail.mul_left c).of_norm_bounded
  intro r
  have hjell : j < startIndex j + 3 + r := by
    have := lt_startIndex_add_three j
    omega
  have hellpos : 0 < node n B (startIndex j + 3 + r) := node_pos hn hB _
  have hdenpos : 0 < node n B (startIndex j + 3 + r) - node n B j :=
    sub_pos.mpr (node_strictMono hn hB hjell)
  have hhalf : node n B (startIndex j + 3 + r) / 2 ≤
      node n B (startIndex j + 3 + r) - node n B j := by
    have htwo := two_mul_node_le_start (n := n) (B := B) (j := j) (r := r) hn hB
    linarith
  have hinv : 1 / (node n B (startIndex j + 3 + r) - node n B j) ≤
      2 / node n B (startIndex j + 3 + r) := by
    calc
      1 / (node n B (startIndex j + 3 + r) - node n B j) ≤
          1 / (node n B (startIndex j + 3 + r) / 2) :=
        one_div_le_one_div_of_le (by positivity) hhalf
      _ = 2 / node n B (startIndex j + 3 + r) := by field_simp
  rw [updateFactor_sub_one hn hB hjell, Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
  calc
    |node n B j - node n B 2| /
          (node n B (startIndex j + 3 + r) - node n B j) =
        |node n B j - node n B 2| *
          (1 / (node n B (startIndex j + 3 + r) - node n B j)) := by ring
    _ ≤ |node n B j - node n B 2| *
          (2 / node n B (startIndex j + 3 + r)) :=
      mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
    _ = c * (1 / node n B (startIndex j + 3 + r)) := by
      simp only [c]
      ring

/-- The limiting weight is the actual limit of the finite normalized barycentric sequence. -/
def limitWeight (n B j : ℕ) : ℝ :=
  limUnder atTop (fun K ↦ finiteWeight n B K j)

/-- `lem:limit-weights-exist`: each finite normalized barycentric coefficient converges to the
declared limiting coefficient.  The proof is the manuscript's absolutely convergent infinite
product argument. -/
theorem finiteWeight_tendsto_limitWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    Tendsto (fun K ↦ finiteWeight n B K j) atTop (nhds (limitWeight n B j)) := by
  let delta : ℕ → ℝ :=
    fun r ↦ updateFactor n B j (startIndex j + 3 + r) - 1
  have hdelta : Summable delta := summable_updateFactor_sub_one hn hB
  have hfactorpos : ∀ r, 0 < 1 + delta r := by
    intro r
    dsimp only [delta]
    have hpos := updateFactor_pos hn hB (j := j)
      (ell := startIndex j + 3 + r) (by
        have := lt_startIndex_add_three j
        omega) (by omega)
    linarith
  have hlog : Summable (fun r ↦ Real.log (1 + delta r)) :=
    Real.summable_log_one_add_of_summable hdelta
  have hprod : HasProd (fun r ↦ 1 + delta r)
      (Real.exp (∑' r, Real.log (1 + delta r))) :=
    Real.hasProd_of_hasSum_log hfactorpos hlog.hasSum
  have hpartial := hprod.tendsto_prod_nat
  have hshift : Tendsto (fun t ↦ finiteWeight n B (startIndex j + t) j) atTop
      (nhds (finiteWeight n B (startIndex j) j *
        Real.exp (∑' r, Real.log (1 + delta r)))) := by
    have hconst : Tendsto (fun _ : ℕ ↦ finiteWeight n B (startIndex j) j) atTop
        (nhds (finiteWeight n B (startIndex j) j)) := tendsto_const_nhds
    have hmul := hconst.mul hpartial
    convert hmul using 1
    funext t
    rw [finiteWeight_eq_initial_mul_prod hn hB]
    congr 1
    apply Finset.prod_congr rfl
    intro r hr
    simp only [delta]
    ring
  have hfull : Tendsto (fun K ↦ finiteWeight n B K j) atTop
      (nhds (finiteWeight n B (startIndex j) j *
        Real.exp (∑' r, Real.log (1 + delta r)))) := by
    apply (tendsto_add_atTop_iff_nat (startIndex j)).mp
    simpa only [add_comm] using hshift
  exact hfull.cauchySeq.tendsto_limUnder

/-- The `M=2` case of `lem:all-moment-weight-decay` for the actual limiting weights. -/
theorem limitWeight_decay_two {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    |limitWeight n B j| ≤ 8 * (n * B : ℝ) ^ 2 / node n B j ^ 2 := by
  exact le_of_tendsto' (finiteWeight_tendsto_limitWeight hn hB j).abs
    (fun K ↦ finiteWeight_decay_two hn hB)

/-- Pointwise limiting version of the auxiliary all-order domination bound. -/
theorem limitWeight_decay_crude {n B j M : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hM : 2 ≤ M) :
    |limitWeight n B j| ≤ crudeDecayConstant n B M / node n B j ^ M := by
  exact le_of_tendsto' (finiteWeight_tendsto_limitWeight hn hB j).abs
    (fun K ↦ finiteWeight_decay_crude hn hB hM)

/-- `lem:all-moments-signed-identity`: the limiting signed weights annihilate every
nonnegative integral power.  Tannery's theorem is the counting-measure dominated-convergence
argument written in the manuscript. -/
theorem limitWeight_signed_moment_identity {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (s : ℕ) :
    ∑' j : ℕ, limitWeight n B j * node n B j ^ s = 0 := by
  let C : ℝ := crudeDecayConstant n B (s + 2)
  let bound : ℕ → ℝ := fun j ↦ C * (1 / node n B j ^ 2)
  have hsum : Summable bound := by
    dsimp only [bound]
    exact (summable_inv_node_sq hn hB).mul_left C
  have hab : ∀ j : ℕ, Tendsto
      (fun K ↦ finiteWeight n B K j * node n B j ^ s) atTop
      (nhds (limitWeight n B j * node n B j ^ s)) := by
    intro j
    exact (finiteWeight_tendsto_limitWeight hn hB j).mul_const _
  have hbound : ∀ K j : ℕ,
      ‖finiteWeight n B K j * node n B j ^ s‖ ≤ bound j := by
    intro K j
    have hdecay := finiteWeight_decay_crude (n := n) (B := B) (K := K) (j := j)
      hn hB (M := s + 2) (by omega)
    have hxpos : 0 < node n B j := node_pos hn hB j
    have hp : node n B j ^ (s + 2) = node n B j ^ s * node n B j ^ 2 := by
      rw [pow_add]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hxpos]
    calc
      |finiteWeight n B K j| * node n B j ^ s ≤
          (C / node n B j ^ (s + 2)) * node n B j ^ s := by
        exact mul_le_mul_of_nonneg_right (by simpa only [C] using hdecay)
          (pow_nonneg hxpos.le _)
      _ = bound j := by
        dsimp only [bound]
        rw [hp]
        field_simp
  have hlim : Tendsto
      (fun K ↦ ∑' j : ℕ, finiteWeight n B K j * node n B j ^ s) atTop
      (nhds (∑' j : ℕ, limitWeight n B j * node n B j ^ s)) :=
    tendsto_tsum_of_dominated_convergence hsum hab
      (Filter.Eventually.of_forall hbound)
  have hfinite (K : ℕ) (hsK : s ≤ K + 1) :
      (∑' j : ℕ, finiteWeight n B K j * node n B j ^ s) = 0 := by
    rw [tsum_eq_sum (s := Finset.range (K + 3))]
    · rw [← Fin.sum_univ_eq_sum_range]
      exact finiteWeight_moment_zero hn hB hsK
    · intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      rw [finiteWeight_eq_zero_of_ge hj, zero_mul]
  have hzero : Tendsto
      (fun K ↦ ∑' j : ℕ, finiteWeight n B K j * node n B j ^ s) atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop s] with K hK
    exact (hfinite K (by omega)).symm
  exact tendsto_nhds_unique hlim hzero

/-- Pointwise limits retain the nonnegative even sign. -/
theorem limitWeight_nonneg_of_even {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (heven : Even j) : 0 ≤ limitWeight n B j := by
  apply ge_of_tendsto (finiteWeight_tendsto_limitWeight hn hB j)
  filter_upwards [eventually_ge_atTop (startIndex j)] with K hK
  exact (finiteWeight_pos_of_even hn hB (by
    have := lt_startIndex_add_three j
    omega) heven).le

/-- Pointwise limits retain the nonpositive odd sign. -/
theorem limitWeight_nonpos_of_odd {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hodd : Odd j) : limitWeight n B j ≤ 0 := by
  apply le_of_tendsto (finiteWeight_tendsto_limitWeight hn hB j)
  filter_upwards [eventually_ge_atTop (startIndex j)] with K hK
  exact (finiteWeight_neg_of_odd hn hB (by
    have := lt_startIndex_add_three j
    omega) hodd).le

/-- The pivot normalization survives the limit: `w₂=1`. -/
theorem limitWeight_two {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    limitWeight n B 2 = 1 := by
  apply tendsto_nhds_unique (finiteWeight_tendsto_limitWeight hn hB 2)
  simpa only [finiteWeight_two hn hB] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))

/-- Positive (even-indexed) part of the limiting signed weights. -/
def evenWeight (n B j : ℕ) : ℝ :=
  if Even j then limitWeight n B j else 0

/-- Absolute value of the negative (odd-indexed) part of the limiting signed weights. -/
def oddWeight (n B j : ℕ) : ℝ :=
  if Odd j then -limitWeight n B j else 0

@[simp] theorem evenWeight_of_even {n B j : ℕ} (hj : Even j) :
    evenWeight n B j = limitWeight n B j := by simp [evenWeight, hj]

@[simp] theorem evenWeight_of_odd {n B j : ℕ} (hj : Odd j) :
    evenWeight n B j = 0 := by
  simp [evenWeight, Nat.not_even_iff_odd.mpr hj]

@[simp] theorem oddWeight_of_odd {n B j : ℕ} (hj : Odd j) :
    oddWeight n B j = -limitWeight n B j := by simp [oddWeight, hj]

@[simp] theorem oddWeight_of_even {n B j : ℕ} (hj : Even j) :
    oddWeight n B j = 0 := by
  simp [oddWeight, Nat.not_odd_iff_even.mpr hj]

theorem evenWeight_nonneg {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    0 ≤ evenWeight n B j := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [evenWeight_of_even hj]
    exact limitWeight_nonneg_of_even hn hB hj
  · simp [evenWeight_of_odd hj]

theorem oddWeight_nonneg {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    0 ≤ oddWeight n B j := by
  rcases Nat.even_or_odd j with hj | hj
  · simp [oddWeight_of_even hj]
  · rw [oddWeight_of_odd hj]
    linarith [limitWeight_nonpos_of_odd hn hB hj]

theorem limitWeight_eq_even_sub_odd (n B j : ℕ) :
    limitWeight n B j = evenWeight n B j - oddWeight n B j := by
  rcases Nat.even_or_odd j with hj | hj
  · simp [evenWeight_of_even hj, oddWeight_of_even hj]
  · simp [evenWeight_of_odd hj, oddWeight_of_odd hj]

/-- Absolute summability, the first assertion of `cor:limit-probabilities-well-defined`. -/
theorem summable_abs_limitWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (fun j : ℕ ↦ |limitWeight n B j|) := by
  let C : ℝ := crudeDecayConstant n B 2
  have hmajor : Summable (fun j : ℕ ↦ C * (1 / node n B j ^ 2)) :=
    (summable_inv_node_sq hn hB).mul_left C
  refine hmajor.of_nonneg_of_le (fun j ↦ abs_nonneg _) (fun j ↦ ?_)
  calc
    |limitWeight n B j| ≤ C / node n B j ^ 2 := by
      simpa only [C] using limitWeight_decay_crude (n := n) (B := B) (j := j)
        hn hB (M := 2) (by omega)
    _ = C * (1 / node n B j ^ 2) := by ring

theorem summable_limitWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (limitWeight n B) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using summable_abs_limitWeight hn hB

theorem summable_evenWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (evenWeight n B) := by
  refine (summable_abs_limitWeight hn hB).of_nonneg_of_le
    (fun j ↦ evenWeight_nonneg hn hB) (fun j ↦ ?_)
  rcases Nat.even_or_odd j with hj | hj
  · rw [evenWeight_of_even hj, abs_of_nonneg (limitWeight_nonneg_of_even hn hB hj)]
  · simp [evenWeight_of_odd hj]

theorem summable_oddWeight {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Summable (oddWeight n B) := by
  refine (summable_abs_limitWeight hn hB).of_nonneg_of_le
    (fun j ↦ oddWeight_nonneg hn hB) (fun j ↦ ?_)
  rcases Nat.even_or_odd j with hj | hj
  · simp [oddWeight_of_even hj]
  · rw [oddWeight_of_odd hj, abs_of_nonpos (limitWeight_nonpos_of_odd hn hB hj)]

/-- Common positive normalization `W` from `cor:limit-probabilities-well-defined`. -/
def normalizer (n B : ℕ) : ℝ := ∑' j : ℕ, evenWeight n B j

theorem normalizer_eq_odd {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    normalizer n B = ∑' j : ℕ, oddWeight n B j := by
  have hzero := limitWeight_signed_moment_identity hn hB 0
  have hdecomp : (fun j : ℕ ↦ limitWeight n B j * node n B j ^ 0) =
      fun j ↦ evenWeight n B j - oddWeight n B j := by
    funext j
    simpa only [pow_zero, mul_one] using limitWeight_eq_even_sub_odd n B j
  rw [hdecomp, (summable_evenWeight hn hB).tsum_sub (summable_oddWeight hn hB)] at hzero
  unfold normalizer
  linarith

theorem one_le_normalizer {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (1 : ℝ) ≤ normalizer n B := by
  have hsingle := (summable_evenWeight hn hB).sum_le_tsum ({2} : Finset ℕ)
    (fun j hj ↦ evenWeight_nonneg hn hB)
  simpa [normalizer, evenWeight_of_even (show Even 2 by decide), limitWeight_two hn hB]
    using hsingle

theorem normalizer_pos {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    0 < normalizer n B := lt_of_lt_of_le zero_lt_one (one_le_normalizer hn hB)

/-- NNReal-normalized even masses. -/
def evenMassNN (n B j : ℕ) : ℝ≥0 :=
  Real.toNNReal (evenWeight n B j / normalizer n B)

/-- NNReal-normalized odd masses. -/
def oddMassNN (n B j : ℕ) : ℝ≥0 :=
  Real.toNNReal (oddWeight n B j / normalizer n B)

theorem hasSum_evenMassENNReal {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    HasSum (fun j : ℕ ↦ (evenMassNN n B j : ℝ≥0∞)) 1 := by
  have hWne : normalizer n B ≠ 0 := ne_of_gt (normalizer_pos hn hB)
  have hreal : HasSum (fun j : ℕ ↦ evenWeight n B j / normalizer n B) 1 := by
    have h := (summable_evenWeight hn hB).hasSum.div_const (normalizer n B)
    have hval : (∑' j : ℕ, evenWeight n B j) / normalizer n B = 1 := by
      change normalizer n B / normalizer n B = 1
      exact div_self hWne
    simpa only [hval] using h
  have hnn := hreal.toNNReal (fun j ↦
    div_nonneg (evenWeight_nonneg hn hB) (normalizer_pos hn hB).le)
  change HasSum (fun j : ℕ ↦
    ((Real.toNNReal (evenWeight n B j / normalizer n B) : ℝ≥0) : ℝ≥0∞)) 1
  apply ENNReal.hasSum_coe.mpr
  simpa only [Real.toNNReal_one] using hnn

theorem hasSum_oddMassENNReal {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    HasSum (fun j : ℕ ↦ (oddMassNN n B j : ℝ≥0∞)) 1 := by
  have hWne : normalizer n B ≠ 0 := ne_of_gt (normalizer_pos hn hB)
  have hreal : HasSum (fun j : ℕ ↦ oddWeight n B j / normalizer n B) 1 := by
    have h := (summable_oddWeight hn hB).hasSum.div_const (normalizer n B)
    rw [← normalizer_eq_odd hn hB] at h
    simpa only [div_self hWne] using h
  have hnn := hreal.toNNReal (fun j ↦
    div_nonneg (oddWeight_nonneg hn hB) (normalizer_pos hn hB).le)
  change HasSum (fun j : ℕ ↦
    ((Real.toNNReal (oddWeight n B j / normalizer n B) : ℝ≥0) : ℝ≥0∞)) 1
  apply ENNReal.hasSum_coe.mpr
  simpa only [Real.toNNReal_one] using hnn

/-- PMFs appearing in `cor:limit-probabilities-well-defined`. -/
def nuPMF (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) : PMF ℕ :=
  pmfOfHasSum (fun j ↦ (evenMassNN n B j : ℝ≥0∞)) (hasSum_evenMassENNReal hn hB)

def muPMF (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) : PMF ℕ :=
  pmfOfHasSum (fun j ↦ (oddMassNN n B j : ℝ≥0∞)) (hasSum_oddMassENNReal hn hB)

/-- The two canonical limiting laws. -/
def nuLaw (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) : Distribution :=
  atomicLaw (nuPMF n B hn hB) (nodeNN n B)

def muLaw (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) : Distribution :=
  atomicLaw (muPMF n B hn hB) (nodeNN n B)

theorem measurable_nodeNN (n B : ℕ) : Measurable (nodeNN n B) :=
  measurable_of_countable _

theorem nodeNN_injective {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Function.Injective (nodeNN n B) := by
  intro i j hij
  apply node_injective hn hB
  exact congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hij

@[simp] theorem nuPMF_toReal {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    ((nuPMF n B hn hB j).toReal : ℝ) = evenWeight n B j / normalizer n B := by
  simp only [nuPMF, pmfOfHasSum_apply]
  rw [ENNReal.coe_toReal]
  rw [evenMassNN, Real.coe_toNNReal _
    (div_nonneg (evenWeight_nonneg hn hB) (normalizer_pos hn hB).le)]

@[simp] theorem muPMF_toReal {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    ((muPMF n B hn hB j).toReal : ℝ) = oddWeight n B j / normalizer n B := by
  simp only [muPMF, pmfOfHasSum_apply]
  rw [ENNReal.coe_toReal]
  rw [oddMassNN, Real.coe_toNNReal _
    (div_nonneg (oddWeight_nonneg hn hB) (normalizer_pos hn hB).le)]

/-- Exact even atom formula from `cor:limit-probabilities-well-defined`. -/
theorem nuLaw_atom_even {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : Even j) :
    (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal =
      limitWeight n B j / normalizer n B := by
  have hatom := atomicLaw_toMeasure_singleton_of_injective
    (nuPMF n B hn hB) (nodeNN n B) (measurable_nodeNN n B)
    (nodeNN_injective hn hB) j
  rw [show (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}) =
      nuPMF n B hn hB j from hatom]
  rw [nuPMF_toReal, evenWeight_of_even hj]

theorem nuLaw_atom_odd {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : Odd j) :
    (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}) = 0 := by
  rw [show (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}) =
      nuPMF n B hn hB j from atomicLaw_toMeasure_singleton_of_injective
        (nuPMF n B hn hB) (nodeNN n B) (measurable_nodeNN n B)
        (nodeNN_injective hn hB) j]
  simp [nuPMF, evenMassNN, evenWeight_of_odd hj]

/-- Exact odd atom formula from `cor:limit-probabilities-well-defined`. -/
theorem muLaw_atom_odd {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : Odd j) :
    (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal =
      |limitWeight n B j| / normalizer n B := by
  have hnonpos := limitWeight_nonpos_of_odd hn hB hj
  rw [show (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}) =
      muPMF n B hn hB j from atomicLaw_toMeasure_singleton_of_injective
        (muPMF n B hn hB) (nodeNN n B) (measurable_nodeNN n B)
        (nodeNN_injective hn hB) j]
  rw [muPMF_toReal, oddWeight_of_odd hj, abs_of_nonpos hnonpos]

theorem muLaw_atom_even {n B j : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hj : Even j) :
    (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}) = 0 := by
  rw [show (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}) =
      muPMF n B hn hB j from atomicLaw_toMeasure_singleton_of_injective
        (muPMF n B hn hB) (nodeNN n B) (measurable_nodeNN n B)
        (nodeNN_injective hn hB) j]
  simp [muPMF, oddMassNN, oddWeight_of_even hj]

/-- The even support carrying `ν`. -/
def evenSupport (n B : ℕ) : Set ℝ≥0 :=
  {x | ∃ j : ℕ, Even j ∧ x = nodeNN n B j}

/-- The odd support carrying `μ`. -/
def oddSupport (n B : ℕ) : Set ℝ≥0 :=
  {x | ∃ j : ℕ, Odd j ∧ x = nodeNN n B j}

theorem evenSupport_disjoint_oddSupport {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Disjoint (evenSupport n B) (oddSupport n B) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, hi, rfl⟩ ⟨j, hj, heq⟩
  have hij : i = j := by
    apply (node_strictMono hn hB).injective
    exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) heq
  subst j
  exact (Nat.not_even_iff_odd.mpr hj) hi

theorem nuLaw_support {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) (evenSupport n B)) = 1 := by
  have hfull := atomicLaw_toMeasure_image_support (nuPMF n B hn hB) (nodeNN n B)
  have hsubset : nodeNN n B '' (nuPMF n B hn hB).support ⊆ evenSupport n B := by
    rintro x ⟨j, hj, rfl⟩
    rw [PMF.mem_support_iff] at hj
    rcases Nat.even_or_odd j with heven | hodd
    · exact ⟨j, heven, rfl⟩
    · exfalso
      apply hj
      simp [nuPMF, evenMassNN, evenWeight_of_odd hodd]
  have hle : (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) (evenSupport n B)) ≤ 1 := by
    calc
      _ ≤ (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) Set.univ) :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  apply le_antisymm hle
  calc
    (1 : ℝ≥0∞) =
        (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0)
          (nodeNN n B '' (nuPMF n B hn hB).support)) := hfull.symm
    _ ≤ (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) (evenSupport n B)) :=
      MeasureTheory.measure_mono hsubset

theorem muLaw_support {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) (oddSupport n B)) = 1 := by
  have hfull := atomicLaw_toMeasure_image_support (muPMF n B hn hB) (nodeNN n B)
  have hsubset : nodeNN n B '' (muPMF n B hn hB).support ⊆ oddSupport n B := by
    rintro x ⟨j, hj, rfl⟩
    rw [PMF.mem_support_iff] at hj
    rcases Nat.even_or_odd j with heven | hodd
    · exfalso
      apply hj
      simp [muPMF, oddMassNN, oddWeight_of_even heven]
    · exact ⟨j, hodd, rfl⟩
  have hle : (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) (oddSupport n B)) ≤ 1 := by
    calc
      _ ≤ (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) Set.univ) :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  apply le_antisymm hle
  calc
    (1 : ℝ≥0∞) =
        (((muLaw n B hn hB : Distribution) : Measure ℝ≥0)
          (nodeNN n B '' (muPMF n B hn hB).support)) := hfull.symm
    _ ≤ (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) (oddSupport n B)) :=
      MeasureTheory.measure_mono hsubset

/-- Absolute convergence at every moment order, as required by `lem:all-moments-limit`. -/
theorem summable_abs_limitWeight_mul_node_pow {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (s : ℕ) :
    Summable (fun j : ℕ ↦ |limitWeight n B j| * node n B j ^ s) := by
  let C : ℝ := crudeDecayConstant n B (s + 2)
  have hmajor : Summable (fun j : ℕ ↦ C * (1 / node n B j ^ 2)) :=
    (summable_inv_node_sq hn hB).mul_left C
  refine hmajor.of_nonneg_of_le
    (fun j ↦ mul_nonneg (abs_nonneg _) (pow_nonneg (node_pos hn hB j).le _)) (fun j ↦ ?_)
  have hdecay := limitWeight_decay_crude (n := n) (B := B) (j := j)
    hn hB (M := s + 2) (by omega)
  have hp : node n B j ^ (s + 2) = node n B j ^ s * node n B j ^ 2 := by
    rw [pow_add]
  calc
    |limitWeight n B j| * node n B j ^ s ≤
        (C / node n B j ^ (s + 2)) * node n B j ^ s := by
      exact mul_le_mul_of_nonneg_right (by simpa only [C] using hdecay)
        (pow_nonneg (node_pos hn hB j).le _)
    _ = C * (1 / node n B j ^ 2) := by
      rw [hp]
      field_simp [ne_of_gt (node_pos hn hB j)]

theorem summable_evenWeight_mul_node_pow {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (s : ℕ) : Summable (fun j : ℕ ↦ evenWeight n B j * node n B j ^ s) := by
  refine (summable_abs_limitWeight_mul_node_pow hn hB s).of_nonneg_of_le
    (fun j ↦ mul_nonneg (evenWeight_nonneg hn hB) (pow_nonneg (node_pos hn hB j).le _))
    (fun j ↦ ?_)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (node_pos hn hB j).le _)
  rcases Nat.even_or_odd j with hj | hj
  · rw [evenWeight_of_even hj, abs_of_nonneg (limitWeight_nonneg_of_even hn hB hj)]
  · simp [evenWeight_of_odd hj]

theorem summable_oddWeight_mul_node_pow {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (s : ℕ) : Summable (fun j : ℕ ↦ oddWeight n B j * node n B j ^ s) := by
  refine (summable_abs_limitWeight_mul_node_pow hn hB s).of_nonneg_of_le
    (fun j ↦ mul_nonneg (oddWeight_nonneg hn hB) (pow_nonneg (node_pos hn hB j).le _))
    (fun j ↦ ?_)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (node_pos hn hB j).le _)
  rcases Nat.even_or_odd j with hj | hj
  · simp [oddWeight_of_even hj]
  · rw [oddWeight_of_odd hj, abs_of_nonpos (limitWeight_nonpos_of_odd hn hB hj)]

/-- Equality of the unnormalized positive and negative moments. -/
theorem even_tsum_mul_node_pow_eq_odd {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (s : ℕ) :
    (∑' j : ℕ, evenWeight n B j * node n B j ^ s) =
      ∑' j : ℕ, oddWeight n B j * node n B j ^ s := by
  have hzero := limitWeight_signed_moment_identity hn hB s
  have hfun : (fun j : ℕ ↦ limitWeight n B j * node n B j ^ s) =
      fun j ↦ evenWeight n B j * node n B j ^ s -
        oddWeight n B j * node n B j ^ s := by
    funext j
    rw [limitWeight_eq_even_sub_odd]
    ring
  rw [hfun, (summable_evenWeight_mul_node_pow hn hB s).tsum_sub
    (summable_oddWeight_mul_node_pow hn hB s)] at hzero
  linarith

theorem summable_nuPMF_moment {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    Summable (fun j : ℕ ↦ (nuPMF n B hn hB j).toReal * node n B j ^ s) := by
  have h := (summable_evenWeight_mul_node_pow hn hB s).mul_left
    (1 / normalizer n B)
  apply h.congr
  intro j
  rw [nuPMF_toReal]
  ring

theorem summable_muPMF_moment {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    Summable (fun j : ℕ ↦ (muPMF n B hn hB j).toReal * node n B j ^ s) := by
  have h := (summable_oddWeight_mul_node_pow hn hB s).mul_left
    (1 / normalizer n B)
  apply h.congr
  intro j
  rw [muPMF_toReal]
  ring

/-- Countable PMF integrability criterion, proved from the explicit sum-of-Dirac
representation. -/
theorem integrable_pmf_real_of_summable (p : PMF ℕ) (f : ℕ → ℝ)
    (h : Summable (fun j : ℕ ↦ (p j).toReal * |f j|)) :
    Integrable f p.toMeasure := by
  have hmeasure : p.toMeasure = Measure.sum (fun j : ℕ ↦ p j • Measure.dirac j) := by
    ext s hs
    rw [PMF.toMeasure_apply_eq_tsum, Measure.sum_apply _ hs]
    apply tsum_congr
    intro j
    simp [Measure.smul_apply, hs, Set.indicator]
  rw [hmeasure]
  apply MeasureTheory.integrable_sum_dirac (fun j ↦ p.apply_ne_top j)
  simpa only [Real.norm_eq_abs] using h

theorem integrable_nuPMF_moment {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    Integrable (fun j : ℕ ↦ node n B j ^ s) (nuPMF n B hn hB).toMeasure := by
  apply integrable_pmf_real_of_summable
  simpa only [abs_pow, abs_of_pos (node_pos hn hB _)] using summable_nuPMF_moment hn hB s

theorem integrable_muPMF_moment {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    Integrable (fun j : ℕ ↦ node n B j ^ s) (muPMF n B hn hB).toMeasure := by
  apply integrable_pmf_real_of_summable
  simpa only [abs_pow, abs_of_pos (node_pos hn hB _)] using summable_muPMF_moment hn hB s

theorem hasFiniteMoments_nuLaw {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    HasFiniteMoments (nuLaw n B hn hB) := by
  intro s
  have hf : StronglyMeasurable (momentIntegrand s) := by
    unfold momentIntegrand
    fun_prop
  unfold HasFiniteMoment
  rw [nuLaw, coe_atomicLaw, ← PMF.toMeasure_map (nodeNN n B) (nuPMF n B hn hB)
    (measurable_nodeNN n B)]
  apply (integrable_map_measure hf.aestronglyMeasurable
    (measurable_nodeNN n B).aemeasurable).2
  change Integrable (fun j : ℕ ↦ node n B j ^ s) (nuPMF n B hn hB).toMeasure
  exact integrable_nuPMF_moment hn hB s

theorem hasFiniteMoments_muLaw {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    HasFiniteMoments (muLaw n B hn hB) := by
  intro s
  have hf : StronglyMeasurable (momentIntegrand s) := by
    unfold momentIntegrand
    fun_prop
  unfold HasFiniteMoment
  rw [muLaw, coe_atomicLaw, ← PMF.toMeasure_map (nodeNN n B) (muPMF n B hn hB)
    (measurable_nodeNN n B)]
  apply (integrable_map_measure hf.aestronglyMeasurable
    (measurable_nodeNN n B).aemeasurable).2
  change Integrable (fun j : ℕ ↦ node n B j ^ s) (muPMF n B hn hB).toMeasure
  exact integrable_muPMF_moment hn hB s

theorem moment_nuLaw_eq_tsum {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    moment (nuLaw n B hn hB) s =
      ∑' j : ℕ, (evenWeight n B j / normalizer n B) * node n B j ^ s := by
  have h := moment_atomicLaw_eq_tsum (nuPMF n B hn hB) (nodeNN n B)
    (measurable_nodeNN n B) s (by
      simpa only [node] using integrable_nuPMF_moment hn hB s)
  simpa only [nuLaw, nuPMF_toReal, node] using h

theorem moment_muLaw_eq_tsum {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    moment (muLaw n B hn hB) s =
      ∑' j : ℕ, (oddWeight n B j / normalizer n B) * node n B j ^ s := by
  have h := moment_atomicLaw_eq_tsum (muPMF n B hn hB) (nodeNN n B)
    (measurable_nodeNN n B) s (by
      simpa only [node] using integrable_muPMF_moment hn hB s)
  simpa only [muLaw, muPMF_toReal, node] using h

/-- `lem:all-moments-limit`: the two normalized limiting laws have every moment finite and
equal. -/
theorem moment_muLaw_eq_nuLaw {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    moment (muLaw n B hn hB) s = moment (nuLaw n B hn hB) s := by
  rw [moment_muLaw_eq_tsum hn hB, moment_nuLaw_eq_tsum hn hB]
  have heq := even_tsum_mul_node_pow_eq_odd hn hB s
  calc
    (∑' j : ℕ, oddWeight n B j / normalizer n B * node n B j ^ s) =
        ∑' j : ℕ, (oddWeight n B j * node n B j ^ s) / normalizer n B := by
      apply tsum_congr
      intro j
      ring
    _ = (∑' j : ℕ, oddWeight n B j * node n B j ^ s) / normalizer n B :=
      tsum_div_const
    _ = (∑' j : ℕ, evenWeight n B j * node n B j ^ s) / normalizer n B := by
      rw [heq]
    _ = ∑' j : ℕ, (evenWeight n B j * node n B j ^ s) / normalizer n B :=
      tsum_div_const.symm
    _ = ∑' j : ℕ, evenWeight n B j / normalizer n B * node n B j ^ s := by
      apply tsum_congr
      intro j
      ring

theorem momentEquivalent_muLaw_nuLaw {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    MomentEquivalent (muLaw n B hn hB) (nuLaw n B hn hB) := by
  refine ⟨hasFiniteMoments_muLaw hn hB, hasFiniteMoments_nuLaw hn hB, ?_⟩
  funext s
  exact moment_muLaw_eq_nuLaw hn hB s

/-- Elementary finite-product inequality used for the explicit lower bound on `|w₁|`. -/
theorem one_sub_sum_le_prod_range (a : ℕ → ℝ) (ha0 : ∀ r, 0 ≤ a r)
    (ha1 : ∀ r, a r ≤ 1) (K : ℕ) :
    1 - ∑ r ∈ Finset.range K, a r ≤ ∏ r ∈ Finset.range K, (1 - a r) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      have hsum0 : 0 ≤ ∑ r ∈ Finset.range K, a r :=
        Finset.sum_nonneg fun r hr ↦ ha0 r
      have hfac0 : 0 ≤ 1 - a K := sub_nonneg.mpr (ha1 K)
      calc
        1 - ((∑ r ∈ Finset.range K, a r) + a K) ≤
            (1 - ∑ r ∈ Finset.range K, a r) * (1 - a K) := by
          nlinarith [mul_nonneg hsum0 (ha0 K)]
        _ ≤ (∏ r ∈ Finset.range K, (1 - a r)) * (1 - a K) :=
          mul_le_mul_of_nonneg_right ih hfac0

/-- The loss `a_ell` in the manuscript's product formula for `|w₁|`. -/
def oneLoss (n B r : ℕ) : ℝ :=
  (node n B 2 - node n B 1) / (node n B (3 + r) - node n B 1)

theorem oneLoss_nonneg {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (r : ℕ) :
    0 ≤ oneLoss n B r := by
  exact (div_pos
    (sub_pos.mpr (node_strictMono hn hB (by omega)))
    (sub_pos.mpr (node_strictMono hn hB (by omega)))).le

theorem oneLoss_le_one {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (r : ℕ) :
    oneLoss n B r ≤ 1 := by
  apply (div_le_one₀ (sub_pos.mpr (node_strictMono hn hB (by omega)))).2
  have hmono := (node_strictMono hn hB).monotone (show 2 ≤ 3 + r by omega)
  linarith

theorem updateFactor_one_eq_one_sub_oneLoss {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (r : ℕ) : updateFactor n B 1 (3 + r) = 1 - oneLoss n B r := by
  have hden : node n B (3 + r) - node n B 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (node_strictMono hn hB (by omega)))
  simp only [updateFactor, oneLoss]
  field_simp
  ring

theorem oneLoss_le_two_mul_inv {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (r : ℕ) :
    oneLoss n B r ≤ 2 * node n B 2 / node n B (3 + r) := by
  have hdouble : 2 * node n B 1 ≤ node n B (3 + r) := by
    calc
      2 * node n B 1 ≤ 2 * node n B 2 := by
        gcongr
        exact (node_strictMono hn hB).monotone (by omega)
      _ ≤ node n B 3 := node_succ_ge_two_mul hn hB (by omega)
      _ ≤ node n B (3 + r) := (node_strictMono hn hB).monotone (by omega)
  have hhalf : node n B (3 + r) / 2 ≤ node n B (3 + r) - node n B 1 := by
    linarith
  have hnum : node n B 2 - node n B 1 ≤ node n B 2 := by
    linarith [node_pos hn hB 1]
  have hdenpos : 0 < node n B (3 + r) - node n B 1 :=
    sub_pos.mpr (node_strictMono hn hB (by omega))
  calc
    oneLoss n B r ≤ node n B 2 / (node n B (3 + r) / 2) := by
      exact div_le_div₀ (node_pos hn hB 2).le hnum
        (div_pos (node_pos hn hB (3 + r)) (by norm_num)) hhalf
    _ = 2 * node n B 2 / node n B (3 + r) := by field_simp

theorem sum_oneLoss_le {n B K : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∑ r ∈ Finset.range K, oneLoss n B r) ≤ 4 / node n B 2 ^ 2 := by
  calc
    (∑ r ∈ Finset.range K, oneLoss n B r) ≤
        ∑ r ∈ Finset.range K, 2 * node n B 2 / node n B (3 + r) :=
      Finset.sum_le_sum fun r hr ↦ oneLoss_le_two_mul_inv hn hB r
    _ = 2 * node n B 2 *
        (∑ r ∈ Finset.range K, 1 / node n B (3 + r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ 2 * node n B 2 * (2 / node n B 3) := by
      exact mul_le_mul_of_nonneg_left
        (sum_inv_node_tail_le (q := 3) (t := K) hn hB (by omega))
        (mul_nonneg (by norm_num) (node_pos hn hB 2).le)
    _ ≤ 4 / node n B 2 ^ 2 := by
      rw [node_succ_eq_pow 2 (by omega)]
      have hx : 1 ≤ node n B 2 := (one_lt_node_two hn hB).le
      have hpow : node n B 2 ^ 3 ≤ node n B 2 ^ B :=
        pow_le_pow_right₀ hx hB
      have hinv := one_div_le_one_div_of_le (pow_pos (node_pos hn hB 2) 3) hpow
      have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 4 * node n B 2)
      calc
        2 * node n B 2 * (2 / node n B 2 ^ B) =
            (4 * node n B 2) * (1 / node n B 2 ^ B) := by ring
        _ ≤ (4 * node n B 2) * (1 / node n B 2 ^ 3) := hmul
        _ = 4 / node n B 2 ^ 2 := by field_simp <;> ring

theorem n_le_abs_finiteWeight_one {n B K : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (n : ℝ) ≤ |finiteWeight n B K 1| := by
  have hprod : 1 - 4 / node n B 2 ^ 2 ≤
      ∏ r ∈ Finset.range K, updateFactor n B 1 (3 + r) := by
    calc
      1 - 4 / node n B 2 ^ 2 ≤ 1 - ∑ r ∈ Finset.range K, oneLoss n B r := by
        linarith [sum_oneLoss_le (n := n) (B := B) (K := K) hn hB]
      _ ≤ ∏ r ∈ Finset.range K, (1 - oneLoss n B r) :=
        one_sub_sum_le_prod_range (oneLoss n B)
          (oneLoss_nonneg hn hB) (oneLoss_le_one hn hB) K
      _ = ∏ r ∈ Finset.range K, updateFactor n B 1 (3 + r) := by
        apply Finset.prod_congr rfl
        intro r hr
        rw [updateFactor_one_eq_one_sub_oneLoss hn hB]
  have hcoefpos : 0 < (node n B 2 - node n B 0) / (node n B 1 - node n B 0) :=
    div_pos (sub_pos.mpr (node_strictMono hn hB (by omega)))
      (sub_pos.mpr (node_strictMono hn hB (by omega)))
  have hcoef : (n : ℝ) ≤
      ((node n B 2 - node n B 0) / (node n B 1 - node n B 0)) *
        (1 - 4 / node n B 2 ^ 2) := by
    simp only [node_zero, node_one, node_two]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
    have hx : (9 : ℝ) ≤ n * B := by nlinarith
    have hxpos : (0 : ℝ) < n * B := by positivity
    have hden : (0 : ℝ) < B - 1 := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    have hone : 1 - 4 / (n * B : ℝ) ^ 2 =
        ((n * B : ℝ) ^ 2 - 4) / (n * B : ℝ) ^ 2 := by
      field_simp
    rw [hone, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hxpos)]
    have hsquare : 4 * ((n : ℝ) * (B : ℝ) - 1) ≤
        ((n : ℝ) - 1) * ((n : ℝ) * (B : ℝ)) ^ 2 := by
      have htwo : (2 : ℝ) ≤ n - 1 := by linarith
      have hquad : 2 * ((n : ℝ) * (B : ℝ)) ≤ ((n : ℝ) * (B : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) * (B : ℝ) - 1)]
      have hfour : 4 * ((n : ℝ) * (B : ℝ)) ≤
          2 * ((n : ℝ) * (B : ℝ)) ^ 2 := by linarith
      have hcoefmono : 2 * ((n : ℝ) * (B : ℝ)) ^ 2 ≤
          ((n : ℝ) - 1) * ((n : ℝ) * (B : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right htwo (sq_nonneg _)
      linarith
    nlinarith
  have hformula := abs_finiteWeight_eq_initial_mul_prod (n := n) (B := B)
    (K := K) (j := 1) hn hB (by simp [startIndex_eq])
  simp only [startIndex_eq, Nat.reduceSub, Nat.zero_add, Nat.sub_zero] at hformula
  rw [finiteWeight_one_base hn hB, abs_neg,
    abs_of_pos hcoefpos] at hformula
  calc
    (n : ℝ) ≤ ((node n B 2 - node n B 0) / (node n B 1 - node n B 0)) *
        (1 - 4 / node n B 2 ^ 2) := hcoef
    _ ≤ ((node n B 2 - node n B 0) / (node n B 1 - node n B 0)) *
        (∏ r ∈ Finset.range K, updateFactor n B 1 (3 + r)) :=
      mul_le_mul_of_nonneg_left hprod hcoefpos.le
    _ = |finiteWeight n B K 1| := hformula.symm

theorem n_le_abs_limitWeight_one {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (n : ℝ) ≤ |limitWeight n B 1| := by
  apply ge_of_tendsto (finiteWeight_tendsto_limitWeight hn hB 1).abs
  exact Filter.Eventually.of_forall fun K ↦ n_le_abs_finiteWeight_one hn hB

theorem n_le_normalizer {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (n : ℝ) ≤ normalizer n B := by
  rw [normalizer_eq_odd hn hB]
  have hsingle := (summable_oddWeight hn hB).sum_le_tsum ({1} : Finset ℕ)
    (fun j hj ↦ oddWeight_nonneg hn hB)
  simp only [Finset.sum_singleton] at hsingle
  have hodd : Odd 1 := odd_one
  rw [oddWeight_of_odd hodd, ← abs_of_nonpos (limitWeight_nonpos_of_odd hn hB hodd)] at hsingle
  simpa using (n_le_abs_limitWeight_one hn hB).trans hsingle

theorem sum_inv_node_sq_tail_le {n B q K : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hq : 2 ≤ q) :
    (∑ r ∈ Finset.range K, 1 / node n B (q + r) ^ 2) ≤ 2 / node n B q ^ 2 := by
  calc
    (∑ r ∈ Finset.range K, 1 / node n B (q + r) ^ 2) ≤
        ∑ r ∈ Finset.range K,
          (1 / node n B q) * (1 / node n B (q + r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hmono : node n B q ≤ node n B (q + r) :=
        (node_strictMono hn hB).monotone (by omega)
      have hinv : 1 / node n B (q + r) ≤ 1 / node n B q :=
        one_div_le_one_div_of_le (node_pos hn hB q) hmono
      calc
        1 / node n B (q + r) ^ 2 =
            (1 / node n B (q + r)) * (1 / node n B (q + r)) := by ring
        _ ≤ (1 / node n B q) * (1 / node n B (q + r)) :=
          mul_le_mul_of_nonneg_right hinv (one_div_nonneg.mpr (node_pos hn hB _).le)
    _ = (1 / node n B q) *
        (∑ r ∈ Finset.range K, 1 / node n B (q + r)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / node n B q) * (2 / node n B q) := by
      exact mul_le_mul_of_nonneg_left (sum_inv_node_tail_le hn hB hq)
        (one_div_nonneg.mpr (node_pos hn hB q).le)
    _ = 2 / node n B q ^ 2 := by field_simp

theorem tsum_inv_node_sq_tail_le {n B q : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B)
    (hq : 2 ≤ q) :
    (∑' r : ℕ, 1 / node n B (q + r) ^ 2) ≤ 2 / node n B q ^ 2 := by
  have hsum : Summable (fun r : ℕ ↦ 1 / node n B (q + r) ^ 2) := by
    have h := (summable_inv_node_sq hn hB).comp_injective (add_right_injective q)
    simpa only [Function.comp_def] using h
  apply le_of_tendsto hsum.tendsto_sum_tsum_nat
  exact Filter.Eventually.of_forall fun K ↦ sum_inv_node_sq_tail_le hn hB hq

theorem abs_limitWeight_zero_le {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    |limitWeight n B 0| ≤ 2 * n := by
  apply le_of_tendsto (finiteWeight_tendsto_limitWeight hn hB 0).abs
  exact Filter.Eventually.of_forall fun K ↦ abs_finiteWeight_zero_le hn hB K

theorem parityTail_le {n B q : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) (hq : 3 ≤ q)
    (part : ℕ → ℝ) (hpart : ∀ j, 0 ≤ part j)
    (hle : ∀ j, part j ≤ |limitWeight n B j|) :
    (∑' r : ℕ, part (q + r)) ≤ 16 * (n * B : ℝ) ^ 2 / node n B q ^ 2 := by
  have hleft : Summable (fun r : ℕ ↦ part (q + r)) := by
    have habs : Summable (fun r : ℕ ↦ |limitWeight n B (q + r)|) :=
      (summable_abs_limitWeight hn hB).comp_injective (add_right_injective q)
    exact habs.of_nonneg_of_le (fun r ↦ hpart _) (fun r ↦ hle _)
  have hright : Summable (fun r : ℕ ↦
      8 * (n * B : ℝ) ^ 2 * (1 / node n B (q + r) ^ 2)) :=
    ((summable_inv_node_sq hn hB).comp_injective (add_right_injective q)).mul_left _
  calc
    (∑' r : ℕ, part (q + r)) ≤
        ∑' r : ℕ, 8 * (n * B : ℝ) ^ 2 * (1 / node n B (q + r) ^ 2) := by
      exact hleft.tsum_le_tsum (fun r ↦ by
        calc
          part (q + r) ≤ |limitWeight n B (q + r)| := hle _
          _ ≤ 8 * (n * B : ℝ) ^ 2 / node n B (q + r) ^ 2 :=
            limitWeight_decay_two hn hB
          _ = 8 * (n * B : ℝ) ^ 2 * (1 / node n B (q + r) ^ 2) := by ring)
        hright
    _ = 8 * (n * B : ℝ) ^ 2 *
        (∑' r : ℕ, 1 / node n B (q + r) ^ 2) := tsum_mul_left
    _ ≤ 8 * (n * B : ℝ) ^ 2 * (2 / node n B q ^ 2) := by
      exact mul_le_mul_of_nonneg_left (tsum_inv_node_sq_tail_le hn hB (by omega))
        (by positivity)
    _ = 16 * (n * B : ℝ) ^ 2 / node n B q ^ 2 := by ring

theorem evenTail_four_le_one {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∑' r : ℕ, evenWeight n B (4 + r)) ≤ 1 := by
  have htail := parityTail_le hn hB (q := 4) (by omega) (evenWeight n B)
    (fun j ↦ evenWeight_nonneg hn hB) (fun j ↦ by
      rcases Nat.even_or_odd j with hj | hj
      · rw [evenWeight_of_even hj, abs_of_nonneg (limitWeight_nonneg_of_even hn hB hj)]
      · simp [evenWeight_of_odd hj])
  have hnode : 4 * node n B 2 ≤ node n B 4 := by
    have h := node_ge_geometric_from (q := 2) hn hB (by omega) 2
    norm_num at h
    simpa [mul_comm] using h
  have hsquare : 16 * node n B 2 ^ 2 ≤ node n B 4 ^ 2 := by
    have hnonneg : 0 ≤ 4 * node n B 2 :=
      mul_nonneg (by norm_num) (node_pos hn hB 2).le
    have h := pow_le_pow_left₀ hnonneg hnode 2
    nlinarith
  have hconst : 16 * (n * B : ℝ) ^ 2 / node n B 4 ^ 2 ≤ 1 := by
    rw [div_le_one₀ (sq_pos_of_pos (node_pos hn hB 4)), ← node_two]
    exact hsquare
  exact htail.trans hconst

theorem normalizer_le_four_mul_n {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    normalizer n B ≤ 4 * n := by
  have hsplit := (summable_evenWeight hn hB).sum_add_tsum_nat_add 4
  have hsum4 :
      (∑ x ∈ Finset.range 4, evenWeight n B x) = limitWeight n B 0 + 1 := by
    norm_num [Finset.sum_range_succ, evenWeight, limitWeight_two hn hB]
  have htailEq :
      (∑' i : ℕ, evenWeight n B (i + 4)) =
        ∑' r : ℕ, evenWeight n B (4 + r) := by
    apply tsum_congr
    intro r
    rw [add_comm]
  have hW : normalizer n B =
      limitWeight n B 0 + 1 + ∑' r : ℕ, evenWeight n B (4 + r) := by
    unfold normalizer
    rw [← hsplit, hsum4, htailEq]
  have h0nonneg := limitWeight_nonneg_of_even hn hB Even.zero
  have h0le : limitWeight n B 0 ≤ 2 * n := by
    rw [← abs_of_nonneg h0nonneg]
    exact abs_limitWeight_zero_le hn hB
  have htail := evenTail_four_le_one hn hB
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hW]
  nlinarith

/-- The even normalization split used for the `p₀` estimate in
`prop:key-prop-1_extended`. -/
theorem normalizer_eq_weight_zero_add_evenTail {n B : ℕ} (hn : 3 ≤ n)
    (hB : 3 ≤ B) :
    normalizer n B =
      limitWeight n B 0 + 1 + ∑' r : ℕ, evenWeight n B (4 + r) := by
  have hsplit := (summable_evenWeight hn hB).sum_add_tsum_nat_add 4
  have hsum4 :
      (∑ x ∈ Finset.range 4, evenWeight n B x) = limitWeight n B 0 + 1 := by
    norm_num [Finset.sum_range_succ, evenWeight, limitWeight_two hn hB]
  have htailEq :
      (∑' i : ℕ, evenWeight n B (i + 4)) =
        ∑' r : ℕ, evenWeight n B (4 + r) := by
    apply tsum_congr
    intro r
    rw [add_comm]
  unfold normalizer
  rw [← hsplit, hsum4, htailEq]

/-- The odd normalization split used for the `q₁` estimate in
`prop:key-prop-1_extended`. -/
theorem normalizer_eq_oddWeight_one_add_oddTail {n B : ℕ} (hn : 3 ≤ n)
    (hB : 3 ≤ B) :
    normalizer n B = oddWeight n B 1 + ∑' r : ℕ, oddWeight n B (3 + r) := by
  have hsplit := (summable_oddWeight hn hB).sum_add_tsum_nat_add 3
  have hsum3 :
      (∑ x ∈ Finset.range 3, oddWeight n B x) = oddWeight n B 1 := by
    norm_num [Finset.sum_range_succ, oddWeight]
  have htailEq :
      (∑' i : ℕ, oddWeight n B (i + 3)) =
        ∑' r : ℕ, oddWeight n B (3 + r) := by
    apply tsum_congr
    intro r
    rw [add_comm]
  rw [normalizer_eq_odd hn hB, ← hsplit, hsum3, htailEq]

/-- The odd tail after the principal atom is at most `1/(n²B²)`; this is the
quantitative tail estimate behind `q₁ ≥ 1-1/(n²B²)` in
`prop:key-prop-1_extended`. -/
theorem oddTail_three_le_inv_sq {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    (∑' r : ℕ, oddWeight n B (3 + r)) ≤
      1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) := by
  have htail := parityTail_le hn hB (q := 3) (by omega) (oddWeight n B)
    (fun j ↦ oddWeight_nonneg hn hB) (fun j ↦ by
      rcases Nat.even_or_odd j with hj | hj
      · simp [oddWeight_of_even hj]
      · rw [oddWeight_of_odd hj,
          abs_of_nonpos (limitWeight_nonpos_of_odd hn hB hj)])
  let x : ℝ := (n : ℝ) * (B : ℝ)
  have hx : 4 ≤ x := by
    dsimp [x]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
    nlinarith
  have hxone : 1 ≤ x := by linarith
  have hnode : 4 * x ^ 2 ≤ node n B 3 := by
    calc
      4 * x ^ 2 ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
      _ = x ^ 3 := by ring
      _ ≤ x ^ B := pow_le_pow_right₀ hxone hB
      _ = node n B 3 := by simp [x, node_three]
  have hsquare : (4 * x ^ 2) ^ 2 ≤ node n B 3 ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) (sq_nonneg x)) hnode 2
  have hconst :
      16 * (n * B : ℝ) ^ 2 / node n B 3 ^ 2 ≤
        1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) := by
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    rw [div_le_div_iff₀ (sq_pos_of_pos (node_pos hn hB 3))
      (mul_pos (sq_pos_of_pos (by exact_mod_cast (show 0 < n by omega)))
        (sq_pos_of_pos (by exact_mod_cast (show 0 < B by omega))))]
    dsimp [x] at hsquare ⊢
    nlinarith
  exact htail.trans hconst

/-- The atom `p₀` has the exact lower bound asserted in
`prop:key-prop-1_extended`. -/
theorem nuLaw_atom_zero_lower {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    1 - 2 / (n : ℝ) ≤
      (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B 0}).toReal := by
  rw [nuLaw_atom_even hn hB Even.zero]
  have hWpos := normalizer_pos hn hB
  rw [le_div_iff₀ hWpos]
  have hsplit := normalizer_eq_weight_zero_add_evenTail hn hB
  have htail := evenTail_four_le_one hn hB
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 2 ≤ 2 * normalizer n B / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    nlinarith [n_le_normalizer hn hB]
  calc
    (1 - 2 / (n : ℝ)) * normalizer n B =
        normalizer n B - 2 * normalizer n B / (n : ℝ) := by ring
    _ ≤ normalizer n B - 2 := sub_le_sub_left hscale _
    _ ≤ limitWeight n B 0 := by nlinarith

/-- The atom `q₁` has the exact lower bound asserted in
`prop:key-prop-1_extended`. -/
theorem muLaw_atom_one_lower {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤
      (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B 1}).toReal := by
  rw [muLaw_atom_odd hn hB odd_one]
  have hodd : Odd 1 := odd_one
  have hweight : |limitWeight n B 1| = oddWeight n B 1 := by
    rw [oddWeight_of_odd hodd, abs_of_nonpos (limitWeight_nonpos_of_odd hn hB hodd)]
  rw [hweight]
  have hWpos := normalizer_pos hn hB
  rw [le_div_iff₀ hWpos]
  let delta : ℝ := 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2)
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have htail := oddTail_three_le_inv_sq hn hB
  have htailW :
      (∑' r : ℕ, oddWeight n B (3 + r)) ≤ delta * normalizer n B := by
    calc
      (∑' r : ℕ, oddWeight n B (3 + r)) ≤ delta := by simpa [delta] using htail
      _ = delta * 1 := by ring
      _ ≤ delta * normalizer n B :=
        mul_le_mul_of_nonneg_left (one_le_normalizer hn hB) hdelta
  have hsplit := normalizer_eq_oddWeight_one_add_oddTail hn hB
  dsimp [delta] at htailW ⊢
  nlinarith

/-- The pivot atom `p₂` has the exact lower bound asserted in
`prop:key-prop-1_extended`. -/
theorem nuLaw_atom_two_lower {n B : ℕ} (hn : 3 ≤ n) (hB : 3 ≤ B) :
    1 / (4 * (n : ℝ)) ≤
      (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B 2}).toReal := by
  rw [nuLaw_atom_even hn hB (show Even 2 by decide), limitWeight_two hn hB]
  exact one_div_le_one_div_of_le (normalizer_pos hn hB)
    (normalizer_le_four_mul_n hn hB)

/-- Packaged conclusion of `prop:key-prop-1_extended`.  Keeping the witnesses in a structure
makes every later application use the same canonical measures and normalization. -/
structure Data (n B : ℕ) where
  weights : ℕ → ℝ
  normalizer : ℝ
  nu : Distribution
  mu : Distribution
  normalizer_pos : 0 < normalizer
  weight_eq_limit : weights = limitWeight n B
  even_weight_nonneg : ∀ j, Even j → 0 ≤ weights j
  odd_weight_nonpos : ∀ j, Odd j → weights j ≤ 0
  nu_atom_even : ∀ j, Even j →
    ((nu : Measure ℝ≥0) {nodeNN n B j}).toReal = weights j / normalizer
  nu_atom_odd : ∀ j, Odd j → ((nu : Measure ℝ≥0) {nodeNN n B j}) = 0
  mu_atom_odd : ∀ j, Odd j →
    ((mu : Measure ℝ≥0) {nodeNN n B j}).toReal = |weights j| / normalizer
  mu_atom_even : ∀ j, Even j → ((mu : Measure ℝ≥0) {nodeNN n B j}) = 0
  nu_support : ((nu : Measure ℝ≥0) (evenSupport n B)) = 1
  mu_support : ((mu : Measure ℝ≥0) (oddSupport n B)) = 1
  momentEquivalent : MomentEquivalent mu nu
  normalizer_ge : (n : ℝ) ≤ normalizer
  p0_ge : 1 - 2 / (n : ℝ) ≤ ((nu : Measure ℝ≥0) {nodeNN n B 0}).toReal
  q1_ge : 1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤
    ((mu : Measure ℝ≥0) {nodeNN n B 1}).toReal
  p2_ge : 1 / (4 * (n : ℝ)) ≤ ((nu : Measure ℝ≥0) {nodeNN n B 2}).toReal
  weight_decay_two : ∀ j,
    |weights j| ≤ 8 * (n * B : ℝ) ^ 2 / node n B j ^ 2

/-- The canonical pair of probability measures constructed in
`prop:key-prop-1_extended`.  The structure fields are exactly the simultaneous
conclusions of that proposition; packaging them prevents later applications from
silently choosing different witnesses for its individual conclusions. -/
noncomputable def binarySeparator (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) : Data n B where
  weights := limitWeight n B
  normalizer := normalizer n B
  nu := nuLaw n B hn hB
  mu := muLaw n B hn hB
  normalizer_pos := normalizer_pos hn hB
  weight_eq_limit := rfl
  even_weight_nonneg := fun _ hj ↦ limitWeight_nonneg_of_even hn hB hj
  odd_weight_nonpos := fun _ hj ↦ limitWeight_nonpos_of_odd hn hB hj
  nu_atom_even := fun _ hj ↦ nuLaw_atom_even hn hB hj
  nu_atom_odd := fun _ hj ↦ nuLaw_atom_odd hn hB hj
  mu_atom_odd := fun _ hj ↦ muLaw_atom_odd hn hB hj
  mu_atom_even := fun _ hj ↦ muLaw_atom_even hn hB hj
  nu_support := nuLaw_support hn hB
  mu_support := muLaw_support hn hB
  momentEquivalent := momentEquivalent_muLaw_nuLaw hn hB
  normalizer_ge := n_le_normalizer hn hB
  p0_ge := nuLaw_atom_zero_lower hn hB
  q1_ge := muLaw_atom_one_lower hn hB
  p2_ge := nuLaw_atom_two_lower hn hB
  weight_decay_two := fun _ ↦ limitWeight_decay_two hn hB

/-- Exact interface for `prop:key-prop-1_extended`.  In that proposition the manuscript's
`j ∈ ℕ` convention means `j > 0`; unlike `Data`, this interface deliberately exposes the
decay estimate only under that hypothesis. -/
structure ExtendedData (n B : ℕ) where
  weights : ℕ → ℝ
  normalizer : ℝ
  nu : Distribution
  mu : Distribution
  normalizer_pos : 0 < normalizer
  weight_eq_limit : weights = limitWeight n B
  even_weight_nonneg : ∀ j, Even j → 0 ≤ weights j
  odd_weight_nonpos : ∀ j, Odd j → weights j ≤ 0
  nu_atom_even : ∀ j, Even j →
    ((nu : Measure ℝ≥0) {nodeNN n B j}).toReal = weights j / normalizer
  nu_atom_odd : ∀ j, Odd j → ((nu : Measure ℝ≥0) {nodeNN n B j}) = 0
  mu_atom_odd : ∀ j, Odd j →
    ((mu : Measure ℝ≥0) {nodeNN n B j}).toReal = |weights j| / normalizer
  mu_atom_even : ∀ j, Even j → ((mu : Measure ℝ≥0) {nodeNN n B j}) = 0
  nu_support : ((nu : Measure ℝ≥0) (evenSupport n B)) = 1
  mu_support : ((mu : Measure ℝ≥0) (oddSupport n B)) = 1
  momentEquivalent : MomentEquivalent mu nu
  normalizer_ge : (n : ℝ) ≤ normalizer
  p0_ge : 1 - 2 / (n : ℝ) ≤ ((nu : Measure ℝ≥0) {nodeNN n B 0}).toReal
  q1_ge : 1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤
    ((mu : Measure ℝ≥0) {nodeNN n B 1}).toReal
  p2_ge : 1 / (4 * (n : ℝ)) ≤ ((nu : Measure ℝ≥0) {nodeNN n B 2}).toReal
  weight_decay_two_pos : ∀ j, 0 < j →
    |weights j| ≤ 8 * (n * B : ℝ) ^ 2 / node n B j ^ 2

/-- Canonical exact extended interface, obtained by forgetting the separately proved `j=0`
case from the stronger headline data. -/
noncomputable def extendedSeparator (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    ExtendedData n B := by
  let d := binarySeparator n B hn hB
  exact
    { weights := d.weights
      normalizer := d.normalizer
      nu := d.nu
      mu := d.mu
      normalizer_pos := d.normalizer_pos
      weight_eq_limit := d.weight_eq_limit
      even_weight_nonneg := d.even_weight_nonneg
      odd_weight_nonpos := d.odd_weight_nonpos
      nu_atom_even := d.nu_atom_even
      nu_atom_odd := d.nu_atom_odd
      mu_atom_odd := d.mu_atom_odd
      mu_atom_even := d.mu_atom_even
      nu_support := d.nu_support
      mu_support := d.mu_support
      momentEquivalent := d.momentEquivalent
      normalizer_ge := d.normalizer_ge
      p0_ge := d.p0_ge
      q1_ge := d.q1_ge
      p2_ge := d.p2_ge
      weight_decay_two_pos := fun j _hj ↦ d.weight_decay_two j }

/-- `prop:key-prop-1_extended`: the extended binary separator with the source's exact
positive-index decay quantifier. -/
theorem key_prop_1_extended (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Nonempty (ExtendedData n B) :=
  ⟨extendedSeparator n B hn hB⟩

/-- `thm:binary-separator` / `prop:key-prop-1`: the headline binary separator.
This is the same witness as the extended proposition, with the headline statement
represented by the reusable `Data` interface. -/
theorem binary_separator (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) :
    Nonempty (Data n B) :=
  ⟨binarySeparator n B hn hB⟩

namespace Data

/-- `thm:binary-separator`: the designated zero atom `q₀=0`. -/
theorem q0_eq_zero {n B : ℕ} (d : Data n B) :
    ((d.mu : Measure ℝ≥0) {nodeNN n B 0}) = 0 :=
  d.mu_atom_even 0 Even.zero

/-- `thm:binary-separator`: the designated zero atom `p₁=0`. -/
theorem p1_eq_zero {n B : ℕ} (d : Data n B) :
    ((d.nu : Measure ℝ≥0) {nodeNN n B 1}) = 0 :=
  d.nu_atom_odd 1 odd_one

/-- `thm:binary-separator`: the designated zero atom `q₂=0`. -/
theorem q2_eq_zero {n B : ℕ} (d : Data n B) :
    ((d.mu : Measure ℝ≥0) {nodeNN n B 2}) = 0 :=
  d.mu_atom_even 2 (by decide)

/-- `lem:explicit-support-bounds`, `sections/proofs.tex`: the four simultaneous quantitative
bounds, stated for the canonical extended-separator data interface. -/
theorem explicit_support_bounds {n B : ℕ} (d : Data n B) :
    (n : ℝ) ≤ d.normalizer ∧
      1 / (4 * (n : ℝ)) ≤ ((d.nu : Measure ℝ≥0) {nodeNN n B 2}).toReal ∧
      1 - 2 / (n : ℝ) ≤ ((d.nu : Measure ℝ≥0) {nodeNN n B 0}).toReal ∧
      1 - 1 / ((n : ℝ) ^ 2 * (B : ℝ) ^ 2) ≤
        ((d.mu : Measure ℝ≥0) {nodeNN n B 1}).toReal :=
  ⟨d.normalizer_ge, d.p2_ge, d.p0_ge, d.q1_ge⟩

/-- Binary half of `cor:maximal-total-variation`: the parity supports separate the two
probability laws, so their manuscript-normalized total variation is exactly one. -/
theorem manuscriptTV_eq_one {n B : ℕ} (d : Data n B)
    (hn : 3 ≤ n) (hB : 3 ≤ B) : manuscriptTV d.nu d.mu = 1 := by
  have hevenMeas : MeasurableSet (evenSupport n B) :=
    ((Set.countable_range (nodeNN n B)).mono (by
      rintro x ⟨j, hj, rfl⟩
      exact ⟨j, rfl⟩)).measurableSet
  have hnu : d.nu (evenSupport n B) = 1 := by
    rw [← ENNReal.coe_eq_one]
    simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using d.nu_support
  have hdis := evenSupport_disjoint_oddSupport hn hB
  have hsubset : evenSupport n B ⊆ (oddSupport n B)ᶜ := Set.disjoint_left.mp hdis
  have hmuOdd : (d.mu : Measure ℝ≥0) (oddSupport n B) = 1 := d.mu_support
  have hoddMeas : MeasurableSet (oddSupport n B) :=
    ((Set.countable_range (nodeNN n B)).mono (by
      rintro x ⟨j, hj, rfl⟩
      exact ⟨j, rfl⟩)).measurableSet
  have hmuComp : (d.mu : Measure ℝ≥0) ((oddSupport n B)ᶜ) = 0 :=
    (prob_compl_eq_zero_iff (μ := (d.mu : Measure ℝ≥0)) hoddMeas).2 hmuOdd
  have hmuMeasure : (d.mu : Measure ℝ≥0) (evenSupport n B) = 0 :=
    measure_mono_null hsubset hmuComp
  have hmu : d.mu (evenSupport n B) = 0 := by
    rw [← ENNReal.coe_eq_zero]
    simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hmuMeasure
  exact manuscriptTV_eq_one_of_separating_set d.nu d.mu hevenMeas hnu hmu

end Data

/-- The exact cutoff `L_M` from `lem:all-moment-weight-decay`. -/
def decayCutoff (B M : ℕ) : ℕ :=
  max 0 ⌈((M : ℝ) - 2) / (1 - 1 / (B : ℝ))⌉₊

/-- The explicit constant controlling indices `0,1,2` in
`lem:all-moment-weight-decay`. -/
def smallIndexDecayConstant (n B M : ℕ) : ℝ :=
  max (2 * n) (max (2 * n * (B : ℝ) ^ M) ((n * B : ℝ) ^ M))

/-- The explicit tail constant in `lem:all-moment-weight-decay`. -/
def tailDecayConstant (n B M : ℕ) : ℝ :=
  if M ≤ 2 then 8 * (n * B : ℝ) ^ 2
  else
    8 * (n * B : ℝ) ^ 2 *
      max (node n B (decayCutoff B M + 2) ^ (M - 2))
        ((2 : ℝ) ^ decayCutoff B M)

/-- The manuscript's explicit `C_M`. -/
def decayConstant (n B M : ℕ) : ℝ :=
  max (smallIndexDecayConstant n B M) (tailDecayConstant n B M)

theorem smallIndexDecayConstant_nonneg (n B M : ℕ) :
    0 ≤ smallIndexDecayConstant n B M := by
  simp [smallIndexDecayConstant]

theorem tailDecayConstant_nonneg (n B M : ℕ) :
    0 ≤ tailDecayConstant n B M := by
  simp only [tailDecayConstant]
  split <;> positivity

theorem decayConstant_nonneg (n B M : ℕ) : 0 ≤ decayConstant n B M := by
  exact le_max_of_le_left (smallIndexDecayConstant_nonneg n B M)

theorem one_le_decayCutoff {B M : ℕ} (hB : 3 ≤ B) (hM : 3 ≤ M) :
    1 ≤ decayCutoff B M := by
  let q : ℝ := ((M : ℝ) - 2) / (1 - 1 / (B : ℝ))
  have hden : 0 < 1 - 1 / (B : ℝ) := by
    have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
    have hBpos : (0 : ℝ) < B := by positivity
    rw [sub_pos, div_lt_one₀ hBpos]
    linarith
  have hnum : 0 < (M : ℝ) - 2 := by
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hq : 0 < q := div_pos hnum hden
  have hceil : 1 ≤ ⌈q⌉₊ := Nat.one_le_ceil_iff.mpr hq
  simpa only [decayCutoff, q, max_eq_right (Nat.zero_le _)] using hceil

/-- The defining ceiling inequality for the exact manuscript cutoff `L_M`. -/
theorem decayCutoff_exponent_condition {B M : ℕ} (hB : 3 ≤ B) (hM : 3 ≤ M) :
    B * (M - 2) ≤ decayCutoff B M * (B - 1) := by
  let q : ℝ := ((M : ℝ) - 2) / (1 - 1 / (B : ℝ))
  let L : ℕ := decayCutoff B M
  have hden : 0 < 1 - 1 / (B : ℝ) := by
    have hBR : (3 : ℝ) ≤ B := by exact_mod_cast hB
    have hBpos : (0 : ℝ) < B := by positivity
    rw [sub_pos, div_lt_one₀ hBpos]
    linarith
  have hL : q ≤ (L : ℝ) := by
    have hceil := Nat.le_ceil q
    simpa only [L, decayCutoff, q, max_eq_right (Nat.zero_le _)] using hceil
  have hbase : (M : ℝ) - 2 ≤ (L : ℝ) * (1 - 1 / (B : ℝ)) := by
    exact (div_le_iff₀ hden).mp hL
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hmul := mul_le_mul_of_nonneg_left hbase hBpos.le
  have hid : (B : ℝ) * (1 - 1 / (B : ℝ)) = (B : ℝ) - 1 := by
    field_simp [ne_of_gt hBpos]
  have hreal : (B : ℝ) * ((M : ℝ) - 2) ≤ (L : ℝ) * ((B : ℝ) - 1) := by
    calc
      (B : ℝ) * ((M : ℝ) - 2) ≤
          (B : ℝ) * ((L : ℝ) * (1 - 1 / (B : ℝ))) := hmul
      _ = (L : ℝ) * ((B : ℝ) * (1 - 1 / (B : ℝ))) := by ring
      _ = (L : ℝ) * ((B : ℝ) - 1) := by rw [hid]
  have hreal' : (B : ℝ) * ((M - 2 : ℕ) : ℝ) ≤
      (L : ℝ) * ((B - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ M), Nat.cast_sub (by omega : 1 ≤ B)]
    simpa using hreal
  have hnat : B * (M - 2) ≤ L * (B - 1) := by exact_mod_cast hreal'
  simpa only [L] using hnat

/-- Exact last-`L` factor estimate underlying `lem:all-moment-weight-decay`. -/
theorem middleProduct_le_cutoff_power {n B M j L : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hM : 3 ≤ M) (hL : 1 ≤ L)
    (hLj : L + 3 ≤ j) (hexponent : B * (M - 2) ≤ L * (B - 1)) :
    (∏ m ∈ Finset.Ico 3 j,
        (node n B m - node n B 2) / (node n B j - node n B m)) ≤
      (2 : ℝ) ^ L / node n B j ^ (M - 2) := by
  let c : ℝ := 2 * node n B (j - 1) / node n B j
  have hj4 : 4 ≤ j := by omega
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact div_nonneg (mul_nonneg (by norm_num) (node_pos hn hB (j - 1)).le)
      (node_pos hn hB j).le
  have htail : (∏ m ∈ Finset.Ico (j - L) j,
      (node n B m - node n B 2) / (node n B j - node n B m)) ≤ c ^ L := by
    calc
      (∏ m ∈ Finset.Ico (j - L) j,
          (node n B m - node n B 2) / (node n B j - node n B m)) ≤
          ∏ _m ∈ Finset.Ico (j - L) j, c := by
        apply Finset.prod_le_prod
        · intro m hm
          exact middleFactor_nonneg hn hB (by
            have hmem := Finset.mem_Ico.mp hm
            exact Finset.mem_Ico.mpr ⟨by omega, hmem.2⟩)
        · intro m hm
          apply middleFactor_le_two_mul_prev_div hn hB hj4
          · have := (Finset.mem_Ico.mp hm).1
            omega
          · exact (Finset.mem_Ico.mp hm).2
      _ = c ^ L := by
        have hcard : j - (j - L) = L := by omega
        simp only [Finset.prod_const, Nat.card_Ico, hcard]
  have hexp : L + B * (M - 2) ≤ B * L := by
    calc
      L + B * (M - 2) ≤ L + L * (B - 1) := Nat.add_le_add_left hexponent L
      _ = L * (1 + (B - 1)) := by ring
      _ = L * B := by congr 1 <;> omega
      _ = B * L := by ring
  have hjpred : j - 1 + 1 = j := by omega
  have hrec : node n B j = node n B (j - 1) ^ B := by
    rw [← hjpred]
    exact node_succ_eq_pow (j - 1) (by omega)
  have hy1 : (1 : ℝ) ≤ node n B (j - 1) := by
    exact (show (1 : ℝ) ≤ node n B 0 by simp).trans
      ((node_strictMono hn hB).monotone (Nat.zero_le _))
  have hpowexp : node n B (j - 1) ^ (L + B * (M - 2)) ≤
      node n B (j - 1) ^ (B * L) :=
    pow_le_pow_right₀ hy1 hexp
  have hratio : c ^ L ≤
      (2 : ℝ) ^ L / node n B j ^ (M - 2) := by
    have hxpos : 0 < node n B j := node_pos hn hB j
    have hcpow : c ^ L =
        (2 : ℝ) ^ L * node n B (j - 1) ^ L / node n B j ^ L := by
      dsimp only [c]
      rw [div_pow]
      ring
    rw [hcpow, div_le_div_iff₀ (pow_pos hxpos _) (pow_pos hxpos _)]
    have hinner : node n B (j - 1) ^ L * node n B j ^ (M - 2) ≤
        node n B j ^ L := by
      rw [hrec]
      simpa only [← pow_mul, ← pow_add] using hpowexp
    calc
      (2 : ℝ) ^ L * node n B (j - 1) ^ L * node n B j ^ (M - 2) =
          (2 : ℝ) ^ L *
            (node n B (j - 1) ^ L * node n B j ^ (M - 2)) := by ring
      _ ≤ (2 : ℝ) ^ L * node n B j ^ L :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
  exact (middleProduct_le_last hn hB hLj).trans (htail.trans hratio)

/-- Exact tail part of `lem:all-moment-weight-decay-uniform-K`. -/
theorem finiteWeight_decay_tail_exact {n B K M j : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hM : 1 ≤ M) (hj : 3 ≤ j) :
    |finiteWeight n B K j| ≤ tailDecayConstant n B M / node n B j ^ M := by
  let A : ℝ := 8 * (n * B : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hxpos : 0 < node n B j := node_pos hn hB j
  have hxone : 1 ≤ node n B j := by
    exact (show (1 : ℝ) ≤ node n B 0 by simp).trans
      ((node_strictMono hn hB).monotone (Nat.zero_le _))
  by_cases hMsmall : M ≤ 2
  · have hpow : node n B j ^ M ≤ node n B j ^ 2 :=
      pow_le_pow_right₀ hxone hMsmall
    have htail : tailDecayConstant n B M = A := by
      simp [tailDecayConstant, hMsmall, A]
    calc
      |finiteWeight n B K j| ≤ A / node n B j ^ 2 := by
        simpa only [A] using finiteWeight_decay_two
          (n := n) (B := B) (K := K) (j := j) hn hB
      _ ≤ A / node n B j ^ M :=
        div_le_div_of_nonneg_left hA (pow_pos hxpos M) hpow
      _ = tailDecayConstant n B M / node n B j ^ M := by rw [htail]
  · have hMlarge : 3 ≤ M := by omega
    let L : ℕ := decayCutoff B M
    have hL : 1 ≤ L := by
      simpa only [L] using one_le_decayCutoff hB hMlarge
    have htail : tailDecayConstant n B M =
        A * max (node n B (L + 2) ^ (M - 2)) ((2 : ℝ) ^ L) := by
      simp only [tailDecayConstant, if_neg hMsmall, A, L, Nat.cast_mul]
    have hpowM : node n B j ^ M =
        node n B j ^ 2 * node n B j ^ (M - 2) := by
      rw [← pow_add]
      congr 1
      omega
    by_cases hjlarge : L + 3 ≤ j
    · by_cases hjrange : j < K + 3
      · have hraw := finiteWeight_le_eight_mul_middle hn hB hj hjrange
        have hmiddle := middleProduct_le_cutoff_power hn hB hMlarge hL hjlarge
          (decayCutoff_exponent_condition hB hMlarge)
        calc
          |finiteWeight n B K j| ≤
              (A / node n B j ^ 2) *
                (∏ m ∈ Finset.Ico 3 j,
                  (node n B m - node n B 2) / (node n B j - node n B m)) := by
            simpa only [A] using hraw
          _ ≤ (A / node n B j ^ 2) *
                ((2 : ℝ) ^ L / node n B j ^ (M - 2)) := by
            exact mul_le_mul_of_nonneg_left hmiddle (by positivity)
          _ = (A * (2 : ℝ) ^ L) / node n B j ^ M := by
            rw [hpowM]
            field_simp
          _ ≤ (A * max (node n B (L + 2) ^ (M - 2)) ((2 : ℝ) ^ L)) /
                node n B j ^ M := by
            gcongr
            exact le_max_right _ _
          _ = tailDecayConstant n B M / node n B j ^ M := by rw [htail]
      · rw [finiteWeight_eq_zero_of_ge (Nat.le_of_not_gt hjrange), abs_zero]
        exact div_nonneg (tailDecayConstant_nonneg n B M) (pow_nonneg hxpos.le _)
    · have hjcut : j ≤ L + 2 := by omega
      have hnode : node n B j ≤ node n B (L + 2) :=
        (node_strictMono hn hB).monotone hjcut
      have hpow : node n B j ^ (M - 2) ≤ node n B (L + 2) ^ (M - 2) :=
        pow_le_pow_left₀ hxpos.le hnode (M - 2)
      calc
        |finiteWeight n B K j| ≤ A / node n B j ^ 2 := by
          simpa only [A] using finiteWeight_decay_two
            (n := n) (B := B) (K := K) (j := j) hn hB
        _ = (A * node n B j ^ (M - 2)) / node n B j ^ M := by
          rw [hpowM]
          field_simp
        _ ≤ (A * node n B (L + 2) ^ (M - 2)) / node n B j ^ M := by
          gcongr
        _ ≤ (A * max (node n B (L + 2) ^ (M - 2)) ((2 : ℝ) ^ L)) /
              node n B j ^ M := by
          gcongr
          exact le_max_left _ _
        _ = tailDecayConstant n B M / node n B j ^ M := by rw [htail]

theorem two_mul_n_le_smallIndexDecayConstant (n B M : ℕ) :
    2 * (n : ℝ) ≤ smallIndexDecayConstant n B M := by
  exact le_max_left _ _

theorem two_mul_n_mul_pow_le_smallIndexDecayConstant (n B M : ℕ) :
    2 * (n : ℝ) * (B : ℝ) ^ M ≤ smallIndexDecayConstant n B M := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem node_two_pow_le_smallIndexDecayConstant (n B M : ℕ) :
    (n * B : ℝ) ^ M ≤ smallIndexDecayConstant n B M := by
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- The zero-extended strengthening of `lem:all-moment-weight-decay-uniform-K`.
It is the form used for counting-measure dominated convergence. -/
theorem finiteWeight_decay_exact_zeroExtended {n B M : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hM : 1 ≤ M) (K j : ℕ) :
    |finiteWeight n B K j| ≤ decayConstant n B M / node n B j ^ M := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [node_zero, one_pow, div_one] using
      (calc
        |finiteWeight n B K 0| ≤ 2 * (n : ℝ) := abs_finiteWeight_zero_le hn hB K
        _ ≤ smallIndexDecayConstant n B M :=
          two_mul_n_le_smallIndexDecayConstant n B M
        _ ≤ decayConstant n B M := le_max_left _ _)
  · by_cases hj1 : j = 1
    · subst j
      rw [le_div_iff₀ (pow_pos (node_pos hn hB 1) M)]
      calc
        |finiteWeight n B K 1| * node n B 1 ^ M ≤
            (2 * (n : ℝ)) * node n B 1 ^ M :=
          mul_le_mul_of_nonneg_right (abs_finiteWeight_one_le hn hB K)
            (pow_nonneg (node_pos hn hB 1).le M)
        _ = 2 * (n : ℝ) * (B : ℝ) ^ M := by rw [node_one]
        _ ≤ smallIndexDecayConstant n B M :=
          two_mul_n_mul_pow_le_smallIndexDecayConstant n B M
        _ ≤ decayConstant n B M := le_max_left _ _
    · by_cases hj2 : j = 2
      · subst j
        rw [finiteWeight_two hn hB, abs_one,
          le_div_iff₀ (pow_pos (node_pos hn hB 2) M), one_mul, node_two]
        exact (node_two_pow_le_smallIndexDecayConstant n B M).trans (le_max_left _ _)
      · have hj3 : 3 ≤ j := by omega
        calc
          |finiteWeight n B K j| ≤
              tailDecayConstant n B M / node n B j ^ M :=
            finiteWeight_decay_tail_exact hn hB hM hj3
          _ ≤ decayConstant n B M / node n B j ^ M := by
            exact div_le_div_of_nonneg_right (le_max_right _ _)
              (pow_nonneg (node_pos hn hB j).le M)

/-- `lem:all-moment-weight-decay-uniform-K`: for every order `M ≥ 1`, the same
explicit manuscript constant `C_M` controls every finite normalized barycentric system
at each source index `0 ≤ j ≤ K+2`. -/
theorem all_moment_weight_decay_uniform_K {n B M : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hM : 1 ≤ M) (K j : ℕ) (_hj : j ≤ K + 2) :
    |finiteWeight n B K j| ≤ decayConstant n B M / node n B j ^ M :=
  finiteWeight_decay_exact_zeroExtended hn hB hM K j

/-- `lem:all-moment-weight-decay`: the pointwise limiting signed weights obey the
same exact `C_M / x_j^M` estimate as the finite systems, for every `M ≥ 1` and every
index (in particular `j = 0,1,2`). -/
theorem all_moment_weight_decay {n B M : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hM : 1 ≤ M) (j : ℕ) :
    |limitWeight n B j| ≤ decayConstant n B M / node n B j ^ M := by
  exact le_of_tendsto' (finiteWeight_tendsto_limitWeight hn hB j).abs
    (fun K ↦ finiteWeight_decay_exact_zeroExtended hn hB hM K j)

/-- `cor:limit-probabilities-well-defined`, `sections/proofs.tex`: the two parity-split
atom probabilities add to the normalized absolute signed weight, and obey the displayed
normalized `C_M /(W x_j^M)` bound for every `M ≥ 1` and every index `j`. -/
theorem limit_probabilities_atom_sum_and_decay {n B M : ℕ}
    (hn : 3 ≤ n) (hB : 3 ≤ B) (hM : 1 ≤ M) (j : ℕ) :
    (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal +
        (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal =
          |limitWeight n B j| / normalizer n B ∧
      (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal +
          (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal ≤
            decayConstant n B M /
              (normalizer n B * node n B j ^ M) := by
  have hsum :
      (((nuLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal +
          (((muLaw n B hn hB : Distribution) : Measure ℝ≥0) {nodeNN n B j}).toReal =
        |limitWeight n B j| / normalizer n B := by
    rcases Nat.even_or_odd j with hj | hj
    · rw [nuLaw_atom_even hn hB hj, muLaw_atom_even hn hB hj]
      simp only [ENNReal.toReal_zero, add_zero]
      rw [abs_of_nonneg (limitWeight_nonneg_of_even hn hB hj)]
    · rw [nuLaw_atom_odd hn hB hj, muLaw_atom_odd hn hB hj]
      simp
  refine ⟨hsum, ?_⟩
  rw [hsum]
  have hW : 0 < normalizer n B := normalizer_pos hn hB
  have hx : 0 < node n B j ^ M := pow_pos (node_pos hn hB j) _
  calc
    |limitWeight n B j| / normalizer n B ≤
        (decayConstant n B M / node n B j ^ M) / normalizer n B := by
      exact (div_le_div_iff_of_pos_right hW).2
        (all_moment_weight_decay hn hB hM j)
    _ = decayConstant n B M / (normalizer n B * node n B j ^ M) := by
      field_simp [hW.ne', hx.ne']

end BinarySeparator

end

end MomentAmbiguity
