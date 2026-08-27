import MomentAmbiguity.ProphetPolicyAnalysis

/-!
# Contiguous dyadic blocks for the prophet hard family

The manuscript uses zero-indexed blocks of sizes `N * 2^j`.  Their starting positions are
`N * (2^j - 1)`.  This module proves that these half-open intervals partition the packed
prefix and that switch instances have identical disclosed moment profiles and identical
marginals through every pre-switch block.
-/

open scoped ENNReal NNReal BigOperators

namespace MomentAmbiguity

open MeasureTheory Set

noncomputable section

def prophetBlockSize (N j : ℕ) : ℕ := N * 2 ^ j

def prophetBlockStart (N j : ℕ) : ℕ := N * (2 ^ j - 1)

@[simp]
theorem prophetBlockStart_zero (N : ℕ) : prophetBlockStart N 0 = 0 := by
  simp [prophetBlockStart]

theorem prophetBlockStart_succ (N j : ℕ) :
    prophetBlockStart N (j + 1) =
      prophetBlockStart N j + prophetBlockSize N j := by
  have hp : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
  calc
    prophetBlockStart N (j + 1) = N * ((2 ^ j - 1) + 2 ^ j) := by
      simp only [prophetBlockStart, pow_succ]
      congr 1
      omega
    _ = N * (2 ^ j - 1) + N * 2 ^ j := Nat.mul_add _ _ _
    _ = prophetBlockStart N j + prophetBlockSize N j := rfl

theorem prophetBlockStart_strictMono {N : ℕ} (hN : 0 < N) :
    StrictMono (prophetBlockStart N) := by
  intro j k hjk
  unfold prophetBlockStart
  apply Nat.mul_lt_mul_of_pos_left _ hN
  have hp := Nat.pow_lt_pow_right (by omega : 1 < 2) hjk
  have hjone : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
  omega

theorem prophetBlockStart_mono {N : ℕ} (hN : 0 < N) :
    Monotone (prophetBlockStart N) :=
  (prophetBlockStart_strictMono hN).monotone

/-- Membership in the `j`-th half-open block. -/
def InProphetBlock (N j i : ℕ) : Prop :=
  prophetBlockStart N j ≤ i ∧ i < prophetBlockStart N (j + 1)

theorem inProphetBlock_unique {N i j k : ℕ} (hN : 0 < N)
    (hj : InProphetBlock N j i) (hk : InProphetBlock N k i) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hnext : prophetBlockStart N (j + 1) ≤ prophetBlockStart N k :=
      prophetBlockStart_mono hN (by omega)
    exact (not_lt_of_ge (hnext.trans hk.1)) hj.2
  · have hnext : prophetBlockStart N (k + 1) ≤ prophetBlockStart N j :=
      prophetBlockStart_mono hN (by omega)
    exact (not_lt_of_ge (hnext.trans hj.1)) hk.2

/-- Every coordinate before the packed endpoint belongs to a unique block. -/
theorem exists_inProphetBlock_of_lt {N L i : ℕ} (hN : 0 < N)
    (hi : i < prophetBlockStart N L) :
    ∃ j : ℕ, j < L ∧ InProphetBlock N j i := by
  induction L with
  | zero => simp at hi
  | succ L ih =>
      by_cases hprev : i < prophetBlockStart N L
      · obtain ⟨j, hjL, hj⟩ := ih hprev
        exact ⟨j, by omega, hj⟩
      · refine ⟨L, by omega, ?_⟩
        exact ⟨by omega, by simpa [Nat.succ_eq_add_one] using hi⟩

/-- Locate a natural coordinate in the packed prefix, returning `none` outside it. -/
def prophetBlockOf (N L i : ℕ) : Option (Fin L) :=
  by
    classical
    exact if h : ∃ j : Fin L, InProphetBlock N j i then some (Classical.choose h) else none

theorem prophetBlockOf_eq_some {N L i : ℕ} (hN : 0 < N) (j : Fin L)
    (hj : InProphetBlock N j i) : prophetBlockOf N L i = some j := by
  unfold prophetBlockOf
  split
  · next h =>
      congr 1
      exact Fin.ext (inProphetBlock_unique hN (Classical.choose_spec h) hj)
  · next h => exact (h ⟨j, hj⟩).elim

theorem prophetBlockOf_eq_some_iff {N L i : ℕ} (hN : 0 < N) (j : Fin L) :
    prophetBlockOf N L i = some j ↔ InProphetBlock N j i := by
  constructor
  · intro h
    unfold prophetBlockOf at h
    split at h
    · next hex =>
      injection h with heq
      rw [← heq]
      exact Classical.choose_spec hex
    · simp at h
  · exact prophetBlockOf_eq_some hN j

theorem prophetBlockOf_eq_none_of_le {N L i : ℕ}
    (hi : prophetBlockStart N L ≤ i) : prophetBlockOf N L i = none := by
  unfold prophetBlockOf
  rw [dif_neg]
  rintro ⟨j, hj⟩
  have hJL : j.1 + 1 ≤ L := by omega
  have hend : prophetBlockStart N (j.1 + 1) ≤ prophetBlockStart N L := by
    by_cases hN0 : N = 0
    · simp [hN0, prophetBlockStart]
    · exact prophetBlockStart_mono (Nat.pos_of_ne_zero hN0) hJL
  exact (not_lt_of_ge (hend.trans hi)) hj.2

theorem prophetBlockOf_ne_none_of_lt {N L i : ℕ} (hN : 0 < N)
    (hi : i < prophetBlockStart N L) : prophetBlockOf N L i ≠ none := by
  obtain ⟨j, hjL, hj⟩ := exists_inProphetBlock_of_lt hN hi
  rw [prophetBlockOf_eq_some hN ⟨j, hjL⟩ hj]
  simp

theorem prophetBlockOf_le_of_le {N L i q : ℕ} (hN : 0 < N) (j : Fin L)
    (hi : InProphetBlock N j i) (hqi : q ≤ i) {k : Fin L}
    (hq : prophetBlockOf N L q = some k) : k ≤ j := by
  have hk : InProphetBlock N k q := by
    unfold prophetBlockOf at hq
    split at hq
    · next h =>
      injection hq with heq
      rw [← heq]
      exact Classical.choose_spec h
    · simp at hq
  by_contra hnot
  have hnext : prophetBlockStart N (j.1 + 1) ≤ prophetBlockStart N k :=
    prophetBlockStart_mono hN (by omega)
  exact (not_lt_of_ge ((hnext.trans hk.1).trans hqi)) hi.2

/-- A moment-equivalent pair used at one dyadic block size. -/
structure ProphetBlockPair where
  mu : Distribution
  nu : Distribution
  momentEquivalent : MomentEquivalent mu nu

/-- The deterministic zero law used to pad the unpacked suffix. -/
def zeroDistribution : Distribution := MeasureTheory.diracProba (0 : ℝ≥0)

theorem zeroDistribution_hasFiniteMoments : HasFiniteMoments zeroDistribution := by
  intro k
  rw [HasFiniteMoment]
  refine MeasureTheory.integrable_dirac' ?_ ?_
  · unfold momentIntegrand
    fun_prop
  · simp [momentIntegrand]

/-- All blocks use their `nu` member. -/
def prophetAllNuLaws (m N L : ℕ) (pairs : Fin L → ProphetBlockPair) :
    Fin m → Distribution := fun i ↦
  match prophetBlockOf N L i.1 with
  | none => zeroDistribution
  | some j => (pairs j).nu

/-- Switch instance `I_t`: blocks through `t` use `nu`, and later blocks use `mu`. -/
def prophetSwitchLaws (m N L : ℕ) (pairs : Fin L → ProphetBlockPair) (t : Fin L) :
    Fin m → Distribution := fun i ↦
  match prophetBlockOf N L i.1 with
  | none => zeroDistribution
  | some j => if j ≤ t then (pairs j).nu else (pairs j).mu

theorem prophetSwitchLaws_eq_nu_of_block {m N L : ℕ} (hN : 0 < N)
    (pairs : Fin L → ProphetBlockPair) {t j : Fin L} (hjt : j ≤ t)
    {i : Fin m} (hi : InProphetBlock N j i.1) :
    prophetSwitchLaws m N L pairs t i = (pairs j).nu := by
  simp [prophetSwitchLaws, prophetBlockOf_eq_some hN j hi, hjt]

theorem prophetSwitchLaws_eq_mu_of_block {m N L : ℕ} (hN : 0 < N)
    (pairs : Fin L → ProphetBlockPair) {t j : Fin L} (htj : t < j)
    {i : Fin m} (hi : InProphetBlock N j i.1) :
    prophetSwitchLaws m N L pairs t i = (pairs j).mu := by
  simp [prophetSwitchLaws, prophetBlockOf_eq_some hN j hi, (not_le_of_gt htj)]

theorem prophetAllNuLaws_eq_of_block {m N L : ℕ} (hN : 0 < N)
    (pairs : Fin L → ProphetBlockPair) {j : Fin L} {i : Fin m}
    (hi : InProphetBlock N j i.1) :
    prophetAllNuLaws m N L pairs i = (pairs j).nu := by
  simp [prophetAllNuLaws, prophetBlockOf_eq_some hN j hi]

theorem prophetSwitchLaws_hasFiniteMoments {m N L : ℕ}
    (pairs : Fin L → ProphetBlockPair) (t : Fin L) (i : Fin m) :
    HasFiniteMoments (prophetSwitchLaws m N L pairs t i) := by
  simp only [prophetSwitchLaws]
  split
  · exact zeroDistribution_hasFiniteMoments
  · split
    · exact (pairs _).momentEquivalent.right_finite
    · exact (pairs _).momentEquivalent.left_finite

theorem prophetAllNuLaws_hasFiniteMoments {m N L : ℕ}
    (pairs : Fin L → ProphetBlockPair) (i : Fin m) :
    HasFiniteMoments (prophetAllNuLaws m N L pairs i) := by
  simp only [prophetAllNuLaws]
  split
  · exact zeroDistribution_hasFiniteMoments
  · exact (pairs _).momentEquivalent.right_finite

/-- All switch points disclose exactly the same coordinate-by-coordinate moment profile. -/
theorem disclosedProfile_prophetSwitch_eq_allNu {m N L : ℕ}
    (pairs : Fin L → ProphetBlockPair) (t : Fin L) :
    disclosedProfile (prophetSwitchLaws m N L pairs t) =
      disclosedProfile (prophetAllNuLaws m N L pairs) := by
  funext i
  simp only [disclosedProfile, prophetSwitchLaws, prophetAllNuLaws]
  split
  · rfl
  · split
    · rfl
    · exact (pairs _).momentEquivalent.sequence_eq

/-- Through a block at or before the switch, the switch instance and the all-`nu` instance
have identical marginals. -/
theorem prophetSwitchLaws_prefix_eq_allNu {m N L : ℕ} (hN : 0 < N)
    (pairs : Fin L → ProphetBlockPair) {t j : Fin L} (hjt : j ≤ t)
    {i : Fin m} (hi : InProphetBlock N j i.1) :
    ∀ q : Fin m, q ≤ i →
      prophetSwitchLaws m N L pairs t q = prophetAllNuLaws m N L pairs q := by
  intro q hqi
  simp only [prophetSwitchLaws, prophetAllNuLaws]
  cases hq : prophetBlockOf N L q.1 with
  | none => rfl
  | some k =>
      have hkj : k ≤ j := prophetBlockOf_le_of_le hN j hi
        (by exact_mod_cast hqi) hq
      simp [hq, hkj.trans hjt]

/-! ## Enumerating one contiguous block -/

def prophetBlockIndices (m N j : ℕ) : Finset (Fin m) :=
  by
    classical
    exact Finset.univ.filter fun i ↦ InProphetBlock N j i.1

theorem mem_prophetBlockIndices {m N j : ℕ} {i : Fin m} :
    i ∈ prophetBlockIndices m N j ↔ InProphetBlock N j i.1 := by
  classical
  simp [prophetBlockIndices]

/-- The `k`-th coordinate of block `j`. -/
def prophetBlockCoord {m : ℕ} (N j : ℕ)
    (hend : prophetBlockStart N (j + 1) ≤ m) (k : Fin (prophetBlockSize N j)) : Fin m :=
  ⟨prophetBlockStart N j + k.1, by
    have hk : prophetBlockStart N j + k.1 <
        prophetBlockStart N j + prophetBlockSize N j := Nat.add_lt_add_left k.2 _
    rw [← prophetBlockStart_succ] at hk
    exact hk.trans_le hend⟩

theorem prophetBlockCoord_mem {m : ℕ} (N j : ℕ)
    (hend : prophetBlockStart N (j + 1) ≤ m) (k : Fin (prophetBlockSize N j)) :
    InProphetBlock N j (prophetBlockCoord N j hend k).1 := by
  refine ⟨?_, ?_⟩
  · simp [prophetBlockCoord]
  · dsimp only [prophetBlockCoord]
    rw [prophetBlockStart_succ]
    omega

/-- Reindexing a sum over a block by its local coordinate. -/
theorem sum_prophetBlockIndices {m N j : ℕ}
    (hend : prophetBlockStart N (j + 1) ≤ m) (f : Fin m → ℝ) :
    (∑ i ∈ prophetBlockIndices m N j, f i) =
      ∑ k : Fin (prophetBlockSize N j), f (prophetBlockCoord N j hend k) := by
  classical
  apply Finset.sum_bij
      (fun i hi ↦ ⟨i.1 - prophetBlockStart N j, by
        have hstart := (mem_prophetBlockIndices.mp hi).1
        have hmem := (mem_prophetBlockIndices.mp hi).2
        rw [prophetBlockStart_succ] at hmem
        exact (Nat.sub_lt_iff_lt_add' hstart).2 (by simpa [add_comm] using hmem)⟩)
  · intro i hi
    simp
  · intro i₁ hi₁ i₂ hi₂ heq
    apply Fin.ext
    have h₁ := (mem_prophetBlockIndices.mp hi₁).1
    have h₂ := (mem_prophetBlockIndices.mp hi₂).1
    have heqv := Fin.ext_iff.mp heq
    change i₁.1 - prophetBlockStart N j = i₂.1 - prophetBlockStart N j at heqv
    calc
      i₁.1 = (i₁.1 - prophetBlockStart N j) + prophetBlockStart N j :=
        (Nat.sub_add_cancel h₁).symm
      _ = (i₂.1 - prophetBlockStart N j) + prophetBlockStart N j := by rw [heqv]
      _ = i₂.1 := Nat.sub_add_cancel h₂
  · intro k hk
    refine ⟨prophetBlockCoord N j hend k,
      mem_prophetBlockIndices.mpr (prophetBlockCoord_mem N j hend k), ?_⟩
    apply Fin.ext
    simp [prophetBlockCoord]
  · intro i hi
    congr 1
    apply Fin.ext
    have hstart := (mem_prophetBlockIndices.mp hi).1
    simp [prophetBlockCoord, Nat.add_sub_of_le hstart]

theorem card_prophetBlockIndices {m N j : ℕ}
    (hend : prophetBlockStart N (j + 1) ≤ m) :
    (prophetBlockIndices m N j).card = prophetBlockSize N j := by
  have hsum := sum_prophetBlockIndices hend (fun _ : Fin m ↦ (1 : ℝ))
  simpa using hsum

/-- Distinct blocks are disjoint, so their sums are bounded by the sum over all coordinates. -/
theorem sum_blocks_le_sum_univ {m N L : ℕ} (hN : 0 < N) (f : Fin m → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ j : Fin L, ∑ i ∈ prophetBlockIndices m N j, f i) ≤ ∑ i : Fin m, f i := by
  classical
  simp_rw [show ∀ j : Fin L,
      (∑ i ∈ prophetBlockIndices m N j, f i) =
        ∑ i : Fin m, if prophetBlockOf N L i.1 = some j then f i else 0 by
    intro j
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i
      simp [prophetBlockIndices, prophetBlockOf_eq_some_iff hN j]
    · intro i hi
      rfl]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  cases hblock : prophetBlockOf N L i.1 with
  | none => simp [hblock, hf i]
  | some k => simp [hblock, hf i]

theorem sum_univ_eq_sum_blocks_of_zero_outside {m N L : ℕ} (hN : 0 < N)
    (f : Fin m → ℝ)
    (hzero : ∀ i, prophetBlockOf N L i.1 = none → f i = 0) :
    (∑ i : Fin m, f i) =
      ∑ j : Fin L, ∑ i ∈ prophetBlockIndices m N j, f i := by
  classical
  simp_rw [show ∀ j : Fin L,
      (∑ i ∈ prophetBlockIndices m N j, f i) =
        ∑ i : Fin m, if prophetBlockOf N L i.1 = some j then f i else 0 by
    intro j
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i
      simp [prophetBlockIndices, prophetBlockOf_eq_some_iff hN j]
    · intro i hi
      rfl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  cases hblock : prophetBlockOf N L i.1 with
  | none => simp [hblock, hzero i hblock]
  | some k => simp [hblock]

theorem sum_weighted_blocks_eq {m N L : ℕ} (hN : 0 < N)
    (c : Fin L → ℝ) (f : Fin m → ℝ) :
    (∑ j : Fin L, c j * ∑ i ∈ prophetBlockIndices m N j, f i) =
      ∑ i : Fin m, match prophetBlockOf N L i.1 with
        | none => 0
        | some j => c j * f i := by
  classical
  simp_rw [show ∀ j : Fin L,
      c j * (∑ i ∈ prophetBlockIndices m N j, f i) =
        ∑ i : Fin m,
          if prophetBlockOf N L i.1 = some j then c j * f i else 0 by
    intro j
    rw [Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i
      simp [prophetBlockIndices, prophetBlockOf_eq_some_iff hN j]
    · intro i hi
      rfl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  cases hblock : prophetBlockOf N L i.1 with
  | none => simp
  | some k => simp

/-- Unconditional probability that a policy selects a coordinate in block `j`. -/
def prophetBlockStopProbability {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (laws : Fin m → Distribution) (N j : ℕ) : ℝ :=
  ∑ i ∈ prophetBlockIndices m N j,
    ∫ x, prophetSelectProbability policy profile i x
      ∂(independentValues laws : Measure _)

theorem prophetBlockStopProbability_nonneg {m : ℕ} (policy : ProphetPolicy m)
    (profile : MomentProfile m) (laws : Fin m → Distribution) (N j : ℕ) :
    0 ≤ prophetBlockStopProbability policy profile laws N j := by
  unfold prophetBlockStopProbability
  exact Finset.sum_nonneg fun i hi ↦ integral_nonneg fun x ↦
    prophetSelectProbability_nonneg policy profile i x

theorem sum_prophetBlockStopProbability_le_one {m N L : ℕ} (hN : 0 < N)
    (policy : ProphetPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) :
    (∑ j : Fin L, prophetBlockStopProbability policy profile laws N j) ≤ 1 := by
  let f : Fin m → ℝ := fun i ↦
    ∫ x, prophetSelectProbability policy profile i x
      ∂(independentValues laws : Measure _)
  calc
    (∑ j : Fin L, prophetBlockStopProbability policy profile laws N j) =
        ∑ j : Fin L, ∑ i ∈ prophetBlockIndices m N j, f i := rfl
    _ ≤ ∑ i : Fin m, f i := sum_blocks_le_sum_univ hN f
      (fun i ↦ integral_nonneg fun x ↦
        prophetSelectProbability_nonneg policy profile i x)
    _ ≤ 1 := sum_integral_prophetSelectProbability_le_one policy profile laws

/-- Before a switch, each block stopping probability is the same as on the all-`nu`
instance. -/
theorem prophetBlockStopProbability_switch_eq_allNu {m N L : ℕ} (hN : 0 < N)
    (pairs : Fin L → ProphetBlockPair) (policy : ProphetPolicy m) {t j : Fin L}
    (hjt : j ≤ t) :
    prophetBlockStopProbability policy
        (disclosedProfile (prophetAllNuLaws m N L pairs))
        (prophetSwitchLaws m N L pairs t) N j =
      prophetBlockStopProbability policy
        (disclosedProfile (prophetAllNuLaws m N L pairs))
        (prophetAllNuLaws m N L pairs) N j := by
  unfold prophetBlockStopProbability
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_selectProbability_eq_of_prefix
  exact prophetSwitchLaws_prefix_eq_allNu hN pairs hjt
    (mem_prophetBlockIndices.mp hi)

end

end MomentAmbiguity
