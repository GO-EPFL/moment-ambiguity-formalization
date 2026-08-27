import MomentAmbiguity.ProphetSeparator
import MomentAmbiguity.CorreaLower
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Prophet inequalities under moment disclosure

This module keeps all guarantees in multiplication form.  The logarithmic rank-one lower bound
is supplied internally by the measurable exponential-bucketing construction in
`CorreaLower`; order-statistic monotonicity propagates it to every fixed rank.  Compatibility
helpers retain the former explicit-external-interface formulation.
-/

open scoped ENNReal NNReal BigOperators Topology

namespace MomentAmbiguity

open Filter MeasureTheory Set

noncomputable section

/-- The explicit constant from `cor:order-stat-separator`. -/
def prophetKappa (r : ℕ) : ℝ :=
  Real.exp (-(1 : ℝ) / 4) / ((8 : ℝ) ^ r * (r.factorial : ℝ))

theorem prophetKappa_pos (r : ℕ) : 0 < prophetKappa r := by
  unfold prophetKappa
  positivity

/-- The `r`-th largest value is pointwise at most the largest value. -/
theorem descendingOrderStatistic_le_first {m : ℕ} (hm : 1 ≤ m)
    (r : ValidRank m) (x : ProphetPath m) :
    descendingOrderStatistic r x ≤
      descendingOrderStatistic (External.firstRank m hm) x := by
  rw [descendingOrderStatistic, Finset.sup'_le_iff]
  intro s hs
  have hcard : s.card = r.1 := (Finset.mem_powersetCard.1 hs).2
  have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨i, hi⟩ := hsne
  have hsingleton : ({i} : Finset (Fin m)) ∈
      rankSubsets (External.firstRank m hm) := by
    simp [rankSubsets, External.firstRank]
  calc
    subsetMinimum x s ≤ x i := by
      have hsne' : s.Nonempty := ⟨i, hi⟩
      rw [subsetMinimum, dif_pos hsne']
      exact Finset.inf'_le _ hi
    _ = subsetMinimum x {i} := by simp [subsetMinimum]
    _ ≤ (rankSubsets (External.firstRank m hm)).sup'
        (rankSubsets_nonempty (External.firstRank m hm)) (subsetMinimum x) :=
      Finset.le_sup' _ hsingleton

theorem orderStatisticBenchmark_le_first {m : ℕ} (hm : 1 ≤ m)
    (r : ValidRank m) (laws : Fin m → Distribution)
    (hfinite : ∀ i, HasFiniteMoments (laws i)) :
    orderStatisticBenchmark r laws ≤
      orderStatisticBenchmark (External.firstRank m hm) laws := by
  have hfirst : HasFiniteFirstMoments laws := fun i ↦ hfinite i 1
  unfold orderStatisticBenchmark
  exact integral_mono
    (integrable_descendingOrderStatistic r laws hfirst)
    (integrable_descendingOrderStatistic (External.firstRank m hm) laws hfirst)
    (fun x ↦ by exact_mod_cast descendingOrderStatistic_le_first hm r x)

/-- A nonnegative guarantee against the maximum is also a guarantee against every lower order
statistic, without dividing by either benchmark. -/
theorem prophetGuarantee_first_to_rank {m : ℕ} (hm : 1 ≤ m)
    (r : ValidRank m) {alpha : ℝ} (halpha : 0 ≤ alpha) (policy : ProphetPolicy m)
    (hpolicy : ProphetUniversalGuarantee (External.firstRank m hm) alpha policy) :
    ProphetUniversalGuarantee r alpha policy := by
  intro laws hfinite
  calc
    alpha * orderStatisticBenchmark r laws ≤
        alpha * orderStatisticBenchmark (External.firstRank m hm) laws :=
      mul_le_mul_of_nonneg_left (orderStatisticBenchmark_le_first hm r laws hfinite) halpha
    _ ≤ prophetExpectedReward policy laws := hpolicy laws hfinite

theorem prophetFeasibleSet_first_subset {m : ℕ} (hm : 1 ≤ m) (r : ValidRank m) :
    prophetFeasibleSet (External.firstRank m hm) ⊆ prophetFeasibleSet r := by
  rintro alpha ⟨halpha, policy, hpolicy⟩
  exact ⟨halpha, policy, prophetGuarantee_first_to_rank hm r halpha policy hpolicy⟩

theorem rhoMom_first_le_rank {m : ℕ} (hm : 1 ≤ m) (r : ValidRank m) :
    rhoMom (External.firstRank m hm) ≤ rhoMom r := by
  apply csSup_le
  · exact prophetFeasibleSet_nonempty (External.firstRank m hm)
  · intro alpha halpha
    exact le_csSup (prophetFeasibleSet_bddAbove r)
      (prophetFeasibleSet_first_subset hm r halpha)

/-- Compatibility helper for `prop:log-lowerbound`, retaining the former explicit external
interface as a theorem parameter. -/
theorem prophet_log_lower_bound_of_external
    (hCorrea : External.CorreaLogLowerBound) :
    ∃ a : ℝ, 0 < a ∧ ∃ m_lb : ℕ, ∃ hm_lb : 2 ≤ m_lb,
      ∀ (m : ℕ) (hm : m_lb ≤ m),
        a / Real.log m ≤ rhoMom (External.firstRank m (by omega)) :=
  hCorrea

/-- `prop:log-lowerbound`, fully verified from the internal exponential-bucketing policy. -/
theorem prophet_log_lower_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ m_lb : ℕ, ∃ hm_lb : 2 ≤ m_lb,
      ∀ (m : ℕ) (hm : m_lb ≤ m),
        a / Real.log m ≤ rhoMom (External.firstRank m (by omega)) :=
  prophet_log_lower_bound_of_external correaLogLowerBound

/-- Compatibility helper for the manuscript's fixed-rank lower direction, parameterized by
the former external interface. -/
theorem prophet_log_lower_bound_rank_of_external
    (hCorrea : External.CorreaLogLowerBound) (r : ℕ) (hr : 1 ≤ r) :
    ∃ a : ℝ, 0 < a ∧ ∃ m₀ : ℕ, ∃ hrm₀ : r ≤ m₀, ∃ hm₀ : 2 ≤ m₀,
      ∀ (m : ℕ) (hm : m₀ ≤ m),
        a / Real.log m ≤ rhoMom (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) := by
  obtain ⟨a, ha, m_lb, hm_lb, hlower⟩ := hCorrea
  let m₀ := max r m_lb
  refine ⟨a, ha, m₀, le_max_left _ _, hm_lb.trans (le_max_right _ _), ?_⟩
  intro m hm
  have hm_lb_m : m_lb ≤ m := (le_max_right r m_lb).trans hm
  have hmpos : 1 ≤ m := hr.trans ((le_max_left r m_lb).trans hm)
  exact (hlower m hm_lb_m).trans
    (rhoMom_first_le_rank hmpos (⟨r, hr, (le_max_left r m_lb).trans hm⟩ : ValidRank m))

/-- The manuscript's lower direction for every fixed rank, fully verified by propagating the
internal rank-one bucket guarantee. -/
theorem prophet_log_lower_bound_rank (r : ℕ) (hr : 1 ≤ r) :
    ∃ a : ℝ, 0 < a ∧ ∃ m₀ : ℕ, ∃ hrm₀ : r ≤ m₀, ∃ hm₀ : 2 ≤ m₀,
      ∀ (m : ℕ) (hm : m₀ ≤ m),
        a / Real.log m ≤ rhoMom (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) :=
  prophet_log_lower_bound_rank_of_external correaLogLowerBound r hr

/-- Integer threshold used in the explicit upper construction. -/
def prophetN (r : ℕ) : ℕ :=
  max 6 (max (2 * r) ⌈(1 / prophetKappa r : ℝ)⌉₊)

theorem six_le_prophetN (r : ℕ) : 6 ≤ prophetN r := le_max_left _ _

theorem two_mul_le_prophetN (r : ℕ) : 2 * r ≤ prophetN r :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem inv_kappa_le_prophetN (r : ℕ) :
    1 / prophetKappa r ≤ prophetN r := by
  have hc : ⌈(1 / prophetKappa r : ℝ)⌉₊ ≤ prophetN r :=
    (le_max_right (2 * r) ⌈(1 / prophetKappa r : ℝ)⌉₊).trans
      (le_max_right 6 (max (2 * r) ⌈(1 / prophetKappa r : ℝ)⌉₊))
  exact (Nat.le_ceil (1 / prophetKappa r)).trans (by exact_mod_cast hc)

/-- The explicit constants in the upper half of `thm:prophet`. -/
def prophetA (r : ℕ) : ℝ :=
  6 * prophetN r + 3 + 12 / prophetN r

def prophetB (r : ℕ) : ℝ :=
  4 * prophetA r * Real.log 2 / (3 * prophetKappa r * prophetN r)

theorem prophetA_pos (r : ℕ) : 0 < prophetA r := by
  unfold prophetA
  have hN : (0 : ℝ) < prophetN r := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 6) (six_le_prophetN r))
  positivity

theorem prophetB_pos (r : ℕ) : 0 < prophetB r := by
  unfold prophetB
  have hN : (0 : ℝ) < prophetN r := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 6) (six_le_prophetN r))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnum : 0 < 4 * prophetA r * Real.log 2 := by
    exact mul_pos (mul_pos (by norm_num) (prophetA_pos r)) hlog
  have hden : 0 < 3 * prophetKappa r * (prophetN r : ℝ) := by
    exact mul_pos (mul_pos (by norm_num) (prophetKappa_pos r)) hN
  exact div_pos hnum hden

/-! ## Dyadic block range -/

/-- Largest dyadic block count satisfying the manuscript's packing inequality. -/
def prophetLevel (N m : ℕ) : ℕ := Nat.log 2 (m / N + 1)

theorem prophetLevel_packing {N m : ℕ} (hN : 1 ≤ N) :
    N * (2 ^ prophetLevel N m - 1) ≤ m := by
  have hx0 : m / N + 1 ≠ 0 := by
    exact Nat.add_one_ne_zero _
  have hp : 2 ^ prophetLevel N m ≤ m / N + 1 := by
    exact Nat.pow_log_le_self 2 hx0
  have hsub : 2 ^ prophetLevel N m - 1 ≤ m / N := by
    rw [Nat.sub_le_iff_le_add]
    simpa [add_comm] using hp
  calc
    N * (2 ^ prophetLevel N m - 1) ≤ N * (m / N) :=
      Nat.mul_le_mul_left N hsub
    _ ≤ m := Nat.mul_div_le m N

theorem prophetLevel_maximal {N m : ℕ} (hN : 1 ≤ N) :
    m < N * (2 ^ (prophetLevel N m + 1) - 1) := by
  have hpow : m / N + 1 < 2 ^ (prophetLevel N m + 1) := by
    simpa [prophetLevel, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by omega) (m / N + 1)
  have hdiv : m / N < 2 ^ (prophetLevel N m + 1) - 1 := by omega
  have hlt : m < (2 ^ (prophetLevel N m + 1) - 1) * N :=
    (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hN)).1 hdiv
  simpa [mul_comm] using hlt

/-- Exact maximality characterization, including the edge case `L=0`. -/
theorem prophetLevel_spec {N m L : ℕ} (hN : 1 ≤ N) :
    L ≤ prophetLevel N m ↔ N * (2 ^ L - 1) ≤ m := by
  constructor
  · intro hL
    have hp : 2 ^ L ≤ 2 ^ prophetLevel N m :=
      Nat.pow_le_pow_right (by omega) hL
    calc
      N * (2 ^ L - 1) ≤ N * (2 ^ prophetLevel N m - 1) := by
        exact Nat.mul_le_mul_left N (Nat.sub_le_sub_right hp 1)
      _ ≤ m := prophetLevel_packing hN
  · intro hpack
    by_contra hnot
    have hsucc : prophetLevel N m + 1 ≤ L := by omega
    have hpow : 2 ^ (prophetLevel N m + 1) ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by omega) hsucc
    have hblocks : N * (2 ^ (prophetLevel N m + 1) - 1) ≤
        N * (2 ^ L - 1) :=
      Nat.mul_le_mul_left N (Nat.sub_le_sub_right hpow 1)
    have hmax := prophetLevel_maximal (m := m) hN
    exact (not_lt_of_ge (hblocks.trans hpack)) hmax

/-- The logarithmic range used in `thm:prophet`: maximality of the packed dyadic blocks and
`m ≥ 4N²` imply `L > (log m)/(2 log 2)`. -/
theorem prophetLevel_log_range {N m : ℕ} (hN : 1 ≤ N)
    (hm : 4 * N ^ 2 ≤ m) :
    Real.log m / (2 * Real.log 2) < (prophetLevel N m : ℝ) := by
  have hNposNat : 0 < N := Nat.zero_lt_of_lt hN
  have hmposNat : 0 < m := lt_of_lt_of_le (by positivity : 0 < 4 * N ^ 2) hm
  have hmax := prophetLevel_maximal (m := m) hN
  have hblock_le : N * (2 ^ (prophetLevel N m + 1) - 1) ≤
      N * 2 ^ (prophetLevel N m + 1) := by
    exact Nat.mul_le_mul_left N (Nat.sub_le _ _)
  have hreal : (m : ℝ) < (N : ℝ) * (2 : ℝ) ^ (prophetLevel N m + 1) := by
    exact_mod_cast hmax.trans_le hblock_le
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmposNat
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hpowposR : (0 : ℝ) < (2 : ℝ) ^ (prophetLevel N m + 1) :=
    pow_pos (by norm_num) _
  have hprodposR : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (prophetLevel N m + 1) :=
    mul_pos hNposR hpowposR
  have hlogUpper : Real.log (m : ℝ) <
      Real.log ((N : ℝ) * (2 : ℝ) ^ (prophetLevel N m + 1)) :=
    Real.strictMonoOn_log (show (m : ℝ) ∈ Set.Ioi 0 from hmposR)
      (show (N : ℝ) * (2 : ℝ) ^ (prophetLevel N m + 1) ∈ Set.Ioi 0 from hprodposR)
      hreal
  rw [Real.log_mul hNposR.ne'
      (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow] at hlogUpper
  have hcast : (4 : ℝ) * (N : ℝ) ^ 2 ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hlogLower : Real.log ((4 : ℝ) * (N : ℝ) ^ 2) ≤ Real.log (m : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (4 : ℝ) * (N : ℝ) ^ 2 ∈ Set.Ioi 0 from
        mul_pos (by norm_num) (pow_pos hNposR _))
      (show (m : ℝ) ∈ Set.Ioi 0 from hmposR) hcast
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (pow_ne_zero _ (by exact_mod_cast hNposNat.ne')),
    Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlogLower
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ (mul_pos (by norm_num) hlogTwo)]
  push_cast at hlogUpper hlogLower
  nlinarith

/-- The maximal-block logarithmic range converts the explicit hard-family coefficient into
the manuscript constant `b_r / log m`. -/
theorem prophet_hard_coefficient_lt (r m : ℕ)
    (hm : 4 * prophetN r ^ 2 ≤ m) :
    2 * prophetA r /
        (3 * prophetKappa r * (prophetN r : ℝ) * (prophetLevel (prophetN r) m : ℝ)) <
      prophetB r / Real.log m := by
  let N := prophetN r
  let L := prophetLevel N m
  have hNnat : 1 ≤ N := by
    dsimp [N]
    exact (by omega : 1 ≤ 6).trans (six_le_prophetN r)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hNnat)
  have hmposNat : 1 < m := by
    have hpack : 4 * N ^ 2 ≤ m := by simpa [N] using hm
    have hNsquare : 1 ≤ N ^ 2 := by
      exact one_le_pow₀ (Nat.zero_lt_of_lt hNnat)
    have : 4 ≤ m := le_trans (Nat.mul_le_mul_left 4 hNsquare) hpack
    omega
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hmposNat)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrange := prophetLevel_log_range hNnat (by simpa [N] using hm)
  have hLreal : (0 : ℝ) < L := by
    have hleft : 0 < Real.log (m : ℝ) / (2 * Real.log 2) := by positivity
    have : (0 : ℝ) < prophetLevel N m := hleft.trans hrange
    simpa [L] using this
  have hD : 0 < 3 * prophetKappa r * (N : ℝ) :=
    mul_pos (mul_pos (by norm_num) (prophetKappa_pos r)) hNreal
  have hDL : 0 < 3 * prophetKappa r * (N : ℝ) * (L : ℝ) := mul_pos hD hLreal
  have hA : 0 < prophetA r := prophetA_pos r
  have hrange' : Real.log (m : ℝ) < 2 * Real.log 2 * (L : ℝ) := by
    have hden : 0 < 2 * Real.log 2 := by positivity
    have := (div_lt_iff₀ hden).mp hrange
    simpa [L, mul_comm, mul_left_comm, mul_assoc] using this
  have hBmul : prophetB r *
      (3 * prophetKappa r * (N : ℝ) * (L : ℝ)) =
        4 * prophetA r * Real.log 2 * (L : ℝ) := by
    have hNprop : (prophetN r : ℝ) ≠ 0 := by
      simpa [N] using hNreal.ne'
    dsimp [prophetB, N]
    field_simp [(prophetKappa_pos r).ne', hNprop]
  dsimp only [N, L] at hDL hBmul hrange' ⊢
  rw [div_lt_div_iff₀ hDL hlogm, hBmul]
  have hscaled := mul_lt_mul_of_pos_left hrange' (by positivity : 0 < 2 * prophetA r)
  nlinarith

/-! ## Internal upper construction -/

/-- The concrete binary separator block, with the notation for `κ_r` used in this module. -/
noncomputable def canonicalProphetHardBlock (r n : ℕ) (hr : 1 ≤ r)
    (hn : max 6 (2 * r) ≤ n) :
    ProphetHardBlock r n (prophetKappa r) := by
  simpa [prophetKappa, orderStatisticKappa] using
    binaryProphetHardBlock r n hr hn

/-- The concrete hard blocks at every packed dyadic level. -/
noncomputable def canonicalProphetHardBlocks (r N L : ℕ) (hr : 1 ≤ r)
    (hN : max 6 (2 * r) ≤ N) :
    ∀ j : Fin L,
      ProphetHardBlock r (prophetBlockSize N j.1) (prophetKappa r) := fun j ↦ by
  apply canonicalProphetHardBlock r (prophetBlockSize N j.1) hr
  apply hN.trans
  rw [prophetBlockSize]
  calc
    N = N * 1 := by simp
    _ ≤ N * 2 ^ j.1 := Nat.mul_le_mul_left N (one_le_pow₀ (by norm_num))

/-- For every moment-based single-selection policy, the fully explicit block-switch family
contains an instance witnessing the upper half of `thm:prophet`.  The order-statistic
benchmark is kept on the right as a product and is never used as a divisor. -/
theorem prophet_upper_witness (r : ℕ) (hr : 1 ≤ r) :
    ∃ b : ℝ, 0 < b ∧ ∃ m₀ : ℕ, ∃ hrm₀ : r ≤ m₀, ∃ hm₀ : 2 ≤ m₀,
      ∀ (m : ℕ) (hm : m₀ ≤ m), ∀ policy : ProphetPolicy m,
        ∃ laws : Fin m → Distribution,
          (∀ i, HasFiniteMoments (laws i)) ∧
          prophetExpectedReward policy laws ≤
            (b / Real.log m) *
              orderStatisticBenchmark (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) laws := by
  let N := prophetN r
  let m₀ := max r (4 * N ^ 2)
  have hNone : 1 ≤ N := by
    dsimp [N]
    exact (by omega : 1 ≤ 6).trans (six_le_prophetN r)
  have hNsquare : 1 ≤ N ^ 2 := one_le_pow₀ (Nat.zero_lt_of_lt hNone)
  have hfour : 2 ≤ 4 * N ^ 2 := by
    exact (by omega : 2 ≤ 4).trans (Nat.mul_le_mul_left 4 hNsquare)
  refine ⟨prophetB r, prophetB_pos r, m₀, le_max_left _ _,
    hfour.trans (le_max_right _ _), ?_⟩
  intro m hm policy
  have hrm : r ≤ m := (le_max_left r (4 * N ^ 2)).trans hm
  have hpackFour : 4 * N ^ 2 ≤ m := (le_max_right r (4 * N ^ 2)).trans hm
  let L := prophetLevel N m
  have hNpos : 0 < N := Nat.zero_lt_of_lt hNone
  have hmgt : 1 < m := by
    have hbase : 4 ≤ 4 * N ^ 2 := Nat.mul_le_mul_left 4 hNsquare
    omega
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hmgt)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlevelRange : Real.log (m : ℝ) / (2 * Real.log 2) <
      (prophetLevel N m : ℝ) := prophetLevel_log_range hNone hpackFour
  have hLposReal : (0 : ℝ) < L := by
    have hleft : 0 < Real.log (m : ℝ) / (2 * Real.log 2) := by positivity
    have : (0 : ℝ) < prophetLevel N m := hleft.trans hlevelRange
    simpa [L] using this
  have hLone : 1 ≤ L := by exact_mod_cast hLposReal
  have hpacked : prophetBlockStart N L ≤ m := by
    simpa [prophetBlockStart, L] using prophetLevel_packing (m := m) hNone
  have hNbase : max 6 (2 * r) ≤ N :=
    max_le (six_le_prophetN r) (two_mul_le_prophetN r)
  let blocks := canonicalProphetHardBlocks r N L hr hNbase
  obtain ⟨t, ht⟩ := exists_hardSwitch_policy_upper hNpos hLone hpacked hrm
    (prophetKappa_pos r) blocks policy
  let laws := prophetSwitchLaws m N L (hardBlockPairs blocks) t
  refine ⟨laws, ?_, ?_⟩
  · intro i
    exact prophetSwitchLaws_hasFiniteMoments (hardBlockPairs blocks) t i
  · have hcoefficient :
        2 * (6 * (N : ℝ) + 3 + 12 / (N : ℝ)) /
            (3 * prophetKappa r * (N : ℝ) * (L : ℝ)) ≤
          prophetB r / Real.log m := by
      have hstrict := prophet_hard_coefficient_lt r m (by simpa [N] using hpackFour)
      simpa [prophetA, N, L] using hstrict.le
    have hbenchmark : 0 ≤
        orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) laws :=
      orderStatisticBenchmark_nonneg _ _
    calc
      prophetExpectedReward policy laws ≤
          (2 * (6 * (N : ℝ) + 3 + 12 / (N : ℝ)) /
            (3 * prophetKappa r * (N : ℝ) * (L : ℝ))) *
            orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) laws := by
              simpa [laws, blocks] using ht
      _ ≤ (prophetB r / Real.log m) *
            orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) laws :=
        mul_le_mul_of_nonneg_right hcoefficient hbenchmark

/-- Fully internal upper half of `thm:prophet`, stated directly for the universal-guarantee
constant `rhoMom`. -/
theorem prophet_upper_bound (r : ℕ) (hr : 1 ≤ r) :
    ∃ b : ℝ, 0 < b ∧ ∃ m₀ : ℕ, ∃ hrm₀ : r ≤ m₀, ∃ hm₀ : 2 ≤ m₀,
      ∀ (m : ℕ) (hm : m₀ ≤ m),
        rhoMom (⟨r, hr, hrm₀.trans hm⟩ : ValidRank m) ≤ b / Real.log m := by
  let N := prophetN r
  let m₀ := max r (4 * N ^ 2)
  have hNbase : max 6 (2 * r) ≤ N :=
    max_le (six_le_prophetN r) (two_mul_le_prophetN r)
  have hNone : 1 ≤ N := (by omega : 1 ≤ 6).trans (hNbase.trans' (le_max_left _ _))
  have hNsquare : 1 ≤ N ^ 2 := one_le_pow₀ (Nat.zero_lt_of_lt hNone)
  have hm₀two : 2 ≤ m₀ := by
    exact ((by omega : 2 ≤ 4).trans (Nat.mul_le_mul_left 4 hNsquare)).trans
      (le_max_right _ _)
  refine ⟨prophetB r, prophetB_pos r, m₀, le_max_left _ _, hm₀two, ?_⟩
  intro m hm
  have hrm : r ≤ m := (le_max_left r (4 * N ^ 2)).trans hm
  have hpackFour : 4 * N ^ 2 ≤ m := (le_max_right r (4 * N ^ 2)).trans hm
  let L := prophetLevel N m
  have hNpos : 0 < N := Nat.zero_lt_of_lt hNone
  have hmgt : 1 < m := by
    have hbase : 4 ≤ 4 * N ^ 2 := Nat.mul_le_mul_left 4 hNsquare
    omega
  have hLposReal : (0 : ℝ) < L := by
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hmgt)
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hleft : 0 < Real.log (m : ℝ) / (2 * Real.log 2) := by positivity
    have hlevelRange := prophetLevel_log_range hNone hpackFour
    have : (0 : ℝ) < prophetLevel N m := hleft.trans hlevelRange
    simpa [L] using this
  have hLone : 1 ≤ L := by exact_mod_cast hLposReal
  have hpacked : prophetBlockStart N L ≤ m := by
    simpa [prophetBlockStart, L] using prophetLevel_packing (m := m) hNone
  let blocks := canonicalProphetHardBlocks r N L hr hNbase
  have hraw := rhoMom_le_of_hardBlocks hNpos hLone hpacked hr hrm
    (prophetKappa_pos r) blocks
  exact hraw.trans (by
    have hstrict := prophet_hard_coefficient_lt r m (by simpa [N] using hpackFour)
    simpa [prophetA, N, L] using hstrict.le)

/-- Compatibility helper for `thm:prophet`, retaining an explicit
`CorreaLogLowerBound` parameter. -/
theorem prophet_of_external (hCorrea : External.CorreaLogLowerBound)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ m₀ : ℕ, ∃ hm₀ : max r 2 ≤ m₀, ∀ (m : ℕ) (hm : m₀ ≤ m),
        a / Real.log m ≤ rhoMom
          (⟨r, hr, (le_max_left r 2).trans (hm₀.trans hm)⟩ : ValidRank m) ∧
        rhoMom (⟨r, hr, (le_max_left r 2).trans (hm₀.trans hm)⟩ : ValidRank m) ≤
          b / Real.log m := by
  obtain ⟨a, ha, ml, hrl, h2l, hlower⟩ :=
    prophet_log_lower_bound_rank_of_external hCorrea r hr
  obtain ⟨b, hb, mu, hru, h2u, hupper⟩ := prophet_upper_bound r hr
  let m₀ := max ml mu
  refine ⟨a, b, ha, hb, m₀, ?_, ?_⟩
  · apply max_le
    · exact hrl.trans (le_max_left _ _)
    · exact h2l.trans (le_max_left _ _)
  · intro m hm
    exact ⟨hlower m ((le_max_left ml mu).trans hm),
      hupper m ((le_max_right ml mu).trans hm)⟩

/-- `thm:prophet`, `sections/prophet.tex`, now fully verified: both the logarithmic lower and
upper directions are internal. -/
theorem prophet (r : ℕ) (hr : 1 ≤ r) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ m₀ : ℕ, ∃ hm₀ : max r 2 ≤ m₀, ∀ (m : ℕ) (hm : m₀ ≤ m),
        a / Real.log m ≤ rhoMom
          (⟨r, hr, (le_max_left r 2).trans (hm₀.trans hm)⟩ : ValidRank m) ∧
        rhoMom (⟨r, hr, (le_max_left r 2).trans (hm₀.trans hm)⟩ : ValidRank m) ≤
          b / Real.log m :=
  prophet_of_external correaLogLowerBound r hr

end

end MomentAmbiguity
