import MomentAmbiguity.SeriesBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
Coefficient and entire-product machinery for the residue-class separator.

The finite products and their coefficients are defined independently.  The expansion theorem
below identifies them exactly.  The analytic infinite product is the locally uniform limit of
the finite products; this is the Lean translation of the manuscript's displayed definition of
`G_N`.
-/

open scoped BigOperators Topology

namespace MomentAmbiguity

open Complex Filter Finset Set

/-- A length-`M+1` digit configuration, with every digit in `{0,...,N-1}`. -/
abbrev FiniteDigitConfig (N M : ℕ) := Fin (M + 1) → Fin N

/-- Total degree of a finite digit configuration. -/
def finiteDigitTotal {N M : ℕ} (c : FiniteDigitConfig N M) : ℕ :=
  ∑ m, (c m : ℕ)

/-- The exponent `∑_m m c_m` of `B⁻¹` contributed by a digit configuration. -/
def finiteDigitExponent {N M : ℕ} (c : FiniteDigitConfig N M) : ℕ :=
  ∑ m : Fin (M + 1), (m : ℕ) * (c m : ℕ)

/-- A manuscript infinite digit configuration is represented by a `Finsupp`; finite support is
therefore part of the type rather than a separately carried proposition.  The two fields encode
`c_m ∈ {0,…,N-1}` and `∑_m c_m = j` exactly. -/
structure InfiniteDigitConfig (N j : ℕ) where
  digits : ℕ →₀ ℕ
  digit_lt : ∀ m, digits m < N
  total_eq : digits.sum (fun _ u ↦ u) = j

@[ext] theorem InfiniteDigitConfig.ext {N j : ℕ} {c d : InfiniteDigitConfig N j}
    (h : c.digits = d.digits) : c = d := by
  cases c
  cases d
  simp_all

/-- The finite exponent `∑_m m c_m` of an infinite (finitely supported) digit
configuration. -/
def InfiniteDigitConfig.exponent {N j : ℕ} (c : InfiniteDigitConfig N j) : ℕ :=
  c.digits.sum (fun m u ↦ m * u)

/-- Extend a finite digit tuple by zero outside its cutoff. -/
noncomputable def finiteDigitConfigFinsupp {N M : ℕ}
    (c : FiniteDigitConfig N M) : ℕ →₀ ℕ :=
  Finsupp.embDomain ⟨Fin.val, Fin.val_injective⟩
    (Finsupp.equivFunOnFinite.symm (fun m ↦ (c m : ℕ)))

@[simp] theorem finiteDigitConfigFinsupp_apply {N M : ℕ}
    (c : FiniteDigitConfig N M) (m : Fin (M + 1)) :
    finiteDigitConfigFinsupp c m.val = (c m : ℕ) := by
  let e : Fin (M + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let v : Fin (M + 1) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i ↦ (c i : ℕ))
  change Finsupp.embDomain e v (e m) = (c m : ℕ)
  rw [Finsupp.embDomain_apply_self]
  rfl

theorem finiteDigitConfigFinsupp_total {N M : ℕ}
    (c : FiniteDigitConfig N M) :
    (finiteDigitConfigFinsupp c).sum (fun _ u ↦ u) = finiteDigitTotal c := by
  rw [finiteDigitConfigFinsupp, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype]
  · rfl
  · simp

theorem finiteDigitConfigFinsupp_exponent {N M : ℕ}
    (c : FiniteDigitConfig N M) :
    (finiteDigitConfigFinsupp c).sum (fun m u ↦ m * u) = finiteDigitExponent c := by
  rw [finiteDigitConfigFinsupp, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype]
  · rfl
  · simp

theorem finiteDigitConfigFinsupp_injective {N M : ℕ} :
    Function.Injective
      (finiteDigitConfigFinsupp : FiniteDigitConfig N M → ℕ →₀ ℕ) := by
  intro c d hcd
  funext m
  apply Fin.ext
  have hm := DFunLike.congr_fun hcd m.val
  simpa only [finiteDigitConfigFinsupp_apply] using hm

/-- Finite configurations of total degree `j`, the indexing set in part (ii) of
`lem:N-class-coeff-formula`. -/
abbrev BoundedDigitConfig (N M j : ℕ) :=
  {c : FiniteDigitConfig N M // finiteDigitTotal c = j}

/-- Regard a bounded configuration as an infinite finitely supported one by extending it by
zero. -/
noncomputable def BoundedDigitConfig.toInfinite {N M j : ℕ} (hN : 1 ≤ N)
    (c : BoundedDigitConfig N M j) : InfiniteDigitConfig N j where
  digits := finiteDigitConfigFinsupp c.1
  digit_lt := by
    intro m
    rw [finiteDigitConfigFinsupp, Finsupp.embDomain_apply]
    split_ifs with hm
    · simpa using (c.1 hm.choose).isLt
    · omega
  total_eq := (finiteDigitConfigFinsupp_total c.1).trans c.2

theorem BoundedDigitConfig.toInfinite_injective {N M j : ℕ} (hN : 1 ≤ N) :
    Function.Injective (BoundedDigitConfig.toInfinite hN :
      BoundedDigitConfig N M j → InfiniteDigitConfig N j) := by
  intro c d hcd
  apply Subtype.ext
  apply finiteDigitConfigFinsupp_injective
  exact congrArg InfiniteDigitConfig.digits hcd

@[simp] theorem BoundedDigitConfig.toInfinite_exponent {N M j : ℕ} (hN : 1 ≤ N)
    (c : BoundedDigitConfig N M j) :
    (c.toInfinite hN).exponent = finiteDigitExponent c.1 := by
  exact finiteDigitConfigFinsupp_exponent c.1

/-- The nonnegative weight of an admissible infinite digit configuration. -/
noncomputable def infiniteDigitConfigWeight (B : ℕ) {N j : ℕ}
    (c : InfiniteDigitConfig N j) : ℝ :=
  (B : ℝ) ^ (-(c.exponent : ℤ))

/-- The factor `∑_{u=0}^{N-1}(z B^{-m})^u`. -/
noncomputable def nwayFactor (B N m : ℕ) (z : ℂ) : ℂ :=
  ∑ u : Fin N, (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)

/-- The manuscript's finite product `G_{N,M}`. -/
noncomputable def nwayFiniteProduct (B N M : ℕ) (z : ℂ) : ℂ :=
  ∏ m : Fin (M + 1), nwayFactor B N m z

/-- The finite coefficient obtained by expanding `G_{N,M}`. -/
noncomputable def nwayFiniteCoeff (B N M j : ℕ) : ℝ :=
  ∑ c : FiniteDigitConfig N M,
    if finiteDigitTotal c = j then (B : ℝ) ^ (-(finiteDigitExponent c : ℤ)) else 0

lemma nwayFiniteCoeff_nonneg (B N M j : ℕ) : 0 ≤ nwayFiniteCoeff B N M j := by
  classical
  unfold nwayFiniteCoeff
  exact sum_nonneg fun c _ ↦ by split <;> positivity

/-- Exact finite coefficient formula, item (ii) of `lem:N-class-coeff-formula`. -/
theorem nwayFiniteCoeff_formula (B N M j : ℕ) :
    nwayFiniteCoeff B N M j =
      ∑ c : FiniteDigitConfig N M,
        if finiteDigitTotal c = j then
          (B : ℝ) ^ (-(finiteDigitExponent c : ℤ)) else 0 := by
  rfl

/-- The finite set of infinite configurations supported in the first `M+1` coordinates.
It is presented as the injective image of the bounded tuples. -/
noncomputable def boundedDigitConfigSet (N j : ℕ) (hN : 1 ≤ N) (M : ℕ) :
    Finset (InfiniteDigitConfig N j) := by
  classical
  exact Finset.univ.image
    (@BoundedDigitConfig.toInfinite N M j hN)

/-- The cutoff configuration sum is exactly the finite Taylor coefficient. -/
theorem sum_boundedDigitConfigSet_eq_nwayFiniteCoeff
    (B N M j : ℕ) (hN : 1 ≤ N) :
    ∑ c ∈ boundedDigitConfigSet N j hN M, infiniteDigitConfigWeight B c =
      nwayFiniteCoeff B N M j := by
  classical
  rw [boundedDigitConfigSet, Finset.sum_image
    (BoundedDigitConfig.toInfinite_injective hN).injOn]
  simp only [infiniteDigitConfigWeight, BoundedDigitConfig.toInfinite_exponent]
  rw [nwayFiniteCoeff, ← Finset.sum_filter]
  symm
  exact Finset.sum_subtype
    (Finset.univ.filter (fun c : FiniteDigitConfig N M ↦ finiteDigitTotal c = j))
    (by simp) _

theorem mem_boundedDigitConfigSet_iff_support_subset
    {N j M : ℕ} (hN : 1 ≤ N) (c : InfiniteDigitConfig N j) :
    c ∈ boundedDigitConfigSet N j hN M ↔ c.digits.support ⊆ Finset.range (M + 1) := by
  classical
  constructor
  · intro hc
    rw [boundedDigitConfigSet] at hc
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hc
    intro m hm
    change m ∈ (finiteDigitConfigFinsupp d.1).support at hm
    rw [finiteDigitConfigFinsupp, Finsupp.support_embDomain] at hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hm
    exact Finset.mem_range.mpr i.isLt
  · intro hsupp
    let d : FiniteDigitConfig N M := fun i ↦ ⟨c.digits i.val, c.digit_lt i.val⟩
    have hdigits : finiteDigitConfigFinsupp d = c.digits := by
      apply Finsupp.ext
      intro m
      by_cases hm : m < M + 1
      · let i : Fin (M + 1) := ⟨m, hm⟩
        have hi := finiteDigitConfigFinsupp_apply d i
        simpa [d, i] using hi
      · have hm_support : m ∉ c.digits.support := by
          intro hmem
          exact hm (Finset.mem_range.mp (hsupp hmem))
        have hc0 : c.digits m = 0 := Finsupp.notMem_support_iff.mp hm_support
        have hd0 : finiteDigitConfigFinsupp d m = 0 := by
          rw [finiteDigitConfigFinsupp]
          apply Finsupp.embDomain_notin_range
          rintro ⟨i, rfl⟩
          exact hm i.isLt
        rw [hd0, hc0]
    have htotal : finiteDigitTotal d = j := by
      have h := finiteDigitConfigFinsupp_total d
      rw [hdigits, c.total_eq] at h
      exact h.symm
    let e : BoundedDigitConfig N M j := ⟨d, htotal⟩
    rw [boundedDigitConfigSet]
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_univ _, ?_⟩
    apply InfiniteDigitConfig.ext
    exact hdigits

theorem monotone_boundedDigitConfigSet (N j : ℕ) (hN : 1 ≤ N) :
    Monotone (boundedDigitConfigSet N j hN) := by
  intro M K hMK c hc
  rw [mem_boundedDigitConfigSet_iff_support_subset hN] at hc ⊢
  exact hc.trans (Finset.range_mono (by omega))

/-- Every finite collection of infinite digit configurations is contained in one cutoff set.
This is the cofinality fact needed to identify the ordinary `tsum` with the manuscript's
monotone union of finite configuration sums. -/
theorem boundedDigitConfigSet_cofinal (N j : ℕ) (hN : 1 ≤ N)
    (s : Finset (InfiniteDigitConfig N j)) :
    ∃ M, s ⊆ boundedDigitConfigSet N j hN M := by
  classical
  let supportUnion : Finset ℕ := s.biUnion (fun c ↦ c.digits.support)
  obtain ⟨K, hK⟩ := Finset.exists_nat_subset_range supportUnion
  refine ⟨K, fun c hc ↦ ?_⟩
  rw [mem_boundedDigitConfigSet_iff_support_subset hN]
  intro m hm
  have hmU : m ∈ supportUnion := by
    exact Finset.mem_biUnion.mpr ⟨c, hc, hm⟩
  have hmK : m ∈ Finset.range K := hK hmU
  exact Finset.mem_range.mpr (Nat.lt.step (Finset.mem_range.mp hmK))

theorem tendsto_boundedDigitConfigSet_atTop (N j : ℕ) (hN : 1 ≤ N) :
    Tendsto (boundedDigitConfigSet N j hN) atTop atTop := by
  rw [tendsto_atTop]
  intro s
  obtain ⟨M, hM⟩ := boundedDigitConfigSet_cofinal N j hN s
  exact eventually_atTop.2
    ⟨M, fun K hMK ↦ hM.trans (monotone_boundedDigitConfigSet N j hN hMK)⟩

/-- `lem:N-class-coeff-formula` (iii), monotonicity: appending a zero digit embeds every
configuration contributing at cutoff `M` into the configurations at cutoff `M+1`, without
changing its total degree or its weight. -/
theorem nwayFiniteCoeff_mono_succ (B N M j : ℕ) (hN : 1 ≤ N) :
    nwayFiniteCoeff B N M j ≤ nwayFiniteCoeff B N (M + 1) j := by
  classical
  let z : Fin N := ⟨0, hN⟩
  let extend : FiniteDigitConfig N M → FiniteDigitConfig N (M + 1) :=
    fun c ↦ Fin.snoc c z
  let termM : FiniteDigitConfig N M → ℝ := fun c ↦
    if finiteDigitTotal c = j then
      (B : ℝ) ^ (-(finiteDigitExponent c : ℤ)) else 0
  let termS : FiniteDigitConfig N (M + 1) → ℝ := fun c ↦
    if finiteDigitTotal c = j then
      (B : ℝ) ^ (-(finiteDigitExponent c : ℤ)) else 0
  have hextend : Function.Injective extend := by
    intro c d hcd
    funext i
    have hi := congrFun hcd i.castSucc
    simpa [extend] using hi
  have htotal (c : FiniteDigitConfig N M) :
      finiteDigitTotal (extend c) = finiteDigitTotal c := by
    simp [extend, finiteDigitTotal, Fin.sum_univ_castSucc, z]
  have hexponent (c : FiniteDigitConfig N M) :
      finiteDigitExponent (extend c) = finiteDigitExponent c := by
    simp [extend, finiteDigitExponent, Fin.sum_univ_castSucc, z]
  have hterm (c : FiniteDigitConfig N M) : termS (extend c) = termM c := by
    simp [termS, termM, htotal c, hexponent c]
  rw [nwayFiniteCoeff, nwayFiniteCoeff]
  change (∑ c, termM c) ≤ ∑ c, termS c
  calc
    (∑ c, termM c) = ∑ d ∈ Finset.univ.image extend, termS d := by
      rw [Finset.sum_image hextend.injOn]
      exact Finset.sum_congr rfl (fun c _ ↦ (hterm c).symm)
    _ ≤ ∑ d ∈ (Finset.univ : Finset (FiniteDigitConfig N (M + 1))), termS d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      intro d hdU hdI
      simp only [termS]
      split <;> positivity
    _ = ∑ c, termS c := by simp

/-- `lem:N-class-coeff-formula` (iii): for fixed degree, the finite digit coefficient is a
nondecreasing sequence of cutoffs. -/
theorem monotone_nwayFiniteCoeff (B N j : ℕ) (hN : 1 ≤ N) :
    Monotone (fun M ↦ nwayFiniteCoeff B N M j) := by
  exact monotone_nat_of_le_succ (nwayFiniteCoeff_mono_succ B N · j hN)

/-- The distributive expansion of the finite product over bounded digit configurations. -/
theorem nwayFiniteProduct_expand_raw (B N M : ℕ) (z : ℂ) :
    nwayFiniteProduct B N M z =
      ∑ c : FiniteDigitConfig N M,
        ∏ m : Fin (M + 1),
          (z * (B : ℂ)⁻¹ ^ (m : ℕ)) ^ (c m : ℕ) := by
  classical
  exact Fintype.prod_sum _

/-- The raw digit expansion, collected into a monomial for each configuration. -/
theorem nwayFiniteProduct_expand (B N M : ℕ) (z : ℂ) :
    nwayFiniteProduct B N M z =
      ∑ c : FiniteDigitConfig N M,
        (B : ℂ) ^ (-(finiteDigitExponent c : ℤ)) * z ^ finiteDigitTotal c := by
  rw [nwayFiniteProduct_expand_raw]
  apply sum_congr rfl
  intro c hc
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hzprod : ∏ m : Fin (M + 1), z ^ (c m : ℕ) =
      z ^ ∑ m : Fin (M + 1), (c m : ℕ) := by
    simpa using Finset.prod_pow_eq_pow_sum Finset.univ (fun m : Fin (M + 1) ↦ (c m : ℕ)) z
  rw [hzprod]
  have hz : ∑ m : Fin (M + 1), (c m : ℕ) = finiteDigitTotal c := rfl
  rw [hz]
  have hB : ∏ m : Fin (M + 1), ((B : ℂ)⁻¹ ^ (m : ℕ)) ^ (c m : ℕ) =
      (B : ℂ) ^ (-(finiteDigitExponent c : ℤ)) := by
    simp only [← pow_mul, inv_pow]
    rw [Finset.prod_inv_distrib]
    have hp : ∏ m : Fin (M + 1), (B : ℂ) ^ ((m : ℕ) * (c m : ℕ)) =
        (B : ℂ) ^ finiteDigitExponent c := by
      simpa [finiteDigitExponent] using
        Finset.prod_pow_eq_pow_sum Finset.univ
          (fun m : Fin (M + 1) ↦ (m : ℕ) * (c m : ℕ)) (B : ℂ)
    rw [hp, zpow_neg, zpow_natCast]
  rw [hB, mul_comm]

/-- Finite Taylor coefficients are exactly the finite digit sums in
`lem:N-class-coeff-formula`. -/
theorem iteratedDeriv_nwayFiniteProduct_zero (B N M j : ℕ) :
    iteratedDeriv j (nwayFiniteProduct B N M) 0 =
      (j.factorial : ℂ) * nwayFiniteCoeff B N M j := by
  rw [show nwayFiniteProduct B N M = fun z ↦
      ∑ c : FiniteDigitConfig N M,
        (B : ℂ) ^ (-(finiteDigitExponent c : ℤ)) * z ^ finiteDigitTotal c by
        funext z; exact nwayFiniteProduct_expand B N M z]
  rw [iteratedDeriv_fun_sum (fun _ _ ↦ by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [nwayFiniteCoeff]
  push_cast
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro c hc
  by_cases h : finiteDigitTotal c = j
  · subst j
    simp [mul_comm]
  · have hn : j ≠ finiteDigitTotal c := Ne.symm h
    simp [h, hn]

/-- The nonconstant tail of a factor. -/
noncomputable def nwayFactorTail (B N m : ℕ) (z : ℂ) : ℂ :=
  ∑ u : Fin N, if (u : ℕ) = 0 then 0 else
    (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)

lemma nwayFactor_eq_one_add_tail (B N m : ℕ) (hN : 1 ≤ N) (z : ℂ) :
    nwayFactor B N m z = 1 + nwayFactorTail B N m z := by
  classical
  let z₀ : Fin N := ⟨0, hN⟩
  rw [nwayFactor, nwayFactorTail, show (∑ u : Fin N,
      (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)) =
      ∑ u : Fin N,
        ((if (u : ℕ) = 0 then (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ) else 0) +
         (if (u : ℕ) = 0 then 0 else (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ))) by
        apply sum_congr rfl
        intro u hu
        split <;> simp_all]
  rw [sum_add_distrib]
  have hz : ∑ u : Fin N,
      (if (u : ℕ) = 0 then (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ) else 0) = 1 := by
    rw [Fintype.sum_eq_single z₀]
    · simp [z₀]
    · intro u hne
      simp only [ite_eq_right_iff]
      intro hu
      exact (hne (Fin.ext hu)).elim
  rw [hz]

lemma continuous_nwayFactorTail (B N m : ℕ) : Continuous (nwayFactorTail B N m) := by
  unfold nwayFactorTail
  classical
  apply continuous_finset_sum
  intro u hu
  by_cases hu0 : (u : ℕ) = 0
  · simpa [hu0] using (continuous_const : Continuous (fun _ : ℂ ↦ (0 : ℂ)))
  · simp only [hu0, ↓reduceIte]
    fun_prop

lemma differentiable_nwayFactor (B N m : ℕ) : Differentiable ℂ (nwayFactor B N m) := by
  unfold nwayFactor
  fun_prop

/-- A geometric majorant for the factor tails on a closed disk. -/
lemma norm_nwayFactorTail_le (B N m : ℕ) (hB : 2 ≤ B) {R : ℝ}
    (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖nwayFactorTail B N m z‖ ≤
      ∑ u : Fin N, if (u : ℕ) = 0 then 0 else
        R ^ (u : ℕ) * (1 / (B : ℝ)) ^ (m * (u : ℕ)) := by
  classical
  rw [nwayFactorTail]
  calc
    ‖∑ u : Fin N, if (u : ℕ) = 0 then 0 else
        (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)‖ ≤
        ∑ u : Fin N, ‖if (u : ℕ) = 0 then 0 else
          (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ u : Fin N, if (u : ℕ) = 0 then 0 else
        R ^ (u : ℕ) * (1 / (B : ℝ)) ^ (m * (u : ℕ)) := by
      apply sum_le_sum
      intro u hu
      split_ifs with hu0
      · simp
      · simp only [norm_pow, norm_mul, norm_inv, norm_natCast, norm_pow, one_div]
        rw [mul_pow, pow_mul]
        gcongr

/-- `lem:N-class-coeff-formula` (i): the defining product converges locally uniformly on
`ℂ`.  The limit is given by the unconditional infinite product `tprod`. -/
theorem nway_hasProdLocallyUniformly (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    HasProdLocallyUniformly
      (fun m z ↦ nwayFactor B N m z)
      (fun z ↦ ∏' m : ℕ, nwayFactor B N m z) := by
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  obtain ⟨R, hR₀, hKR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨max R 0, le_max_right _ _, fun z hz ↦ ?_⟩
    have hzR : dist z 0 ≤ R := by
      simpa [Metric.mem_closedBall] using hR hz
    have hnorm : ‖z‖ ≤ R := by simpa [dist_zero_right] using hzR
    exact hnorm.trans (le_max_left _ _)
  let U : ℕ → ℝ := fun m ↦ ∑ u : Fin N, if (u : ℕ) = 0 then 0 else
    R ^ (u : ℕ) * (1 / (B : ℝ)) ^ (m * (u : ℕ))
  have hgeom : Summable U := by
    unfold U
    apply summable_sum
    intro u hu
    by_cases hu0 : (u : ℕ) = 0
    · simp [hu0]
    · simp only [hu0, ↓reduceIte]
      rw [show (fun m : ℕ ↦ R ^ (u : ℕ) * (1 / (B : ℝ)) ^ (m * (u : ℕ))) =
          fun m ↦ R ^ (u : ℕ) * ((1 / (B : ℝ)) ^ (u : ℕ)) ^ m by
          funext m; rw [Nat.mul_comm m (u : ℕ), ← pow_mul]]
      apply Summable.mul_left
      apply summable_geometric_of_lt_one (by positivity)
      have hq : 0 ≤ (1 / (B : ℝ)) ∧ (1 / (B : ℝ)) < 1 := by
        constructor
        · positivity
        · exact (div_lt_one (show (0 : ℝ) < B by positivity)).2
            (by exact_mod_cast (show 1 < B by omega))
      exact pow_lt_one₀ hq.1 hq.2 (by omega)
  have htail : ∀ᶠ m in atTop, ∀ z ∈ K,
      ‖nwayFactorTail B N m z‖ ≤ U m := by
    filter_upwards [] with m z hz
    exact norm_nwayFactorTail_le B N m hB hR₀ (hKR z hz)
  simpa only [nwayFactor_eq_one_add_tail B N _ (by omega : 1 ≤ N)] using
    hgeom.hasProdUniformlyOn_nat_one_add hK htail
      (fun m ↦ (continuous_nwayFactorTail B N m).continuousOn)

/-- The locally uniform product limit is entire. -/
theorem differentiable_nwayInfiniteProduct (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Differentiable ℂ (fun z ↦ ∏' m : ℕ, nwayFactor B N m z) := by
  have hconv := (nway_hasProdLocallyUniformly B N hB hN).tendstoLocallyUniformly_finsetRange
  rw [← tendstoLocallyUniformlyOn_univ] at hconv
  have hdiff : ∀ᶠ M : ℕ in atTop,
      DifferentiableOn ℂ (fun z ↦ ∏ m ∈ range M, nwayFactor B N m z) univ := by
    filter_upwards [] with M
    exact ((Differentiable.fun_finsetProd fun m _ ↦ differentiable_nwayFactor B N m)).differentiableOn
  exact differentiableOn_univ.mp (hconv.differentiableOn hdiff isOpen_univ)

/-- The entire function denoted by `G_N` in the manuscript. -/
noncomputable def nwayInfiniteProduct (B N : ℕ) (z : ℂ) : ℂ :=
  ∏' m : ℕ, nwayFactor B N m z

private theorem nwayFiniteProduct_tendstoLocallyUniformly (B N : ℕ)
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    TendstoLocallyUniformlyOn
      (fun M ↦ nwayFiniteProduct B N M)
      (nwayInfiniteProduct B N) atTop univ := by
  have h := (nway_hasProdLocallyUniformly B N hB hN).tendstoLocallyUniformly_finsetRange
  rw [tendstoLocallyUniformlyOn_univ]
  intro u hu z
  obtain ⟨s, hs, hevent⟩ := h u hu z
  refine ⟨s, hs, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hevent] with M hM
  intro y hy
  change (nwayInfiniteProduct B N y, nwayFiniteProduct B N M y) ∈ u
  rw [nwayInfiniteProduct, nwayFiniteProduct,
    Fin.prod_univ_eq_prod_range (fun m ↦ nwayFactor B N m y) (M + 1)]
  exact hM y hy

private theorem nwayFiniteProduct_iteratedDeriv_tendstoLocallyUniformly
    (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    TendstoLocallyUniformlyOn
      (fun M ↦ iteratedDeriv j (nwayFiniteProduct B N M))
      (iteratedDeriv j (nwayInfiniteProduct B N)) atTop univ := by
  induction j with
  | zero => simpa using nwayFiniteProduct_tendstoLocallyUniformly B N hB hN
  | succ j ih =>
      rw [show (fun M ↦ iteratedDeriv (j + 1) (nwayFiniteProduct B N M)) =
          fun M ↦ deriv (iteratedDeriv j (nwayFiniteProduct B N M)) by
            funext M; rw [iteratedDeriv_succ],
        iteratedDeriv_succ]
      apply ih.deriv
      · filter_upwards [] with M
        have hc : ContDiff ℂ ⊤ (nwayFiniteProduct B N M) := by
          unfold nwayFiniteProduct nwayFactor
          fun_prop
        exact (hc.differentiable_iteratedDeriv j (by simp)).differentiableOn
      · exact isOpen_univ

/-- The complex Taylor coefficient of the entire product at the origin. -/
noncomputable def nwayCoeffC (B N j : ℕ) : ℂ :=
  (j.factorial : ℂ)⁻¹ * iteratedDeriv j (nwayInfiniteProduct B N) 0

/-- The real coefficient `w_j` in `lem:N-class-coeff-formula`. -/
noncomputable def nwayCoeff (B N j : ℕ) : ℝ := (nwayCoeffC B N j).re

/-- Item (iii) of `lem:N-class-coeff-formula`: every finite coefficient converges to the
Taylor coefficient of the locally-uniform product. -/
theorem tendsto_nwayFiniteCoeff (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Tendsto (fun M ↦ (nwayFiniteCoeff B N M j : ℂ)) atTop (𝓝 (nwayCoeffC B N j)) := by
  have hd := (nwayFiniteProduct_iteratedDeriv_tendstoLocallyUniformly B N j hB hN).tendsto_at
    (show (0 : ℂ) ∈ (univ : Set ℂ) by simp)
  have hm := hd.const_mul (j.factorial : ℂ)⁻¹
  have hfun : (fun M ↦ (j.factorial : ℂ)⁻¹ *
      iteratedDeriv j (nwayFiniteProduct B N M) 0) =
      fun M ↦ (nwayFiniteCoeff B N M j : ℂ) := by
    funext M
    rw [iteratedDeriv_nwayFiniteProduct_zero]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)), one_mul]
  rw [← hfun]
  simpa only [nwayCoeffC] using hm

theorem nwayCoeffC_eq_real (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayCoeffC B N j = (nwayCoeff B N j : ℂ) := by
  have hlim := tendsto_nwayFiniteCoeff B N j hB hN
  have him : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (nwayCoeffC B N j).im) := by
    have hi := (Complex.continuous_im.tendsto _).comp hlim
    convert hi using 1
    funext M
    simp
  have him0 : (nwayCoeffC B N j).im = 0 :=
    tendsto_nhds_unique him tendsto_const_nhds
  apply Complex.ext
  · simp [nwayCoeff]
  · simpa [him0]

theorem nwayCoeff_nonneg (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    0 ≤ nwayCoeff B N j := by
  have hlim := (Complex.continuous_re.tendsto _).comp
    (tendsto_nwayFiniteCoeff B N j hB hN)
  have hlim' : Tendsto (fun M ↦ nwayFiniteCoeff B N M j) atTop (𝓝 (nwayCoeff B N j)) := by
    convert hlim using 1
    · funext M
      simp
    · simp [nwayCoeff]
  exact isClosed_Ici.mem_of_tendsto hlim' (Eventually.of_forall fun M ↦
    nwayFiniteCoeff_nonneg B N M j)

/-- Real-valued form of the coefficient convergence in item (iii) of
`lem:N-class-coeff-formula`. -/
theorem tendsto_nwayFiniteCoeff_real (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Tendsto (fun M ↦ nwayFiniteCoeff B N M j) atTop (𝓝 (nwayCoeff B N j)) := by
  have hlim := (Complex.continuous_re.tendsto _).comp
    (tendsto_nwayFiniteCoeff B N j hB hN)
  convert hlim using 1
  · funext M
    simp
  · simp [nwayCoeff]

/-- The manuscript's infinite configuration sum is an ordinary absolutely convergent
`tsum`.  An infinite digit sequence is represented by `InfiniteDigitConfig`, whose `Finsupp`
field makes finite support part of the type. -/
theorem summable_infiniteDigitConfigWeight (B N j : ℕ)
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Summable (infiniteDigitConfigWeight B : InfiniteDigitConfig N j → ℝ) := by
  let w : InfiniteDigitConfig N j → ℝ := infiniteDigitConfigWeight B
  have hw0 : ∀ c, 0 ≤ w c := by
    intro c
    dsimp only [w, infiniteDigitConfigWeight]
    positivity
  apply summable_of_sum_le hw0
  intro s
  obtain ⟨M, hsM⟩ := boundedDigitConfigSet_cofinal N j (by omega) s
  have hsumSubset : ∑ c ∈ s, w c ≤
      ∑ c ∈ boundedDigitConfigSet N j (by omega) M, w c := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsM
      (fun c _hc _hnot ↦ hw0 c)
  have hcutoff :
      ∑ c ∈ boundedDigitConfigSet N j (by omega) M, w c =
        nwayFiniteCoeff B N M j := by
    simpa [w] using sum_boundedDigitConfigSet_eq_nwayFiniteCoeff B N M j (by omega)
  have hcoeffLe : nwayFiniteCoeff B N M j ≤ nwayCoeff B N j := by
    apply ge_of_tendsto (tendsto_nwayFiniteCoeff_real B N j hB hN)
    exact eventually_atTop.2
      ⟨M, fun K hMK ↦ monotone_nwayFiniteCoeff B N j (by omega) hMK⟩
  exact hsumSubset.trans (hcutoff.trans_le hcoeffLe)

/-- `lem:N-class-coeff-formula` (iii), `sections/proofs.tex`: the analytic Taylor
coefficient equals the manuscript sum over all finitely supported digit configurations.
The two displayed source sums with `q = 1/B` and with powers of `B` are definitionally
represented by the integer-power weight `B ^ (-exponent)` below. -/
theorem nwayCoeff_eq_infiniteDigitConfig_tsum (B N j : ℕ)
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayCoeff B N j =
      ∑' c : InfiniteDigitConfig N j, infiniteDigitConfigWeight B c := by
  let w : InfiniteDigitConfig N j → ℝ := infiniteDigitConfigWeight B
  have hs := summable_infiniteDigitConfigWeight B N j hB hN
  have hsum : Tendsto
      (fun M ↦ ∑ c ∈ boundedDigitConfigSet N j (by omega) M, w c)
      atTop (𝓝 (∑' c, w c)) := by
    exact hs.hasSum.comp (tendsto_boundedDigitConfigSet_atTop N j (by omega))
  have hcoeff : Tendsto
      (fun M ↦ ∑ c ∈ boundedDigitConfigSet N j (by omega) M, w c)
      atTop (𝓝 (nwayCoeff B N j)) := by
    convert tendsto_nwayFiniteCoeff_real B N j hB hN using 1
    funext M
    simpa [w] using sum_boundedDigitConfigSet_eq_nwayFiniteCoeff B N M j (by omega)
  simpa [w] using tendsto_nhds_unique hcoeff hsum

/-- Taylor expansion part of `lem:N-class-coeff-formula`. -/
theorem hasSum_nwayCoeff (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (z : ℂ) :
    HasSum (fun j ↦ (nwayCoeff B N j : ℂ) * z ^ j) (nwayInfiniteProduct B N z) := by
  have hTaylor := Complex.hasSum_taylorSeries_of_entire
    (differentiable_nwayInfiniteProduct B N hB hN) 0 z
  change HasSum
    (fun j ↦ (j.factorial : ℂ)⁻¹ • (z - 0) ^ j •
      iteratedDeriv j (nwayInfiniteProduct B N) 0)
    (nwayInfiniteProduct B N z) at hTaylor
  apply hTaylor.congr_fun
  intro j
  rw [← nwayCoeffC_eq_real B N j hB hN]
  simp only [nwayCoeffC, sub_zero, smul_eq_mul]
  ring

/-! ### Residue-class moment matching -/

/-- The factor at the nontrivial Fourier character selected by moment order `t` vanishes. -/
theorem nwayFactor_character_eq_zero
    (B N t : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N)
    (k : ZMod N) (hk : k ≠ 0) :
    nwayFactor B N t (ZMod.stdAddChar (-k) * (B : ℂ) ^ t) = 0 := by
  have hbase : (ZMod.stdAddChar (-k) * (B : ℂ) ^ t) * (B : ℂ)⁻¹ ^ t =
      ZMod.stdAddChar (-k) := by
    rw [inv_pow, mul_assoc, mul_inv_cancel₀]
    · simp
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  rw [nwayFactor]
  simp only [hbase]
  rw [Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
    (fun u : Fin N => ZMod.stdAddChar (-k) ^ (u : ℕ))
    (fun a : ZMod N => (ZMod.stdAddChar.mulShift (-k)) a)]
  · exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar N (neg_ne_zero.mpr hk))
  · intro u
    rw [AddChar.mulShift_apply]
    have he : (ZMod.finEquiv N).toEquiv u = (u.val : ZMod N) := by
      have hNz : N ≠ 0 := NeZero.ne N
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hNz
      subst N
      apply Fin.ext
      change u.val = u.val % (d + 1)
      exact (Nat.mod_eq_of_lt u.isLt).symm
    rw [he, mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

/-- The entire product vanishes at every nontrivial Fourier character. -/
theorem nwayInfiniteProduct_character_eq_zero
    (B N t : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N)
    (k : ZMod N) (hk : k ≠ 0) :
    nwayInfiniteProduct B N (ZMod.stdAddChar (-k) * (B : ℂ) ^ t) = 0 := by
  rw [nwayInfiniteProduct, tprod_of_exists_eq_zero]
  exact ⟨t, nwayFactor_character_eq_zero B N t hB hN k hk⟩

/-- The real summand `w_j B^(tj)` used in the manuscript's `W_h(t)`. -/
noncomputable def nwayMomentTerm (B N t j : ℕ) : ℝ :=
  nwayCoeff B N j * (B : ℝ) ^ (t * j)

theorem nwayMomentTerm_nonneg (B N t j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    0 ≤ nwayMomentTerm B N t j :=
  mul_nonneg (nwayCoeff_nonneg B N j hB hN) (pow_nonneg (by positivity) _)

theorem summable_nwayMomentTerm (B N t : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Summable (nwayMomentTerm B N t) := by
  have hc := hasSum_nwayCoeff B N hB hN ((B : ℂ) ^ t)
  have hr := Complex.hasSum_re hc
  apply hr.summable.congr
  intro j
  simp only [nwayMomentTerm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← pow_mul]
  norm_cast

/-- The absolutely convergent character-twisted moment series. -/
theorem hasSum_nwayTwistedMoment (B N t : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (k : ZMod N) :
    HasSum (fun j : ℕ =>
      ZMod.stdAddChar (-((j : ZMod N) * k)) * (nwayMomentTerm B N t j : ℂ))
      (nwayInfiniteProduct B N (ZMod.stdAddChar (-k) * (B : ℂ) ^ t)) := by
  have hs := hasSum_nwayCoeff B N hB hN
    (ZMod.stdAddChar (-k) * (B : ℂ) ^ t)
  apply hs.congr_fun
  intro j
  rw [nwayMomentTerm]
  push_cast
  rw [mul_pow, ← pow_mul]
  have hchar : ZMod.stdAddChar (-k) ^ j =
      ZMod.stdAddChar (-((j : ZMod N) * k)) := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul]
  rw [hchar]
  ring

/-- The complex form of the residue-class moment sum `W_h(t)`. -/
noncomputable def nwayResidueMomentC (B N t : ℕ) [NeZero N] (h : ZMod N) : ℂ :=
  ∑' m : ℕ, (nwayMomentTerm B N t (h.val + N * m) : ℂ)

theorem dft_nwayResidueMomentC (B N t : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (k : ZMod N) :
    ZMod.dft (fun h : ZMod N => nwayResidueMomentC B N t h) k =
      nwayInfiniteProduct B N (ZMod.stdAddChar (-k) * (B : ℂ) ^ t) := by
  have htw := hasSum_nwayTwistedMoment B N t hB hN k
  rw [ZMod.dft_apply]
  simp only [nwayResidueMomentC, smul_eq_mul]
  calc
    ∑ h : ZMod N, ZMod.stdAddChar (-(h * k)) *
        ∑' m : ℕ, (nwayMomentTerm B N t (h.val + N * m) : ℂ) =
      ∑ h : ZMod N, ∑' m : ℕ,
        ZMod.stdAddChar (-(((h.val + N * m : ℕ) : ZMod N) * k)) *
          (nwayMomentTerm B N t (h.val + N * m) : ℂ) := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [← tsum_mul_left]
            apply tsum_congr
            intro m
            congr 2
            simp
    _ = ∑' j : ℕ, ZMod.stdAddChar (-((j : ZMod N) * k)) *
        (nwayMomentTerm B N t j : ℂ) := by
          rw [Nat.sumByResidueClasses htw.summable N]
    _ = _ := htw.tsum_eq

/-- `lem:N-class-moment-matching`: Fourier inversion makes every residue sum equal. -/
theorem nwayResidueMomentC_eq_common
    (B N t : ℕ) [NeZero N] (hB : 2 ≤ B) (hN : 2 ≤ N) (h : ZMod N) :
    nwayResidueMomentC B N t h =
      (N : ℂ)⁻¹ * nwayInfiniteProduct B N ((B : ℂ) ^ t) := by
  have hinv := congr_fun (ZMod.dft (N := N).symm_apply_apply
    (fun h : ZMod N => nwayResidueMomentC B N t h)) h
  rw [ZMod.invDFT_apply] at hinv
  rw [← hinv]
  congr 1
  rw [Finset.sum_eq_single 0]
  · rw [dft_nwayResidueMomentC B N t hB hN]
    simp
  · intro k hkU hk
    rw [dft_nwayResidueMomentC B N t hB hN,
      nwayInfiniteProduct_character_eq_zero B N t hB hN k hk]
    simp
  · simp

/-- The real residue-class moment sum. -/
noncomputable def nwayResidueMoment (B N t : ℕ) [NeZero N] (h : ZMod N) : ℝ :=
  ∑' m : ℕ, nwayMomentTerm B N t (h.val + N * m)

theorem summable_nwayResidueMoment (B N t : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : ZMod N) :
    Summable (fun m : ℕ => nwayMomentTerm B N t (h.val + N * m)) := by
  exact (summable_nwayMomentTerm B N t hB hN).comp_injective
    (fun _ _ hEq => Nat.mul_left_cancel (by omega) (Nat.add_left_cancel hEq))

theorem nwayResidueMomentC_eq_coe (B N t : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : ZMod N) :
    nwayResidueMomentC B N t h = (nwayResidueMoment B N t h : ℂ) := by
  rw [nwayResidueMomentC, nwayResidueMoment]
  exact (Complex.ofRealCLM.hasSum
    (summable_nwayResidueMoment B N t hB hN h).hasSum).tsum_eq

theorem nwayResidueMoment_eq_common (B N t : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : ZMod N) :
    nwayResidueMoment B N t h =
      (nwayInfiniteProduct B N ((B : ℂ) ^ t)).re / N := by
  have hc := nwayResidueMomentC_eq_common B N t hB hN h
  rw [nwayResidueMomentC_eq_coe B N t hB hN h] at hc
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc' : (N : ℂ) * (nwayResidueMoment B N t h : ℂ) =
      nwayInfiniteProduct B N ((B : ℂ) ^ t) := by
    calc
      (N : ℂ) * (nwayResidueMoment B N t h : ℂ) =
          (N : ℂ) * ((N : ℂ)⁻¹ * nwayInfiniteProduct B N ((B : ℂ) ^ t)) := by
            rw [hc]
      _ = nwayInfiniteProduct B N ((B : ℂ) ^ t) := by
        rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  have hr := congrArg Complex.re hc'
  apply (eq_div_iff (by positivity : (N : ℝ) ≠ 0)).2
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm] using hr

/-! ### Exact normalization bounds -/

lemma nwayFactor_zero (B N m : ℕ) (hN : 1 ≤ N) : nwayFactor B N m 0 = 1 := by
  classical
  let u0 : Fin N := ⟨0, hN⟩
  rw [nwayFactor, Fintype.sum_eq_single u0]
  · simp [u0]
  · intro u hne
    have hu : (u : ℕ) ≠ 0 := fun h => hne (Fin.ext h)
    simp [hu]

@[simp] theorem nwayCoeff_zero (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayCoeff B N 0 = 1 := by
  have hp : nwayInfiniteProduct B N 0 = 1 := by
    rw [nwayInfiniteProduct]
    have hf : (fun m : ℕ => nwayFactor B N m 0) = fun _ => (1 : ℂ) := by
      funext m
      exact nwayFactor_zero B N m (by omega)
    rw [hf]
    simp
  simp [nwayCoeff, nwayCoeffC, hp]

/-- The real value of one product factor at `x=1`. -/
noncomputable def nwayFactorReal (B N m : ℕ) : ℝ :=
  ∑ u : Fin N, (1 / (B : ℝ)) ^ (m * (u : ℕ))

theorem nwayFactorReal_tail_le (B N m : ℕ) (hB : 2 ≤ B) :
    nwayFactorReal B N (m + 1) ≤ (dyadicFactor m)⁻¹ := by
  let q : ℝ := 1 / (B : ℝ)
  let r : ℝ := q ^ (m + 1)
  have hq0 : 0 ≤ q := by positivity
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hB)
  have hr0 : 0 ≤ r := pow_nonneg hq0 _
  have hrlt : r < 1 := by
    apply pow_lt_one₀ hq0
    · exact hqhalf.trans_lt (by norm_num)
    · omega
  have hrdy : r ≤ dyadicTerm m := by
    dsimp [r, dyadicTerm]
    exact pow_le_pow_left₀ hq0 hqhalf _
  have hgeom : nwayFactorReal B N (m + 1) = (r ^ N - 1) / (r - 1) := by
    rw [nwayFactorReal]
    calc
      (∑ u : Fin N, (1 / (B : ℝ)) ^ ((m + 1) * (u : ℕ))) =
          ∑ u : Fin N, r ^ (u : ℕ) := by
            apply Finset.sum_congr rfl
            intro u hu
            simp [r, q, pow_mul]
      _ = ∑ u ∈ Finset.range N, r ^ u := Fin.sum_univ_eq_sum_range _ _
      _ = (r ^ N - 1) / (r - 1) := geom_sum_eq (ne_of_lt hrlt) N
  rw [hgeom]
  have hden : 0 < 1 - r := sub_pos.mpr hrlt
  have hrewrite : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
    rw [show r ^ N - 1 = -(1 - r ^ N) by ring,
      show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
  rw [hrewrite]
  calc
    (1 - r ^ N) / (1 - r) ≤ 1 / (1 - r) :=
      div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 N]) hden.le
    _ = (1 - r)⁻¹ := by rw [one_div]
    _ ≤ (dyadicFactor m)⁻¹ :=
      (inv_le_inv₀ hden (dyadicFactor_pos m)).2 (by
        unfold dyadicFactor
        linarith)

theorem nwayFactor_one_eq_coe (B N m : ℕ) :
    nwayFactor B N m 1 = (nwayFactorReal B N m : ℂ) := by
  rw [nwayFactor, nwayFactorReal]
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  simp only [one_mul, ← pow_mul]
  simp [one_div]

@[simp] theorem nwayFactorReal_zero (B N : ℕ) : nwayFactorReal B N 0 = N := by
  rw [nwayFactorReal]
  simp

/-- Product of the factors after the leading factor `N`. -/
noncomputable def nwayTailPartial (B N M : ℕ) : ℝ :=
  ∏ m ∈ Finset.range M, nwayFactorReal B N (m + 1)

theorem nwayFiniteProduct_one_eq (B N M : ℕ) (hN : 2 ≤ N) :
    nwayFiniteProduct B N M 1 = (N : ℂ) * (nwayTailPartial B N M : ℂ) := by
  rw [nwayFiniteProduct,
    Fin.prod_univ_eq_prod_range (fun m => nwayFactor B N m 1) (M + 1)]
  rw [Finset.prod_range_succ']
  rw [nwayFactor_one_eq_coe, nwayFactorReal_zero]
  rw [nwayTailPartial]
  push_cast
  nth_rw 1 [mul_comm]
  apply congrArg ((N : ℂ) * ·)
  apply Finset.prod_congr rfl
  intro m hm
  exact nwayFactor_one_eq_coe B N (m + 1)

theorem tendsto_nwayTailPartial (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    Tendsto (nwayTailPartial B N) atTop
      (𝓝 ((nwayInfiniteProduct B N 1).re / N)) := by
  have hc0 := (nway_hasProdLocallyUniformly B N hB hN).tendstoLocallyUniformly_finsetRange
  have hc1 := hc0.tendstoLocallyUniformlyOn.tendsto_at
    (show (1 : ℂ) ∈ (Set.univ : Set ℂ) by simp)
  have hc2 := hc1.comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun M => nwayFiniteProduct B N M 1) atTop
      (𝓝 (nwayInfiniteProduct B N 1)) := by
    apply hc2.congr'
    filter_upwards [] with M
    change (∏ i ∈ Finset.range (M + 1), nwayFactor B N i 1) =
      nwayFiniteProduct B N M 1
    rw [nwayFiniteProduct,
      Fin.prod_univ_eq_prod_range (fun m => nwayFactor B N m 1) (M + 1)]
  have hr := (Complex.continuous_re.tendsto _).comp hc
  have hd := hr.div_const (N : ℝ)
  apply hd.congr'
  filter_upwards [] with M
  have heq := nwayFiniteProduct_one_eq B N M hN
  change (nwayFiniteProduct B N M 1).re / (N : ℝ) = nwayTailPartial B N M
  rw [heq]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  field_simp

theorem nwayTailPartial_le_thirty_two_nine (B N M : ℕ) (hB : 2 ≤ B) :
    nwayTailPartial B N M ≤ 32 / 9 := by
  calc
    nwayTailPartial B N M ≤ ∏ m ∈ Finset.range M, (dyadicFactor m)⁻¹ := by
      apply Finset.prod_le_prod
      · intro m hm
        unfold nwayFactorReal
        exact Finset.sum_nonneg fun u hu ↦ by positivity
      · intro m hm
        exact nwayFactorReal_tail_le B N m hB
    _ ≤ 32 / 9 := dyadic_reciprocal_partial_product_le_thirty_two_nine M

/-- The common normalizer `W` from `lem:N-class-moment-matching`. -/
noncomputable def nwayNormalizer (B N : ℕ) [NeZero N] : ℝ :=
  nwayResidueMoment B N 0 0

theorem nwayResidueMoment_zero_eq_coeff_tsum (B N : ℕ) [NeZero N]
    (h : ZMod N) :
    nwayResidueMoment B N 0 h =
      ∑' m : ℕ, nwayCoeff B N (h.val + N * m) := by
  simp [nwayResidueMoment, nwayMomentTerm]

theorem nwayResidueMoment_eq_normalizer (B N t : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : ZMod N) :
    nwayResidueMoment B N t h = nwayResidueMoment B N t 0 := by
  rw [nwayResidueMoment_eq_common B N t hB hN h,
    nwayResidueMoment_eq_common B N t hB hN 0]

theorem nwayNormalizer_eq_residue (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) (h : ZMod N) :
    nwayNormalizer B N = nwayResidueMoment B N 0 h := by
  rw [nwayNormalizer, nwayResidueMoment_eq_normalizer B N 0 hB hN h]

theorem nwayNormalizer_eq_product (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayNormalizer B N = (nwayInfiniteProduct B N 1).re / N := by
  simpa [nwayNormalizer] using nwayResidueMoment_eq_common B N 0 hB hN 0

theorem nwayNormalizer_le_thirty_two_nine (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) : nwayNormalizer B N ≤ 32 / 9 := by
  rw [nwayNormalizer_eq_product B N hB hN]
  exact le_of_tendsto' (tendsto_nwayTailPartial B N hB hN)
    (fun M => nwayTailPartial_le_thirty_two_nine B N M hB)

theorem nwayNormalizer_ge_one (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) : 1 ≤ nwayNormalizer B N := by
  rw [nwayNormalizer, nwayResidueMoment_zero_eq_coeff_tsum]
  have hs : Summable (fun m : ℕ => nwayCoeff B N ((0 : ZMod N).val + N * m)) := by
    simpa [nwayMomentTerm] using
      summable_nwayResidueMoment B N 0 hB hN (0 : ZMod N)
  calc
    1 = nwayCoeff B N ((0 : ZMod N).val + N * 0) := by
      simp [nwayCoeff_zero B N hB hN]
    _ ≤ ∑' m : ℕ, nwayCoeff B N ((0 : ZMod N).val + N * m) :=
      hs.le_tsum 0 (fun m hm => nwayCoeff_nonneg B N _ hB hN)

theorem nwayNormalizer_pos (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) : 0 < nwayNormalizer B N :=
  zero_lt_one.trans_le (nwayNormalizer_ge_one B N hB hN)

theorem nwayNormalizer_lt_four (B N : ℕ) [NeZero N]
    (hB : 2 ≤ B) (hN : 2 ≤ N) : nwayNormalizer B N < 4 :=
  (nwayNormalizer_le_thirty_two_nine B N hB hN).trans_lt (by norm_num)

/-- Euclidean division parameters used in the coefficient estimates. -/
def nwayLevel (N j : ℕ) : ℕ := j / (N - 1)

def nwayRemainder (N j : ℕ) : ℕ := j % (N - 1)

/-- The manuscript exponent `e(j)`. -/
def nwayExponent (N j : ℕ) : ℕ :=
  let L := nwayLevel N j
  let b := nwayRemainder N j
  (N - 1) * (L * (L - 1) / 2) + L * b

lemma nwayRemainder_lt (N j : ℕ) (hN : 2 ≤ N) : nwayRemainder N j < N - 1 := by
  exact Nat.mod_lt _ (by omega)

lemma nway_decomposition (N j : ℕ) :
    (N - 1) * nwayLevel N j + nwayRemainder N j = j := by
  simpa [nwayLevel, nwayRemainder, mul_comm] using Nat.div_add_mod j (N - 1)

private def exponentAux (d L b : ℕ) : ℕ :=
  d * (L * (L - 1) / 2) + L * b

private lemma level_ge_three_quadratic {L : ℕ} (hL : 3 ≤ L) :
    L ≤ L * (L - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
  exact Nat.mul_le_mul_left L (by omega : 2 ≤ L - 1)

private theorem exponentAux_gap_le (d L b : ℕ) (hd : 0 < d) (hb : b < d) :
    ((d * L + b : ℕ) : ℤ) - exponentAux d L b ≤ (d : ℤ) := by
  by_cases hL : L ≤ 2
  · interval_cases L <;> simp [exponentAux] <;> omega
  · have hL3 : 3 ≤ L := by omega
    have hquad := level_ge_three_quadratic hL3
    have hbmul : b ≤ L * b := Nat.le_mul_of_pos_left b (by omega)
    have hde : d * L + b ≤ exponentAux d L b := by
      exact Nat.add_le_add (Nat.mul_le_mul_left d hquad) hbmul
    have hz : (((d * L + b : ℕ) : ℤ) - exponentAux d L b) ≤ 0 :=
      sub_nonpos.mpr (by exact_mod_cast hde)
    omega

private theorem exponentAux_gap_eq_iff (d L b : ℕ) (hd : 0 < d) (hb : b < d) :
    ((d * L + b : ℕ) : ℤ) - exponentAux d L b = (d : ℤ) ↔
      d ≤ d * L + b ∧ d * L + b ≤ 2 * d := by
  constructor
  · intro heq
    by_cases hL : L ≤ 2
    · interval_cases L <;> simp [exponentAux] at heq ⊢ <;> omega
    · have hL3 : 3 ≤ L := by omega
      have hquad := level_ge_three_quadratic hL3
      have hde : d * L + b ≤ exponentAux d L b :=
        Nat.add_le_add (Nat.mul_le_mul_left d hquad)
          (Nat.le_mul_of_pos_left b (by omega))
      have hz : (((d * L + b : ℕ) : ℤ) - exponentAux d L b) ≤ 0 :=
        sub_nonpos.mpr (by exact_mod_cast hde)
      omega
  · rintro ⟨hlo, hhi⟩
    have hLpos : 1 ≤ L := by
      by_contra h
      have : L = 0 := by omega
      subst L
      simp at hlo
      omega
    have hLle : L ≤ 2 := by
      by_contra h
      have hL3 : 3 ≤ L := by omega
      have h3d : 3 * d ≤ L * d := Nat.mul_le_mul_right d hL3
      have hcomm : L * d = d * L := Nat.mul_comm _ _
      omega
    interval_cases L <;> simp [exponentAux] at * <;> omega

/-- Arithmetic half of `lem:N-class-coeff-bounds`: `j-e(j) ≤ N-1`.
The subtraction is in `ℤ`, as it is in the manuscript's proof when `L ≥3`. -/
theorem nway_index_sub_exponent_le (N j : ℕ) (hN : 2 ≤ N) :
    (j : ℤ) - nwayExponent N j ≤ (N - 1 : ℕ) := by
  have h := exponentAux_gap_le (N - 1) (nwayLevel N j) (nwayRemainder N j)
    (by omega) (nwayRemainder_lt N j hN)
  rw [nway_decomposition N j] at h
  simp only [nwayExponent, exponentAux] at h ⊢
  convert h using 1 <;> omega

/-- Equality range in `lem:N-class-coeff-bounds`. -/
theorem nway_index_sub_exponent_eq_iff (N j : ℕ) (hN : 2 ≤ N) :
    (j : ℤ) - nwayExponent N j = (N - 1 : ℕ) ↔
      N - 1 ≤ j ∧ j ≤ 2 * N - 2 := by
  have h := exponentAux_gap_eq_iff (N - 1) (nwayLevel N j) (nwayRemainder N j)
    (by omega) (nwayRemainder_lt N j hN)
  rw [nway_decomposition N j] at h
  simp only [nwayExponent, exponentAux] at h ⊢
  convert h using 1 <;> omega

/-! ### A coefficient recurrence and the quantitative coefficient bounds -/

lemma nwayFactor_succ (B N m : ℕ) (hB : 2 ≤ B) (z : ℂ) :
    nwayFactor B N (m + 1) z = nwayFactor B N m ((B : ℂ)⁻¹ * z) := by
  rw [nwayFactor, nwayFactor]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  rw [pow_succ, ← mul_assoc]
  ring

theorem nwayInfiniteProduct_functional (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N)
    (z : ℂ) :
    nwayInfiniteProduct B N z =
      nwayFactor B N 0 z * nwayInfiniteProduct B N ((B : ℂ)⁻¹ * z) := by
  have hz := ((nway_hasProdLocallyUniformly B N hB hN).hasProd
    (x := z)).tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  have htail := ((nway_hasProdLocallyUniformly B N hB hN).hasProd
    (x := (B : ℂ)⁻¹ * z)).tendsto_prod_nat
  have hr := htail.const_mul (nwayFactor B N 0 z)
  apply tendsto_nhds_unique hz
  apply hr.congr'
  filter_upwards [] with M
  change nwayFactor B N 0 z *
      ∏ i ∈ Finset.range M, nwayFactor B N i ((B : ℂ)⁻¹ * z) =
    ∏ i ∈ Finset.range (M + 1), nwayFactor B N i z
  calc
    nwayFactor B N 0 z *
        ∏ i ∈ Finset.range M, nwayFactor B N i ((B : ℂ)⁻¹ * z) =
      nwayFactor B N 0 z *
        ∏ i ∈ Finset.range M, nwayFactor B N (i + 1) z := by
          congr 1
          apply Finset.prod_congr rfl
          intro m hm
          exact (nwayFactor_succ B N m hB z).symm
    _ = ∏ i ∈ Finset.range (M + 1), nwayFactor B N i z := by
      rw [Finset.prod_range_succ', mul_comm]

lemma nwayFactor_zero_form (B N : ℕ) (z : ℂ) :
    nwayFactor B N 0 z = ∑ u : Fin N, z ^ (u : ℕ) := by
  rw [nwayFactor]
  simp

lemma iteratedDeriv_nwayFactor_zero (B N i : ℕ) :
    iteratedDeriv i (nwayFactor B N 0) 0 =
      if i < N then (i.factorial : ℂ) else 0 := by
  rw [show nwayFactor B N 0 = fun z : ℂ => ∑ u : Fin N, z ^ (u : ℕ) by
    funext z; exact nwayFactor_zero_form B N z]
  rw [iteratedDeriv_fun_sum (fun _ _ => by fun_prop)]
  simp only [iteratedDeriv_fun_pow_zero]
  by_cases hi : i < N
  · let u : Fin N := ⟨i, hi⟩
    rw [Fintype.sum_eq_single u]
    · simp [u, hi]
    · intro v hv
      have hvne : i ≠ (v : ℕ) := fun he => hv (Fin.ext he.symm)
      simp [hvne]
  · have hall : ∀ u : Fin N, i ≠ (u : ℕ) := by
      intro u he
      subst i
      exact hi u.isLt
    simp [hi, hall]

lemma iteratedDeriv_nwayInfiniteProduct_scaled (B N i : ℕ)
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    iteratedDeriv i (fun z : ℂ => nwayInfiniteProduct B N ((B : ℂ)⁻¹ * z)) 0 =
      (B : ℂ)⁻¹ ^ i * iteratedDeriv i (nwayInfiniteProduct B N) 0 := by
  have hc : ContDiff ℂ (i : WithTop ℕ∞) (nwayInfiniteProduct B N) :=
    (differentiable_nwayInfiniteProduct B N hB hN).contDiff
  simpa using congrFun (iteratedDeriv_comp_const_mul hc ((B : ℂ)⁻¹)) 0

private theorem nwayCoeff_recurrence_scaled (B N j : ℕ)
    (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (j.factorial : ℂ) * nwayCoeff B N j =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) *
        (if i < N then (i.factorial : ℂ) else 0) *
        ((B : ℂ)⁻¹ ^ (j - i) *
          ((j - i).factorial : ℂ) * nwayCoeff B N (j - i)) := by
  have hfun : nwayInfiniteProduct B N = fun z =>
      nwayFactor B N 0 z * nwayInfiniteProduct B N ((B : ℂ)⁻¹ * z) := by
    funext z
    exact nwayInfiniteProduct_functional B N hB hN z
  have hcG : ContDiff ℂ (j : WithTop ℕ∞) (nwayInfiniteProduct B N) :=
    (differentiable_nwayInfiniteProduct B N hB hN).contDiff
  have hcf : ContDiffAt ℂ (j : WithTop ℕ∞) (nwayFactor B N 0) 0 := by
    unfold nwayFactor
    fun_prop
  have hcg : ContDiffAt ℂ (j : WithTop ℕ∞)
      (fun z : ℂ => nwayInfiniteProduct B N ((B : ℂ)⁻¹ * z)) 0 := by
    fun_prop
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv j f 0) hfun
  change iteratedDeriv j (nwayInfiniteProduct B N) 0 =
    iteratedDeriv j (nwayFactor B N 0 *
      fun z : ℂ => nwayInfiniteProduct B N ((B : ℂ)⁻¹ * z)) 0 at hd
  rw [iteratedDeriv_mul hcf hcg] at hd
  have hcoeff (r : ℕ) : iteratedDeriv r (nwayInfiniteProduct B N) 0 =
      (r.factorial : ℂ) * nwayCoeff B N r := by
    rw [← nwayCoeffC_eq_real B N r hB hN, nwayCoeffC]
    rw [← mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)), one_mul]
  rw [hcoeff j] at hd
  simp_rw [iteratedDeriv_nwayFactor_zero,
    iteratedDeriv_nwayInfiniteProduct_scaled B N _ hB hN, hcoeff] at hd
  simpa only [mul_assoc] using hd

/-- The coefficient recurrence obtained from
`G_N(z)=(1+⋯+z^(N-1))G_N(z/B)`. -/
theorem nwayCoeff_recurrence (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayCoeff B N j =
      ∑ i ∈ Finset.range (j + 1), if i < N then
        (B : ℝ) ^ (-(j - i : ℕ) : ℤ) * nwayCoeff B N (j - i) else 0 := by
  have hs := nwayCoeff_recurrence_scaled B N j hB hN
  have hs' : (j.factorial : ℂ) * nwayCoeff B N j =
      (j.factorial : ℂ) *
        ∑ i ∈ Finset.range (j + 1), if i < N then
          (B : ℂ)⁻¹ ^ (j - i) * nwayCoeff B N (j - i) else 0 := by
    rw [hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hile : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hiN : i < N
    · simp only [hiN, ↓reduceIte]
      push_cast
      rw [show (j.choose i : ℂ) * i.factorial *
          ((B : ℂ)⁻¹ ^ (j - i) * (j - i).factorial * nwayCoeff B N (j - i)) =
          ((j.choose i * i.factorial * (j - i).factorial : ℕ) : ℂ) *
            ((B : ℂ)⁻¹ ^ (j - i) * nwayCoeff B N (j - i)) by push_cast; ring]
      rw [Nat.choose_mul_factorial_mul_factorial hile]
    · simp [hiN]
  have hcancel := mul_left_cancel₀
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j) : (j.factorial : ℂ) ≠ 0) hs'
  have hpow (k : ℕ) : (B : ℂ)⁻¹ ^ k = (((B : ℝ) ^ (-(k : ℤ))) : ℂ) := by
    rw [show (B : ℂ) = ((B : ℝ) : ℂ) by norm_cast]
    rw [← Complex.ofReal_inv]
    push_cast
    rw [zpow_neg, zpow_natCast, inv_pow]
  simp_rw [hpow] at hcancel
  apply Complex.ofReal_injective
  push_cast
  calc
    (nwayCoeff B N j : ℂ) =
        ∑ i ∈ Finset.range (j + 1), if i < N then
          (((B : ℝ) ^ (-(j - i : ℕ) : ℤ) : ℂ) *
            (nwayCoeff B N (j - i) : ℂ)) else 0 := hcancel
    _ = ∑ i ∈ Finset.range (j + 1),
        ((if i < N then (B : ℝ) ^ (-(j - i : ℕ) : ℤ) *
          nwayCoeff B N (j - i) else 0 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiN : i < N <;> simp [hiN]

private lemma triangular_succ (L : ℕ) :
    (L + 1) * L / 2 = L * (L - 1) / 2 + L := by
  calc
    (L + 1) * L / 2 = L * (L + 1) / 2 := by rw [mul_comm]
    _ = ∑ i ∈ Finset.range (L + 1), i := by
      simpa [Nat.add_sub_cancel, mul_comm] using (Finset.sum_range_id (L + 1)).symm
    _ = (∑ i ∈ Finset.range L, i) + L := by rw [Finset.sum_range_succ]
    _ = L * (L - 1) / 2 + L := by rw [Finset.sum_range_id]

private lemma nwayExponent_formula (d L b : ℕ) (hd : 0 < d) (hb : b < d) :
    nwayExponent (d + 1) (d * L + b) =
      d * (L * (L - 1) / 2) + L * b := by
  simp [nwayExponent, nwayLevel, nwayRemainder, Nat.mul_add_div hd,
    Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb]

lemma nwayExponent_add_block (d j : ℕ) (hd : 0 < d) :
    nwayExponent (d + 1) (j + d) = nwayExponent (d + 1) j + j := by
  have hb : j % d < d := Nat.mod_lt _ hd
  have hdecomp : d * (j / d) + j % d = j := Nat.div_add_mod j d
  have hf0 := nwayExponent_formula d (j / d) (j % d) hd hb
  have hf1 := nwayExponent_formula d (j / d + 1) (j % d) hd hb
  rw [← hdecomp]
  rw [show d * (j / d) + j % d + d = d * (j / d + 1) + j % d by ring]
  rw [hf1, hf0]
  rw [show (j / d + 1) * (j / d + 1 - 1) / 2 =
      (j / d) * (j / d - 1) / 2 + j / d by
        simpa [Nat.add_sub_cancel] using triangular_succ (j / d)]
  ring

lemma nwayExponent_step_le (d j k : ℕ) (hd : 0 < d)
    (hk0 : 1 ≤ k) (hkd : k ≤ d) (hkj : k ≤ j) :
    nwayExponent (d + 1) j ≤ j - k + nwayExponent (d + 1) (j - k) := by
  let L := j / d
  let b := j % d
  have hb : b < d := Nat.mod_lt _ hd
  have hj : d * L + b = j := Nat.div_add_mod j d
  by_cases hkb : k ≤ b
  · have hb' : b - k < d := by omega
    have hLk : L * k ≤ d * L := by
      simpa [mul_comm] using Nat.mul_le_mul_left L hkd
    rw [← hj]
    rw [Nat.add_sub_assoc hkb]
    rw [nwayExponent_formula d L b hd hb,
      nwayExponent_formula d L (b - k) hd hb']
    have hmul : L * (b - k) + L * k = L * b := by
      rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel (Nat.mul_le_mul_left L hkb)]
    omega
  · have hLpos : 1 ≤ L := by
      have hkj' := hkj
      rw [← hj] at hkj'
      by_contra hL
      have : L = 0 := Nat.eq_zero_of_not_pos hL
      rw [this] at hkj'
      simp only [mul_zero, zero_add] at hkj'
      exact hkb hkj'
    obtain ⟨L', hL⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
    let b' := d + b - k
    have hb' : b' < d := by omega
    have hjrepr : j = d * (L' + 1) + b := by
      rw [← hj, hL]
    have hsub : d * (L' + 1) + b - k = d * L' + b' := by
      dsimp [b']
      rw [show d * (L' + 1) + b = d * L' + (d + b) by ring,
        Nat.add_sub_assoc (by omega : k ≤ d + b)]
    rw [hjrepr]
    rw [hsub, nwayExponent_formula d (L' + 1) b hd hb,
      nwayExponent_formula d L' b' hd hb']
    rw [show (L' + 1) * (L' + 1 - 1) / 2 =
      L' * (L' - 1) / 2 + L' by
        simpa [Nat.add_sub_cancel] using triangular_succ L']
    dsimp [b']
    have hb_le : b ≤ d + b - k := by omega
    have hmul : L' * b ≤ L' * (d + b - k) := Nat.mul_le_mul_left L' hb_le
    have hleft : (L' + 1) * b = L' * b + b := by ring
    have htri : d * (L' * (L' - 1) / 2 + L') =
        d * (L' * (L' - 1) / 2) + d * L' := by ring
    omega

/-- Lower half of `lem:N-class-coeff-bounds`: the canonical packed digit configuration
contributes `B⁻ᵉ⁽ʲ⁾`. -/
theorem nwayCoeff_lower_bound (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (B : ℝ) ^ (-(nwayExponent N j : ℤ)) ≤ nwayCoeff B N j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    let d := N - 1
    have hd : 0 < d := by omega
    have hNd : d + 1 = N := by omega
    by_cases hj0 : j = 0
    · subst j
      have he : nwayExponent N 0 = 0 := by
        simp [nwayExponent, nwayLevel, nwayRemainder]
      rw [he, nwayCoeff_zero B N hB hN]
      simp
    by_cases hsmall : j < d
    · have he : nwayExponent N j = 0 := by
        rw [← hNd]
        simp [nwayExponent, nwayLevel, nwayRemainder, Nat.div_eq_of_lt hsmall]
      rw [nwayCoeff_recurrence B N j hB hN]
      rw [he]
      simp only [Nat.cast_zero, neg_zero, zpow_zero]
      let f : ℕ → ℝ := fun i => if i < N then
        (B : ℝ) ^ (-(j - i : ℕ) : ℤ) * nwayCoeff B N (j - i) else 0
      have hjN : j < N := by omega
      have hfj : f j = 1 := by
        simp [f, hjN, nwayCoeff_zero B N hB hN]
      rw [← hfj]
      exact Finset.single_le_sum (s := Finset.range (j + 1))
        (f := f) (fun i hi => by
          dsimp [f]
          split
          · exact mul_nonneg (zpow_nonneg (by positivity) _)
              (nwayCoeff_nonneg B N _ hB hN)
          · positivity) (Finset.mem_range.mpr (by omega))
    · have hdj : d ≤ j := Nat.le_of_not_gt hsmall
      let r := j - d
      have hrj : r < j := by dsimp [r]; omega
      have hlower := ih r hrj
      have hex0 := nwayExponent_add_block d r hd
      rw [hNd] at hex0
      have hradd : r + d = j := by dsimp [r]; omega
      rw [hradd] at hex0
      have hzpow : (B : ℝ) ^ (-(nwayExponent N j : ℤ)) =
          (B : ℝ) ^ (-(r : ℤ)) *
            (B : ℝ) ^ (-(nwayExponent N r : ℤ)) := by
        rw [hex0]
        push_cast
        rw [show -(↑(nwayExponent N r) + ↑r : ℤ) =
          -(r : ℤ) + -(nwayExponent N r : ℤ) by ring,
          zpow_add₀ (by positivity : (B : ℝ) ≠ 0)]
      rw [nwayCoeff_recurrence B N j hB hN, hzpow]
      let f : ℕ → ℝ := fun i => if i < N then
        (B : ℝ) ^ (-(j - i : ℕ) : ℤ) * nwayCoeff B N (j - i) else 0
      have hdN : d < N := by omega
      have hfd : f d = (B : ℝ) ^ (-(r : ℤ)) * nwayCoeff B N r := by
        simp [f, hdN, r]
      calc
        (B : ℝ) ^ (-(r : ℤ)) * (B : ℝ) ^ (-(nwayExponent N r : ℤ)) ≤
            (B : ℝ) ^ (-(r : ℤ)) * nwayCoeff B N r :=
          mul_le_mul_of_nonneg_left hlower (zpow_nonneg (by positivity) _)
        _ = f d := hfd.symm
        _ ≤ ∑ i ∈ Finset.range (j + 1), f i :=
          Finset.single_le_sum (s := Finset.range (j + 1))
            (f := f) (fun i hi => by
              dsimp [f]
              split
              · exact mul_nonneg (zpow_nonneg (by positivity) _)
                  (nwayCoeff_nonneg B N _ hB hN)
              · positivity) (Finset.mem_range.mpr (by omega))

private lemma reverse_two_sum (j : ℕ) :
    (∑ i ∈ Finset.range j, (2 : ℝ) ^ (j - (i + 1))) = (2 : ℝ) ^ j - 1 := by
  calc
    (∑ i ∈ Finset.range j, (2 : ℝ) ^ (j - (i + 1))) =
        ∑ i ∈ Finset.range j, (2 : ℝ) ^ (j - 1 - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          omega
    _ = ∑ i ∈ Finset.range j, (2 : ℝ) ^ i :=
      Finset.sum_range_reflect (fun i => (2 : ℝ) ^ i) j
    _ = (2 : ℝ) ^ j - 1 := by
      have hg := geom_sum_mul (x := (2 : ℝ)) j
      nlinarith

/-- Upper half of `lem:N-class-coeff-bounds`.  The recurrence proof is the formal counterpart
of injecting a bounded-multiplicity configuration into its tuple of nonnegative displacements. -/
theorem nwayCoeff_upper_bound (B N j : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    nwayCoeff B N j ≤ (2 : ℝ) ^ j *
      (B : ℝ) ^ (-(nwayExponent N j : ℤ)) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj0 : j = 0
    · subst j
      have he : nwayExponent N 0 = 0 := by
        simp [nwayExponent, nwayLevel, nwayRemainder]
      rw [he, nwayCoeff_zero B N hB hN]
      norm_num
    let d := N - 1
    have hd : 0 < d := by omega
    have hNd : d + 1 = N := by omega
    let f : ℕ → ℝ := fun i => if i < N then
      (B : ℝ) ^ (-(j - i : ℕ) : ℤ) * nwayCoeff B N (j - i) else 0
    have hrec0 := nwayCoeff_recurrence B N j hB hN
    change nwayCoeff B N j = ∑ i ∈ Finset.range (j + 1), f i at hrec0
    rw [Finset.sum_range_succ'] at hrec0
    have hf0 : f 0 = (B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j := by
      have hN0 : 0 < N := by omega
      simp only [f, hN0, if_true, Nat.sub_zero]
    rw [hf0] at hrec0
    let A : ℝ := (B : ℝ) ^ (-(nwayExponent N j : ℤ))
    let T : ℝ := (2 : ℝ) ^ j
    have hterm : ∀ i ∈ Finset.range j,
        f (i + 1) ≤ (2 : ℝ) ^ (j - (i + 1)) * A := by
      intro i hi
      have hi_lt : i < j := Finset.mem_range.mp hi
      have hij : i + 1 ≤ j := by omega
      by_cases hiN : i + 1 < N
      · have hikd : i + 1 ≤ d := by omega
        have hih := ih (j - (i + 1)) (by omega)
        have hex0 := nwayExponent_step_le d j (i + 1) hd (by omega) hikd hij
        rw [hNd] at hex0
        have hz : (B : ℝ) ^ (-(j - (i + 1) : ℕ) : ℤ) *
              (B : ℝ) ^ (-(nwayExponent N (j - (i + 1)) : ℤ)) ≤ A := by
          rw [← zpow_add₀ (by positivity : (B : ℝ) ≠ 0)]
          apply zpow_le_zpow_right₀ (by exact_mod_cast (show 1 ≤ B by omega))
          push_cast
          omega
        rw [show f (i + 1) = (B : ℝ) ^ (-(j - (i + 1) : ℕ) : ℤ) *
            nwayCoeff B N (j - (i + 1)) by simp [f, hiN]]
        calc
          (B : ℝ) ^ (-(j - (i + 1) : ℕ) : ℤ) *
              nwayCoeff B N (j - (i + 1)) ≤
            (B : ℝ) ^ (-(j - (i + 1) : ℕ) : ℤ) *
              ((2 : ℝ) ^ (j - (i + 1)) *
                (B : ℝ) ^ (-(nwayExponent N (j - (i + 1)) : ℤ))) :=
              mul_le_mul_of_nonneg_left hih (zpow_nonneg (by positivity) _)
          _ = (2 : ℝ) ^ (j - (i + 1)) *
              ((B : ℝ) ^ (-(j - (i + 1) : ℕ) : ℤ) *
                (B : ℝ) ^ (-(nwayExponent N (j - (i + 1)) : ℤ))) := by ring
          _ ≤ (2 : ℝ) ^ (j - (i + 1)) * A :=
            mul_le_mul_of_nonneg_left hz (by positivity)
      · rw [show f (i + 1) = 0 by simp [f, hiN]]
        positivity
    have hsum : (∑ i ∈ Finset.range j, f (i + 1)) ≤ (T - 1) * A := by
      calc
        (∑ i ∈ Finset.range j, f (i + 1)) ≤
            ∑ i ∈ Finset.range j, (2 : ℝ) ^ (j - (i + 1)) * A :=
          Finset.sum_le_sum hterm
        _ = (∑ i ∈ Finset.range j, (2 : ℝ) ^ (j - (i + 1))) * A := by
          rw [Finset.sum_mul]
        _ = (T - 1) * A := by rw [reverse_two_sum]
    have hqpos : 0 ≤ (B : ℝ) ^ (-(j : ℤ)) := zpow_nonneg (by positivity) _
    have hqlt : (B : ℝ) ^ (-(j : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_lt_one_of_one_lt₀
        (one_lt_pow₀ (by exact_mod_cast (show 1 < B by omega)) hj0)
    have hTB : T * (B : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      rw [show T = (2 : ℝ) ^ j by rfl]
      rw [← div_eq_mul_inv]
      apply (div_le_one (by positivity : (0 : ℝ) < (B : ℝ) ^ j)).2
      exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hB) j
    have hA : 0 ≤ A := zpow_nonneg (by positivity) _
    have hbudget : (T - 1) * A ≤ (T * A) * (1 - (B : ℝ) ^ (-(j : ℤ))) := by
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hTB)]
    have hmain : nwayCoeff B N j ≤
        T * A * (1 - (B : ℝ) ^ (-(j : ℤ))) +
          (B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j := by
      calc
        nwayCoeff B N j = (∑ k ∈ Finset.range j, f (k + 1)) +
            (B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j := hrec0
        _ ≤ (T - 1) * A +
            (B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j := by
          simpa only [add_comm] using
            add_le_add_right hsum ((B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j)
        _ ≤ T * A * (1 - (B : ℝ) ^ (-(j : ℤ))) +
            (B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j := by
          simpa only [add_comm] using
            add_le_add_right hbudget ((B : ℝ) ^ (-(j : ℤ)) * nwayCoeff B N j)
    apply le_of_mul_le_mul_left (a := 1 - (B : ℝ) ^ (-(j : ℤ)))
      (b := nwayCoeff B N j) (c := T * A) ?_ (sub_pos.mpr hqlt)
    nlinarith [hmain]

end MomentAmbiguity
