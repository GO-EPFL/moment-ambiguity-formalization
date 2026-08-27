import MomentAmbiguity.External.Secretary
import MomentAmbiguity.NWaySeparator
import MomentAmbiguity.SecretaryRamsey
import MomentAmbiguity.ClassicalSecretary

/-!
# Internal hard-family construction for the secretary upper bound

The finite Ramsey conclusion is transferred from deterministic grid laws to the concrete
moment-equivalent `N`-way laws.  The transfer is quantitative: the product first-atom event
has probability at least one minus the sum of its coordinate failure probabilities, and a
bounded secretary success kernel changes by at most that failure probability.
-/

open scoped ENNReal NNReal BigOperators

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set
open External

noncomputable section

/-- A deterministic law concentrated at `x`; this is an internal construction, not part of
the external Ramsey hypothesis. -/
def deterministicLaw (x : ℝ≥0) : Distribution := MeasureTheory.diracProba x

/-- Assign distinct grid locations to the labelled items. -/
def assignedGridLaws {m N : ℕ} (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N) :
    Fin m → Distribution := fun i ↦ deterministicLaw (grid (a i))

/-- The deterministic secretary path induced by a grid assignment and an arrival order. -/
def gridPath {m N : ℕ} (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) : SecretaryPath m :=
  (σ, fun i ↦ grid (a i))

/-- The terminal probability of stopping at `t` on a deterministic grid path. -/
def gridStopMass {m N : ℕ} (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) : ℝ :=
  (policy.kernel (profile, gridPath grid a σ) {some t}).toReal

theorem gridStopMass_nonneg {m N : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) :
    0 ≤ gridStopMass policy profile grid a σ t := ENNReal.toReal_nonneg

theorem gridStopMass_le_one {m N : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) :
    gridStopMass policy profile grid a σ t ≤ 1 := by
  unfold gridStopMass
  have hle : policy.kernel (profile, gridPath grid a σ) {some t} ≤ (1 : ℝ≥0∞) := by
    calc
      policy.kernel (profile, gridPath grid a σ) {some t} ≤
          policy.kernel (profile, gridPath grid a σ) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle

theorem gridStopMass_sum_le_one {m N : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) :
    ∑ t, gridStopMass policy profile grid a σ t ≤ 1 := by
  let μ : Measure (Option (Fin m)) := policy.kernel (profile, gridPath grid a σ)
  let e : Fin m ↪ Option (Fin m) := ⟨some, Option.some_injective _⟩
  let s : Finset (Option (Fin m)) := Finset.univ.map e
  have hsum : (∑ z ∈ s, μ.real {z}) = μ.real (s : Set (Option (Fin m))) :=
    MeasureTheory.sum_measureReal_singleton s
  have hrewrite : (∑ t : Fin m, μ.real {some t}) = ∑ z ∈ s, μ.real {z} := by
    simpa [e, s] using (Finset.sum_map Finset.univ e (fun z ↦ μ.real {z})).symm
  rw [show (∑ t, gridStopMass policy profile grid a σ t) =
      ∑ t, μ.real {some t} by rfl, hrewrite, hsum]
  have hle : μ (s : Set (Option (Fin m))) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  calc
    μ.real (s : Set (Option (Fin m))) ≤ μ.real Set.univ :=
      ENNReal.toReal_mono (measure_ne_top _ _) hle
    _ = 1 := by simp [Measure.real]

theorem gridPath_agreeThrough {m N : ℕ} (grid : Fin N → ℝ≥0)
    (a b : Fin m ↪ Fin N) (σ τ : Equiv.Perm (Fin m)) (t : Fin m)
    (h : GridAgreeThrough t a b σ τ) :
    SecretaryAgreeThrough t (gridPath grid a σ) (gridPath grid b τ) := by
  intro i hi
  obtain ⟨hperm, hindex⟩ := h i hi
  simp only [secretaryObservation, gridPath]
  exact Prod.ext hperm (congrArg grid hindex)

theorem gridStopMass_causal {m N : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0)
    (a b : Fin m ↪ Fin N) (σ τ : Equiv.Perm (Fin m)) (t : Fin m)
    (h : GridAgreeThrough t a b σ τ) :
    gridStopMass policy profile grid a σ t =
      gridStopMass policy profile grid b τ t := by
  unfold gridStopMass
  rw [policy.causal profile _ _ t (gridPath_agreeThrough grid a b σ τ t h)]

/-- Downward quantisation into the finite colour set `{0,…,q}`. -/
def quantizedGridStopBin {m N : ℕ} (q : ℕ) (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) : ℕ :=
  ⌊(q : ℝ) * gridStopMass policy profile grid a σ t⌋₊

theorem quantizedGridStopBin_le {m N : ℕ} (q : ℕ) (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0) (a : Fin m ↪ Fin N)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) :
    quantizedGridStopBin q policy profile grid a σ t ≤ q := by
  unfold quantizedGridStopBin
  apply Nat.floor_le_of_le
  have hp := gridStopMass_le_one policy profile grid a σ t
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  nlinarith

theorem quantizedGridStopBin_total_le {m N : ℕ} (q : ℕ)
    (policy : SecretaryPolicy m) (profile : MomentProfile m) (grid : Fin N → ℝ≥0)
    (a : Fin m ↪ Fin N) (σ : Equiv.Perm (Fin m)) :
    ∑ t, quantizedGridStopBin q policy profile grid a σ t ≤ q := by
  have hfloor : ∀ t : Fin m,
      (quantizedGridStopBin q policy profile grid a σ t : ℝ) ≤
        (q : ℝ) * gridStopMass policy profile grid a σ t := by
    intro t
    exact Nat.floor_le (mul_nonneg (by positivity)
      (gridStopMass_nonneg policy profile grid a σ t))
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hreal : ((∑ t, quantizedGridStopBin q policy profile grid a σ t : ℕ) : ℝ) ≤ q := by
    calc
      ((∑ t, quantizedGridStopBin q policy profile grid a σ t : ℕ) : ℝ) =
          ∑ t, (quantizedGridStopBin q policy profile grid a σ t : ℝ) := by simp
      _ ≤ ∑ t, (q : ℝ) * gridStopMass policy profile grid a σ t :=
        Finset.sum_le_sum (fun t _ ↦ hfloor t)
      _ = (q : ℝ) * ∑ t, gridStopMass policy profile grid a σ t := by
        rw [Finset.mul_sum]
      _ ≤ (q : ℝ) * 1 := mul_le_mul_of_nonneg_left
        (gridStopMass_sum_le_one policy profile grid a σ) hq0
      _ = q := by ring
  exact_mod_cast hreal

/-- The policy's finite stopping-mass table. Quantisation, subprobability, and causality are all
proved here rather than included in `FiniteRamseyPrinciple`. -/
def policyFiniteSecretaryTable {m N : ℕ} (q : ℕ) (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (grid : Fin N → ℝ≥0) : FiniteSecretaryTable m N q where
  bin := quantizedGridStopBin q policy profile grid
  bin_le := quantizedGridStopBin_le q policy profile grid
  total_le := quantizedGridStopBin_total_le q policy profile grid
  causal := by
    intro a b σ τ t h
    unfold quantizedGridStopBin
    rw [gridStopMass_causal policy profile grid a b σ τ t h]

theorem gridStopMass_lt_quantized_add {m N q : ℕ} (hq : 1 ≤ q)
    (policy : SecretaryPolicy m) (profile : MomentProfile m) (grid : Fin N → ℝ≥0)
    (a : Fin m ↪ Fin N) (σ : Equiv.Perm (Fin m)) (t : Fin m) :
    gridStopMass policy profile grid a σ t <
      (quantizedGridStopBin q policy profile grid a σ t : ℝ) / q + 1 / q := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hfloor := Nat.lt_floor_add_one
    ((q : ℝ) * gridStopMass policy profile grid a σ t)
  unfold quantizedGridStopBin
  rw [← add_div]
  exact (lt_div_iff₀ hqR).2 (by simpa [mul_comm] using hfloor)

/-- Given a rank-arrival permutation `τ` and an independently averaged label-arrival
permutation `σ`, this is the rank assignment to fixed labels: `φ(label)=τ(σ⁻¹(label))`. -/
def rankAssignment {m : ℕ} (τ σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) :=
  σ.symm.trans τ

@[simp]
theorem rankAssignment_arrivedLabel {m : ℕ} (τ σ : Equiv.Perm (Fin m)) (t : Fin m) :
    rankAssignment τ σ (σ t) = τ t := by
  simp [rankAssignment]

/-- A Ramsey-canonical quantised table defines a classical relative-rank rule after averaging
over the independent uniform label-arrival permutation. This averaging is what preserves
label-aware policies. -/
def averagedQuantizedClassicalRule {m N q : ℕ} (hq : 1 ≤ q)
    (table : FiniteSecretaryTable m N q) (H : Fin m ↪ Fin N)
    (hcanonical : ∀ σ φ ψ t, SameAssignedRankPrefix t σ φ ψ →
      table.bin (permutedGridAssignment H φ) σ t =
        table.bin (permutedGridAssignment H ψ) σ t) : ClassicalSecretaryRule m where
  stopProb := fun τ t ↦
    ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
      ∑ σ : Equiv.Perm (Fin m),
        (table.bin (permutedGridAssignment H (rankAssignment τ σ)) σ t : ℝ) / q
  nonneg := by
    intro τ t
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun σ _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  total_le_one := by
    intro τ
    let card : ℝ := Fintype.card (Equiv.Perm (Fin m))
    have hcard : 0 < card := by dsimp [card]; positivity
    have hper : ∀ σ : Equiv.Perm (Fin m),
        (∑ t : Fin m,
          (table.bin (permutedGridAssignment H (rankAssignment τ σ)) σ t : ℝ) / q) ≤ 1 := by
      intro σ
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      rw [← Finset.sum_div]
      apply (div_le_iff₀ hqR).mpr
      simpa only [one_mul, Nat.cast_sum] using
        (show ((∑ t, table.bin
            (permutedGridAssignment H (rankAssignment τ σ)) σ t : ℕ) : ℝ) ≤ (q : ℝ) by
          exact_mod_cast table.total_le
            (permutedGridAssignment H (rankAssignment τ σ)) σ)
    calc
      ∑ t : Fin m, card⁻¹ * ∑ σ : Equiv.Perm (Fin m),
          (table.bin (permutedGridAssignment H (rankAssignment τ σ)) σ t : ℝ) / q =
          card⁻¹ * ∑ σ : Equiv.Perm (Fin m), ∑ t : Fin m,
            (table.bin (permutedGridAssignment H (rankAssignment τ σ)) σ t : ℝ) / q := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ card⁻¹ * ∑ _σ : Equiv.Perm (Fin m), (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ ↦ hper σ))
          (inv_nonneg.mpr hcard.le)
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul, mul_one]
        change card⁻¹ * card = 1
        exact inv_mul_cancel₀ hcard.ne'
  causal := by
    intro τ τ' t hprefix
    apply congrArg (((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ * ·)
    )
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hcanonical σ (rankAssignment τ σ) (rankAssignment τ' σ) t]
    intro i j hi hj
    simp only [rankAssignment_arrivedLabel]
    exact hprefix i j hi hj

/-- The adversarial hard-family formulation used to identify the robust secretary value. -/
def SecretaryMomentUpperBound (m : ℕ) : Prop :=
  ∀ policy : SecretaryPolicy m, ∀ ε : ℝ, 0 < ε →
    ∃ laws : Fin m → Distribution,
      (∀ i, HasFiniteMoments (laws i)) ∧
      secretarySuccessProbability policy laws ≤ secretaryS m + ε

/-- The secretary success indicator always lies in the unit interval. -/
theorem secretarySuccessIndicator_nonneg {m : ℕ} (path : SecretaryPath m)
    (choice : Option (Fin m)) : 0 ≤ secretarySuccessIndicator path choice := by
  cases choice <;> simp [secretarySuccessIndicator]
  split <;> norm_num

theorem secretarySuccessIndicator_le_one {m : ℕ} (path : SecretaryPath m)
    (choice : Option (Fin m)) : secretarySuccessIndicator path choice ≤ 1 := by
  cases choice <;> simp [secretarySuccessIndicator]
  split <;> norm_num

/-- The cardinal value observed at a fixed arrival time is measurable, despite the coordinate
being selected by the (finite, discrete) random permutation. -/
theorem measurable_secretaryObservedValue {m : ℕ} (t : Fin m) :
    Measurable (fun path : SecretaryPath m ↦ (secretaryObservation path t).2) := by
  classical
  change Measurable (fun path : SecretaryPath m ↦ path.2 (path.1 t))
  let F : SecretaryPath m → ℝ≥0 := fun path ↦
    ∑ i : Fin m, if path.1 t = i then path.2 i else 0
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro i hi
    have hindex : Measurable (fun path : SecretaryPath m ↦ path.1 t) :=
      (measurable_of_finite (fun σ : Equiv.Perm (Fin m) ↦ σ t)).comp measurable_fst
    have heq : MeasurableSet {path : SecretaryPath m | path.1 t = i} :=
      hindex (measurableSet_singleton i)
    exact Measurable.ite heq ((measurable_pi_apply i).comp measurable_snd) measurable_const
  convert hF using 1
  funext path
  simp [F]

/-- The path event on which arrival time `t` attains a (possibly tied) maximum. -/
def secretaryWinningSet {m : ℕ} (t : Fin m) : Set (SecretaryPath m) :=
  {path | ∀ s : Fin m, (secretaryObservation path s).2 ≤
    (secretaryObservation path t).2}

theorem measurableSet_secretaryWinningSet {m : ℕ} (t : Fin m) :
    MeasurableSet (secretaryWinningSet t) := by
  rw [show secretaryWinningSet t = ⋂ s : Fin m,
      {path | (secretaryObservation path s).2 ≤ (secretaryObservation path t).2} by
    ext path
    simp [secretaryWinningSet]]
  exact MeasurableSet.iInter (fun s ↦
    measurableSet_le (measurable_secretaryObservedValue s)
      (measurable_secretaryObservedValue t))

/-- The success indicator is jointly measurable in the realized path and selected time. -/
theorem measurable_secretarySuccessIndicator {m : ℕ} :
    Measurable (fun z : SecretaryPath m × Option (Fin m) ↦
      secretarySuccessIndicator z.1 z.2) := by
  classical
  let F : SecretaryPath m × Option (Fin m) → ℝ := fun z ↦
    ∑ t : Fin m, if z.2 = some t then
      if z.1 ∈ secretaryWinningSet t then 1 else 0 else 0
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro t ht
    have hchoice : MeasurableSet
        {z : SecretaryPath m × Option (Fin m) | z.2 = some t} :=
      measurable_snd (measurableSet_singleton (some t))
    have hwin : MeasurableSet
        {z : SecretaryPath m × Option (Fin m) | z.1 ∈ secretaryWinningSet t} :=
      measurable_fst (measurableSet_secretaryWinningSet t)
    exact Measurable.ite hchoice
      (Measurable.ite hwin measurable_const measurable_const) measurable_const
  convert hF using 1
  funext z
  rcases z with ⟨path, choice⟩
  cases choice with
  | none => simp [F, secretarySuccessIndicator]
  | some t => simp [F, secretarySuccessIndicator, secretaryWinningSet]

/-- Integrating the success indicator against a Markov decision kernel gives a measurable
unit-interval-valued function of the path. -/
def secretaryConditionalSuccess {m : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (path : SecretaryPath m) : ℝ :=
  ∫ choice, secretarySuccessIndicator path choice ∂policy.kernel (profile, path)

theorem stronglyMeasurable_secretaryConditionalSuccess {m : ℕ}
    (policy : SecretaryPolicy m) (profile : MomentProfile m) :
    StronglyMeasurable (secretaryConditionalSuccess policy profile) := by
  unfold secretaryConditionalSuccess
  have hstrong : StronglyMeasurable
      (fun z : SecretaryPath m × Option (Fin m) ↦ secretarySuccessIndicator z.1 z.2) :=
    measurable_secretarySuccessIndicator.stronglyMeasurable
  simpa only using hstrong.integral_kernel_prod_right''
    (η := policy.kernel) (a := profile)

theorem secretaryConditionalSuccess_nonneg {m : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (path : SecretaryPath m) :
    0 ≤ secretaryConditionalSuccess policy profile path := by
  unfold secretaryConditionalSuccess
  exact integral_nonneg (fun choice ↦ secretarySuccessIndicator_nonneg path choice)

theorem secretaryConditionalSuccess_le_one {m : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (path : SecretaryPath m) :
    secretaryConditionalSuccess policy profile path ≤ 1 := by
  unfold secretaryConditionalSuccess
  have hf : Integrable (fun choice ↦ secretarySuccessIndicator path choice)
      (policy.kernel (profile, path)) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  calc
    (∫ choice, secretarySuccessIndicator path choice
        ∂policy.kernel (profile, path)) ≤ ∫ _choice, (1 : ℝ)
        ∂policy.kernel (profile, path) := by
      exact integral_mono hf (integrable_const 1)
        (fun choice ↦ secretarySuccessIndicator_le_one path choice)
    _ = 1 := by simp

/-! ### Internal lift of a classical relative-rank rule

For a fixed cardinal vector we rank labels by the lexicographic keys `(value,label)`.  The
label component breaks ties deterministically, so the largest key is always a value maximizer.
This section constructs the resulting measurable cardinal-value policy and proves its
pointwise guarantee.  Thus classical attainment remains a purely relative-rank external fact. -/

/-- Strict lexicographic comparison of the tie-safe keys `(value,label)`. -/
def secretaryLexLT {m : ℕ} (x : ProphetPath m) (i j : Fin m) : Prop :=
  x i < x j ∨ (x i = x j ∧ i < j)

theorem secretaryLexLT_irrefl {m : ℕ} (x : ProphetPath m) (i : Fin m) :
    ¬ secretaryLexLT x i i := by
  simp [secretaryLexLT]

theorem secretaryLexLT_trans {m : ℕ} (x : ProphetPath m) {i j k : Fin m}
    (hij : secretaryLexLT x i j) (hjk : secretaryLexLT x j k) :
    secretaryLexLT x i k := by
  rcases hij with hij | ⟨hij, hij'⟩
  · rcases hjk with hjk | ⟨hjk, hjk'⟩
    · exact Or.inl (hij.trans hjk)
    · exact Or.inl (hjk ▸ hij)
  · rcases hjk with hjk | ⟨hjk, hjk'⟩
    · exact Or.inl (hij ▸ hjk)
    · exact Or.inr ⟨hij.trans hjk, hij'.trans hjk'⟩

theorem secretaryLexLT_total {m : ℕ} (x : ProphetPath m) {i j : Fin m} (hij : i ≠ j) :
    secretaryLexLT x i j ∨ secretaryLexLT x j i := by
  rcases lt_trichotomy (x i) (x j) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Or.inl (Or.inr ⟨h, hlt⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hgt⟩)
  · exact Or.inr (Or.inl h)

/-- Labels whose tie-safe key is strictly below that of `i`. -/
noncomputable def secretaryLexPredecessors {m : ℕ} (x : ProphetPath m)
    (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j ↦ secretaryLexLT x j i

/-- The zero-based tie-safe rank of a label. -/
def secretaryLexRankNat {m : ℕ} (x : ProphetPath m) (i : Fin m) : ℕ :=
  (secretaryLexPredecessors x i).card

theorem secretaryLexRankNat_lt_m {m : ℕ} (x : ProphetPath m) (i : Fin m) :
    secretaryLexRankNat x i < m := by
  have hproper : secretaryLexPredecessors x i ⊂ (Finset.univ : Finset (Fin m)) := by
    have hsub : secretaryLexPredecessors x i ⊆ (Finset.univ : Finset (Fin m)) :=
      fun _ _ ↦ Finset.mem_univ _
    exact (Finset.ssubset_iff_of_subset hsub).2
      ⟨i, Finset.mem_univ _, by simp [secretaryLexPredecessors,
        secretaryLexLT_irrefl]⟩
  simpa [secretaryLexRankNat] using Finset.card_lt_card hproper

/-- The tie-safe rank as an element of `Fin m`. -/
def secretaryLexRank {m : ℕ} (x : ProphetPath m) (i : Fin m) : Fin m :=
  ⟨secretaryLexRankNat x i, secretaryLexRankNat_lt_m x i⟩

theorem secretaryLexRankNat_lt_of_lt {m : ℕ} (x : ProphetPath m) {i j : Fin m}
    (hij : secretaryLexLT x i j) :
    secretaryLexRankNat x i < secretaryLexRankNat x j := by
  have hsub : secretaryLexPredecessors x i ⊆ secretaryLexPredecessors x j := by
    intro k hk
    simp only [secretaryLexPredecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact secretaryLexLT_trans x hk hij
  have hproper : secretaryLexPredecessors x i ⊂ secretaryLexPredecessors x j := by
    exact (Finset.ssubset_iff_of_subset hsub).2 ⟨i,
      by simp [secretaryLexPredecessors, hij],
      by simp [secretaryLexPredecessors, secretaryLexLT_irrefl]⟩
  simpa [secretaryLexRankNat] using Finset.card_lt_card hproper

theorem secretaryLexRank_injective {m : ℕ} (x : ProphetPath m) :
    Function.Injective (secretaryLexRank x) := by
  intro i j hij
  by_contra hne
  rcases secretaryLexLT_total x hne with hlt | hgt
  · have h := secretaryLexRankNat_lt_of_lt x hlt
    exact (Nat.ne_of_lt h) (congrArg Fin.val hij)
  · have h := secretaryLexRankNat_lt_of_lt x hgt
    exact (Nat.ne_of_lt h) (congrArg Fin.val hij.symm)

/-- The permutation sending each fixed label to its tie-safe rank. -/
noncomputable def secretaryLexRankPerm {m : ℕ} (x : ProphetPath m) :
    Equiv.Perm (Fin m) :=
  Equiv.ofBijective (secretaryLexRank x)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨secretaryLexRank_injective x, rfl⟩)

@[simp]
theorem secretaryLexRankPerm_apply {m : ℕ} (x : ProphetPath m) (i : Fin m) :
    secretaryLexRankPerm x i = secretaryLexRank x i := rfl

theorem secretaryLexRankPerm_lt_iff {m : ℕ} (x : ProphetPath m) (i j : Fin m) :
    secretaryLexRankPerm x i < secretaryLexRankPerm x j ↔ secretaryLexLT x i j := by
  constructor
  · intro hrank
    by_contra hnot
    have hne : i ≠ j := by
      intro hij
      subst j
      exact (lt_irrefl _ hrank)
    rcases secretaryLexLT_total x hne with hij | hji
    · exact hnot hij
    · have hreverse := secretaryLexRankNat_lt_of_lt x hji
      have hforward : secretaryLexRankNat x i < secretaryLexRankNat x j := by
        exact_mod_cast hrank
      omega
  · intro hij
    exact_mod_cast secretaryLexRankNat_lt_of_lt x hij

theorem measurable_secretaryLexLT {m : ℕ} (i j : Fin m) :
    Measurable (fun x : ProphetPath m ↦ secretaryLexLT x i j) := by
  apply measurableSet_setOf.mp
  exact (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)).union
    (((measurable_pi_apply i).eq (measurable_pi_apply j)).setOf.inter
      (MeasurableSet.const (i < j)))

theorem measurable_secretaryLexRankNat {m : ℕ} (i : Fin m) :
    Measurable (fun x : ProphetPath m ↦ secretaryLexRankNat x i) := by
  classical
  let f : ProphetPath m → ℕ := fun x ↦
    ∑ j : Fin m, if secretaryLexLT x j i then 1 else 0
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro j hj
    exact Measurable.ite (measurable_secretaryLexLT j i).setOf
      measurable_const measurable_const
  convert hf using 1
  funext x
  simpa [f, secretaryLexRankNat, secretaryLexPredecessors] using
    (Finset.card_filter (fun j : Fin m ↦ secretaryLexLT x j i) Finset.univ)

theorem measurable_secretaryLexRank {m : ℕ} (i : Fin m) :
    Measurable (fun x : ProphetPath m ↦ secretaryLexRank x i) := by
  intro s hs
  rw [show (fun x : ProphetPath m ↦ secretaryLexRank x i) ⁻¹' s =
      (fun x : ProphetPath m ↦ secretaryLexRankNat x i) ⁻¹'
        (Fin.val '' s) by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hx
      exact ⟨secretaryLexRank x i, hx, rfl⟩
    · rintro ⟨y, hy, hval⟩
      have heq : y = secretaryLexRank x i := Fin.ext hval
      simpa [heq] using hy]
  exact measurable_secretaryLexRankNat i (Fin.val '' s).to_countable.measurableSet

theorem measurable_secretaryLexRankPerm {m : ℕ} :
    Measurable (secretaryLexRankPerm : ProphetPath m → Equiv.Perm (Fin m)) := by
  intro s hs
  rw [show secretaryLexRankPerm ⁻¹' s =
      ⋃ φ : s, ⋂ i : Fin m, {x : ProphetPath m | secretaryLexRank x i = φ.1 i} by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      refine ⟨⟨secretaryLexRankPerm x, hx⟩, ?_⟩
      intro i
      rfl
    · rintro ⟨φ, hφ⟩
      have heq : secretaryLexRankPerm x = φ.1 := by
        apply Equiv.ext
        intro i
        exact hφ i
      simpa [heq] using φ.2]
  exact MeasurableSet.iUnion fun φ ↦ MeasurableSet.iInter fun i ↦
    (measurable_secretaryLexRank i) (measurableSet_singleton (φ.1 i))

/-- Arrival ranks induced by the realized cardinal vector and deterministic label tie-break. -/
def secretaryArrivalRank {m : ℕ}
    (input : MomentProfile m × SecretaryPath m) : Equiv.Perm (Fin m) :=
  input.2.1.trans (secretaryLexRankPerm input.2.2)

theorem measurable_secretaryArrivalRank {m : ℕ} :
    Measurable (secretaryArrivalRank :
      MomentProfile m × SecretaryPath m → Equiv.Perm (Fin m)) := by
  let compose : Equiv.Perm (Fin m) × Equiv.Perm (Fin m) → Equiv.Perm (Fin m) :=
    fun p ↦ p.1.trans p.2
  have hcompose : Measurable compose := measurable_of_finite compose
  exact hcompose.comp
    (((measurable_fst.comp measurable_snd).prodMk
      (measurable_secretaryLexRankPerm.comp (measurable_snd.comp measurable_snd))))

/-- The finite probability vector implementing a classical terminal-mass rule, with leftover
mass assigned to the explicit no-selection outcome. -/
def classicalRuleWeight {m : ℕ} (rule : ClassicalSecretaryRule m)
    (τ : Equiv.Perm (Fin m)) : Option (Fin m) → ℝ≥0
  | none => ⟨1 - ∑ t, rule.stopProb τ t, sub_nonneg.mpr (rule.total_le_one τ)⟩
  | some t => ⟨rule.stopProb τ t, rule.nonneg τ t⟩

theorem classicalRuleWeight_sum {m : ℕ} (rule : ClassicalSecretaryRule m)
    (τ : Equiv.Perm (Fin m)) : ∑ c, classicalRuleWeight rule τ c = 1 := by
  apply NNReal.eq
  rw [NNReal.coe_sum]
  rw [Fintype.sum_option]
  change (1 - ∑ t, rule.stopProb τ t) + ∑ t, rule.stopProb τ t = 1
  ring

/-- The probability law on stopping times associated with a classical terminal-mass rule. -/
noncomputable def classicalRuleLaw {m : ℕ} (rule : ClassicalSecretaryRule m)
    (τ : Equiv.Perm (Fin m)) : ProbabilityMeasure (Option (Fin m)) :=
  pmfProbabilityMeasure (pmfOfFintype (classicalRuleWeight rule τ)
    (classicalRuleWeight_sum rule τ))

/-- A finite-input kernel for the classical rule. Every function on the finite rank-pattern
space is measurable. -/
noncomputable def classicalRuleRankKernel {m : ℕ} (rule : ClassicalSecretaryRule m) :
    Kernel (Equiv.Perm (Fin m)) (Option (Fin m)) where
  toFun τ := classicalRuleLaw rule τ
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    exact measurable_of_finite _

theorem classicalRuleRankKernel_isMarkov {m : ℕ} (rule : ClassicalSecretaryRule m) :
    IsMarkovKernel (classicalRuleRankKernel rule) := by
  refine ⟨fun τ ↦ ?_⟩
  show IsProbabilityMeasure (classicalRuleLaw rule τ).toMeasure
  infer_instance

theorem classicalRuleRankKernel_singleton {m : ℕ}
    (rule : ClassicalSecretaryRule m) (τ : Equiv.Perm (Fin m)) (t : Fin m) :
    (classicalRuleRankKernel rule τ) {some t} =
      (classicalRuleWeight rule τ (some t) : ℝ≥0∞) := by
  rw [show classicalRuleRankKernel rule τ =
      ((classicalRuleLaw rule τ : ProbabilityMeasure (Option (Fin m))) : Measure _) by rfl]
  rw [show ((classicalRuleLaw rule τ : ProbabilityMeasure (Option (Fin m))) : Measure _)
      = (pmfOfFintype (classicalRuleWeight rule τ)
        (classicalRuleWeight_sum rule τ)).toMeasure by rfl]
  rw [(pmfOfFintype (classicalRuleWeight rule τ)
      (classicalRuleWeight_sum rule τ)).toMeasure_apply_singleton
        (some t) (measurableSet_singleton (some t)), pmfOfFintype_apply]

theorem classicalRuleRankKernel_singleton_toReal {m : ℕ}
    (rule : ClassicalSecretaryRule m) (τ : Equiv.Perm (Fin m)) (t : Fin m) :
    ((classicalRuleRankKernel rule τ) {some t}).toReal = rule.stopProb τ t := by
  rw [classicalRuleRankKernel_singleton, ENNReal.coe_toReal]
  rfl

/-- The classical rule kernel pulled back along the measurable realized arrival-rank map. -/
noncomputable def liftedClassicalRuleKernel {m : ℕ} (rule : ClassicalSecretaryRule m) :
    Kernel (MomentProfile m × SecretaryPath m) (Option (Fin m)) where
  toFun input := classicalRuleRankKernel rule (secretaryArrivalRank input)
  measurable' := (classicalRuleRankKernel rule).measurable.comp
    measurable_secretaryArrivalRank

theorem liftedClassicalRuleKernel_isMarkov {m : ℕ} (rule : ClassicalSecretaryRule m) :
    IsMarkovKernel (liftedClassicalRuleKernel rule) := by
  refine ⟨fun input ↦ ?_⟩
  exact (classicalRuleRankKernel_isMarkov rule).isProbabilityMeasure
    (secretaryArrivalRank input)

theorem secretaryArrivalRank_sameRelativePrefix {m : ℕ} (x y : SecretaryPath m)
    (t : Fin m) (h : SecretaryAgreeThrough t x y) :
    SameRelativePrefix t
      (x.1.trans (secretaryLexRankPerm x.2))
      (y.1.trans (secretaryLexRankPerm y.2)) := by
  intro i j hi hj
  have hoi := h i hi
  have hoj := h j hj
  have hli : x.1 i = y.1 i := congrArg Prod.fst hoi
  have hlj : x.1 j = y.1 j := congrArg Prod.fst hoj
  have hvi : x.2 (x.1 i) = y.2 (y.1 i) := congrArg Prod.snd hoi
  have hvj : x.2 (x.1 j) = y.2 (y.1 j) := congrArg Prod.snd hoj
  have hvi' : x.2 (y.1 i) = y.2 (y.1 i) := by simpa [hli] using hvi
  have hvj' : x.2 (y.1 j) = y.2 (y.1 j) := by simpa [hlj] using hvj
  simp only [Equiv.trans_apply, secretaryLexRankPerm_lt_iff]
  unfold secretaryLexLT
  rw [hli, hlj, hvi', hvj']

/-- Internal cardinal-value lift of a classical relative-rank rule. -/
noncomputable def liftClassicalSecretaryRule {m : ℕ}
    (rule : ClassicalSecretaryRule m) : SecretaryPolicy m where
  kernel := liftedClassicalRuleKernel rule
  isMarkov := liftedClassicalRuleKernel_isMarkov rule
  causal := by
    intro profile x y t hxy
    have hrank := secretaryArrivalRank_sameRelativePrefix x y t hxy
    have hstop := rule.causal
      (x.1.trans (secretaryLexRankPerm x.2))
      (y.1.trans (secretaryLexRankPerm y.2)) t hrank
    change classicalRuleRankKernel rule
        (x.1.trans (secretaryLexRankPerm x.2)) {some t} =
      classicalRuleRankKernel rule
        (y.1.trans (secretaryLexRankPerm y.2)) {some t}
    rw [classicalRuleRankKernel_singleton, classicalRuleRankKernel_singleton]
    congr 1
    apply NNReal.eq
    exact hstop

/-- Integrate a pointwise tie-safe classical guarantee over arbitrary independent value laws.
This is the internal bridge from the narrow classical attainment interface to the manuscript's
universal robust guarantee. -/
theorem pointwiseSecretaryGuarantee_to_universal {m : ℕ} {α : ℝ}
    (policy : SecretaryPolicy m)
    (hpoint : ∀ (profile : MomentProfile m) (values : ProphetPath m),
      α ≤ pointwiseSecretarySuccess policy profile values) :
    SecretaryUniversalGuarantee α policy := by
  intro laws hfinite
  let profile : MomentProfile m := disclosedProfile laws
  let μσ : ProbabilityMeasure (Equiv.Perm (Fin m)) := uniformPermutation m
  let μx : ProbabilityMeasure (ProphetPath m) := independentValues laws
  let F : SecretaryPath m → ℝ := fun z ↦ secretaryConditionalSuccess policy profile z
  have hFstrong : StronglyMeasurable F :=
    stronglyMeasurable_secretaryConditionalSuccess policy profile
  have hFint : Integrable F ((μσ : Measure _).prod (μx : Measure _)) := by
    apply Integrable.of_bound hFstrong.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (secretaryConditionalSuccess_nonneg policy profile z)]
      exact secretaryConditionalSuccess_le_one policy profile z)
  have hinnerInt : Integrable (fun values ↦ ∫ σ, F (σ, values) ∂(μσ : Measure _))
      (μx : Measure _) := hFint.integral_prod_right
  have hconstInt : Integrable (fun _values : ProphetPath m ↦ α) (μx : Measure _) :=
    integrable_const α
  have hmono : (∫ _values : ProphetPath m, α ∂(μx : Measure _)) ≤
      ∫ values, ∫ σ, F (σ, values) ∂(μσ : Measure _) ∂(μx : Measure _) := by
    apply integral_mono hconstInt hinnerInt
    intro values
    simpa [pointwiseSecretarySuccess, F, secretaryConditionalSuccess, μσ] using
      hpoint profile values
  have hsuccess : secretarySuccessProbability policy laws =
      ∫ z, F z ∂((μσ : Measure _).prod (μx : Measure _)) := by
    simp only [secretarySuccessProbability, secretarySuccessProbabilityAtProfile,
      secretaryPathLaw, secretaryExperiment, profile, μσ, μx,
      ProbabilityMeasure.toMeasure_prod, F, secretaryConditionalSuccess]
  calc
    α = ∫ _values : ProphetPath m, α ∂(μx : Measure _) := by simp
    _ ≤ ∫ values, ∫ σ, F (σ, values) ∂(μσ : Measure _) ∂(μx : Measure _) := hmono
    _ = ∫ z, F z ∂((μσ : Measure _).prod (μx : Measure _)) :=
      (integral_prod_symm F hFint).symm
    _ = secretarySuccessProbability policy laws := hsuccess.symm

/-! ### Deterministic-grid evaluation -/

/-- The largest label at a positive horizon. -/
def secretaryLastLabel {m : ℕ} (hm : 1 ≤ m) : Fin m := ⟨m - 1, by omega⟩

theorem fin_le_secretaryLastLabel {m : ℕ} (hm : 1 ≤ m) (i : Fin m) :
    i ≤ secretaryLastLabel hm := by
  apply Fin.mk_le_mk.mpr
  omega

/-- On a strictly ordered deterministic assignment, success is exactly selection at the
arrival time of the last (largest) label. -/
theorem secretarySuccessIndicator_gridPath {m N : ℕ} (hm : 1 ≤ m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (a : Fin m ↪ Fin N)
    (ha : StrictMono a) (σ : Equiv.Perm (Fin m)) (t : Fin m) :
    secretarySuccessIndicator (gridPath grid a σ) (some t) =
      if t = σ.symm (secretaryLastLabel hm) then 1 else 0 := by
  have hcomp : StrictMono (fun i : Fin m ↦ grid (a i)) := hgrid.comp ha
  by_cases htime : t = σ.symm (secretaryLastLabel hm)
  · rw [if_pos htime]
    simp only [secretarySuccessIndicator]
    rw [if_pos]
    intro s
    simp only [secretaryObservation, gridPath]
    rw [htime, Equiv.apply_symm_apply]
    exact hcomp.monotone (fin_le_secretaryLastLabel hm (σ s))
  · rw [if_neg htime]
    simp only [secretarySuccessIndicator]
    rw [if_neg]
    intro hwin
    have htop := hwin (σ.symm (secretaryLastLabel hm))
    simp only [secretaryObservation, gridPath, Equiv.apply_symm_apply] at htop
    have hle : secretaryLastLabel hm ≤ σ t := (hcomp.le_iff_le).mp htop
    have heq : σ t = secretaryLastLabel hm :=
      le_antisymm (fin_le_secretaryLastLabel hm _) hle
    have := congrArg σ.symm heq
    exact htime (by simpa using this)

/-- The inner terminal-choice integral on a deterministic grid is a singleton stopping mass. -/
theorem secretaryConditionalSuccess_gridPath {m N : ℕ} (hm : 1 ≤ m)
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (a : Fin m ↪ Fin N)
    (ha : StrictMono a) (σ : Equiv.Perm (Fin m)) :
    (∫ choice, secretarySuccessIndicator (gridPath grid a σ) choice
        ∂policy.kernel (profile, gridPath grid a σ)) =
      gridStopMass policy profile grid a σ (σ.symm (secretaryLastLabel hm)) := by
  have hint : Integrable (secretarySuccessIndicator (gridPath grid a σ))
      (policy.kernel (profile, gridPath grid a σ)) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [MeasureTheory.integral_fintype hint]
  simp only [gridStopMass, Measure.real]
  rw [show (∑ choice : Option (Fin m),
      (policy.kernel (profile, gridPath grid a σ) {choice}).toReal •
        secretarySuccessIndicator (gridPath grid a σ) choice) =
      ∑ t : Fin m,
        (policy.kernel (profile, gridPath grid a σ) {some t}).toReal •
          secretarySuccessIndicator (gridPath grid a σ) (some t) by
      rw [Fintype.sum_option]
      simp [secretarySuccessIndicator]]
  simp [secretarySuccessIndicator_gridPath hm grid hgrid a ha σ]

/-- Deterministic success for an arbitrary bijective assignment of an ordered homogeneous
value set to the fixed item labels. -/
theorem secretarySuccessIndicator_permutedGrid {m N : ℕ} (hm : 1 ≤ m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (H : Fin m ↪ Fin N)
    (hH : StrictMono H) (φ σ : Equiv.Perm (Fin m)) (t : Fin m) :
    secretarySuccessIndicator (gridPath grid (permutedGridAssignment H φ) σ) (some t) =
      if t = σ.symm (φ.symm (secretaryLastLabel hm)) then 1 else 0 := by
  have hcomp : StrictMono (fun r : Fin m ↦ grid (H r)) := hgrid.comp hH
  by_cases htime : t = σ.symm (φ.symm (secretaryLastLabel hm))
  · rw [if_pos htime]
    simp only [secretarySuccessIndicator]
    rw [if_pos]
    intro s
    simp only [secretaryObservation, gridPath, permutedGridAssignment,
      Function.Embedding.trans_apply]
    rw [htime, Equiv.apply_symm_apply]
    change grid (H (φ (σ s))) ≤ grid (H (φ (φ.symm (secretaryLastLabel hm))))
    rw [Equiv.apply_symm_apply]
    exact hcomp.monotone (fin_le_secretaryLastLabel hm (φ (σ s)))
  · rw [if_neg htime]
    simp only [secretarySuccessIndicator]
    rw [if_neg]
    intro hwin
    have htop := hwin (σ.symm (φ.symm (secretaryLastLabel hm)))
    simp only [secretaryObservation, gridPath, permutedGridAssignment,
      Function.Embedding.trans_apply, Equiv.apply_symm_apply] at htop
    change grid (H (φ (φ.symm (secretaryLastLabel hm)))) ≤
      grid (H (φ (σ t))) at htop
    rw [Equiv.apply_symm_apply] at htop
    have hle : secretaryLastLabel hm ≤ φ (σ t) := (hcomp.le_iff_le).mp htop
    have heq : φ (σ t) = secretaryLastLabel hm :=
      le_antisymm (fin_le_secretaryLastLabel hm _) hle
    have hlabel := congrArg φ.symm heq
    have harrival := congrArg σ.symm (show σ t = φ.symm (secretaryLastLabel hm) by
      simpa using hlabel)
    exact htime (by simpa using harrival)

theorem secretaryConditionalSuccess_permutedGrid {m N : ℕ} (hm : 1 ≤ m)
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (H : Fin m ↪ Fin N)
    (hH : StrictMono H) (φ σ : Equiv.Perm (Fin m)) :
    (∫ choice,
        secretarySuccessIndicator (gridPath grid (permutedGridAssignment H φ) σ) choice
          ∂policy.kernel (profile, gridPath grid (permutedGridAssignment H φ) σ)) =
      gridStopMass policy profile grid (permutedGridAssignment H φ) σ
        (σ.symm (φ.symm (secretaryLastLabel hm))) := by
  have hint : Integrable
      (secretarySuccessIndicator (gridPath grid (permutedGridAssignment H φ) σ))
      (policy.kernel (profile, gridPath grid (permutedGridAssignment H φ) σ)) :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [MeasureTheory.integral_fintype hint]
  simp only [gridStopMass, Measure.real]
  rw [show (∑ choice : Option (Fin m),
      (policy.kernel (profile, gridPath grid (permutedGridAssignment H φ) σ)
          {choice}).toReal •
        secretarySuccessIndicator (gridPath grid (permutedGridAssignment H φ) σ) choice) =
      ∑ t : Fin m,
        (policy.kernel (profile, gridPath grid (permutedGridAssignment H φ) σ)
          {some t}).toReal •
          secretarySuccessIndicator
            (gridPath grid (permutedGridAssignment H φ) σ) (some t) by
      rw [Fintype.sum_option]
      simp [secretarySuccessIndicator]]
  simp [secretarySuccessIndicator_permutedGrid hm grid hgrid H hH φ σ]

/-- Uniform finite permutation integration is ordinary finite averaging. -/
theorem uniformPermutation_integral_eq_average {m : ℕ}
    (f : Equiv.Perm (Fin m) → ℝ) :
    (∫ σ, f σ ∂(uniformPermutation m : Measure _)) =
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) * ∑ σ, f σ := by
  unfold uniformPermutation
  rw [coe_pmfProbabilityMeasure, PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]

/-! ### Pointwise success of the internal classical lift -/

/-- The fixed label with largest lexicographic `(value,label)` key. -/
def secretaryLexMaxLabel {m : ℕ} (hm : 1 ≤ m) (x : ProphetPath m) : Fin m :=
  (secretaryLexRankPerm x).symm (secretaryLastLabel hm)

@[simp]
theorem secretaryLexRankPerm_lexMaxLabel {m : ℕ} (hm : 1 ≤ m)
    (x : ProphetPath m) :
    secretaryLexRankPerm x (secretaryLexMaxLabel hm x) = secretaryLastLabel hm := by
  simp [secretaryLexMaxLabel]

/-- The lexicographically largest label is a maximizer of the cardinal values; deterministic
label tie-breaking changes only which maximizer is distinguished. -/
theorem secretaryLexMaxLabel_value_max {m : ℕ} (hm : 1 ≤ m)
    (x : ProphetPath m) (i : Fin m) :
    x i ≤ x (secretaryLexMaxLabel hm x) := by
  by_contra hnot
  have hv : x (secretaryLexMaxLabel hm x) < x i := lt_of_not_ge hnot
  have hlex : secretaryLexLT x (secretaryLexMaxLabel hm x) i := Or.inl hv
  have hrank := (secretaryLexRankPerm_lt_iff x (secretaryLexMaxLabel hm x) i).2 hlex
  rw [secretaryLexRankPerm_lexMaxLabel] at hrank
  exact (not_lt_of_ge (fin_le_secretaryLastLabel hm _)) hrank

theorem secretarySuccessIndicator_lexMaxLabel {m : ℕ} (hm : 1 ≤ m)
    (x : ProphetPath m) (σ : Equiv.Perm (Fin m)) :
    secretarySuccessIndicator (σ, x)
      (some (σ.symm (secretaryLexMaxLabel hm x))) = 1 := by
  simp only [secretarySuccessIndicator]
  rw [if_pos]
  intro s
  simp only [secretaryObservation, Equiv.apply_symm_apply]
  exact secretaryLexMaxLabel_value_max hm x (σ s)

/-- For every fixed cardinal vector and arrival order, the lifted policy's success mass is at
least the classical rule's mass of selecting the largest tie-safe rank. -/
theorem liftClassicalSecretaryRule_inner_success_ge {m : ℕ} (hm : 1 ≤ m)
    (rule : ClassicalSecretaryRule m) (profile : MomentProfile m)
    (x : ProphetPath m) (σ : Equiv.Perm (Fin m)) :
    rule.stopProb (σ.trans (secretaryLexRankPerm x))
        ((σ.trans (secretaryLexRankPerm x)).symm (secretaryLastLabel hm)) ≤
      ∫ choice, secretarySuccessIndicator (σ, x) choice
        ∂(liftClassicalSecretaryRule rule).kernel (profile, (σ, x)) := by
  let t : Fin m := σ.symm (secretaryLexMaxLabel hm x)
  let μ : Measure (Option (Fin m)) :=
    (liftClassicalSecretaryRule rule).kernel (profile, (σ, x))
  have htime : (σ.trans (secretaryLexRankPerm x)).symm (secretaryLastLabel hm) = t := by
    simp [t, secretaryLexMaxLabel, Equiv.symm_trans_apply]
  have hmass : μ.real {some t} =
      rule.stopProb (σ.trans (secretaryLexRankPerm x)) t := by
    change ((classicalRuleRankKernel rule
      (σ.trans (secretaryLexRankPerm x))) {some t}).toReal = _
    exact classicalRuleRankKernel_singleton_toReal rule _ t
  have hwin : secretarySuccessIndicator (σ, x) (some t) = 1 := by
    simpa [t] using secretarySuccessIndicator_lexMaxLabel hm x σ
  have hint : Integrable (secretarySuccessIndicator (σ, x)) μ :=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [MeasureTheory.integral_fintype hint]
  have hsingle :
      μ.real {some t} • secretarySuccessIndicator (σ, x) (some t) ≤
        ∑ choice : Option (Fin m),
          μ.real {choice} • secretarySuccessIndicator (σ, x) choice := by
    exact Finset.single_le_sum
      (f := fun choice : Option (Fin m) ↦
        μ.real {choice} • secretarySuccessIndicator (σ, x) choice)
      (fun choice _ ↦ smul_nonneg measureReal_nonneg
        (secretarySuccessIndicator_nonneg (σ, x) choice))
      (Finset.mem_univ (some t))
  calc
    rule.stopProb (σ.trans (secretaryLexRankPerm x))
        ((σ.trans (secretaryLexRankPerm x)).symm (secretaryLastLabel hm)) =
        μ.real {some t} • secretarySuccessIndicator (σ, x) (some t) := by
      rw [hwin]
      simp only [smul_eq_mul, mul_one]
      rw [hmass, htime]
    _ ≤ ∑ choice : Option (Fin m),
        μ.real {choice} • secretarySuccessIndicator (σ, x) choice := hsingle

/-- Right composition by a fixed rank assignment permutes the finite arrival-order space. -/
def rightComposePerm {m : ℕ} (φ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) where
  toFun σ := σ.trans φ
  invFun τ := τ.trans φ.symm
  left_inv σ := by ext i; simp
  right_inv τ := by ext i; simp

@[simp]
theorem rightComposePerm_apply {m : ℕ} (φ σ : Equiv.Perm (Fin m)) :
    rightComposePerm φ σ = σ.trans φ := rfl

theorem classicalRuleLift_pointwise {m : ℕ} (hm : 1 ≤ m)
    (rule : ClassicalSecretaryRule m) (profile : MomentProfile m)
    (x : ProphetPath m) :
    classicalSecretarySuccess hm rule ≤
      pointwiseSecretarySuccess (liftClassicalSecretaryRule rule) profile x := by
  rw [pointwiseSecretarySuccess, uniformPermutation_integral_eq_average]
  unfold classicalSecretarySuccess
  have hreindex :
      (∑ τ : Equiv.Perm (Fin m),
        rule.stopProb τ (τ.symm (secretaryLastLabel hm))) =
      ∑ σ : Equiv.Perm (Fin m),
        rule.stopProb (σ.trans (secretaryLexRankPerm x))
          ((σ.trans (secretaryLexRankPerm x)).symm (secretaryLastLabel hm)) := by
    rw [← Equiv.sum_comp (rightComposePerm (secretaryLexRankPerm x))
      (fun τ : Equiv.Perm (Fin m) ↦
        rule.stopProb τ (τ.symm (secretaryLastLabel hm)))]
    simp only [rightComposePerm_apply]
  change ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
      (∑ τ : Equiv.Perm (Fin m),
        rule.stopProb τ (τ.symm (secretaryLastLabel hm))) ≤ _
  rw [hreindex]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun σ _ ↦
      liftClassicalSecretaryRule_inner_success_ge hm rule profile x σ))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- An attaining relative-rank rule lifts internally to a robust cardinal-value policy. -/
theorem classicalRuleAttainment_universal {m : ℕ} (hm : 1 ≤ m)
    (rule : ClassicalSecretaryRule m)
    (hattain : secretaryS m ≤ classicalSecretarySuccess hm rule) :
    SecretaryUniversalGuarantee (secretaryS m) (liftClassicalSecretaryRule rule) := by
  apply pointwiseSecretaryGuarantee_to_universal
  intro profile x
  exact hattain.trans (classicalRuleLift_pointwise hm rule profile x)

/-- The relative-rank attainment half of the classical theorem yields the manuscript's robust
lower bound only through the preceding internal tie-breaking, kernel, and integration proofs. -/
theorem classicalPointwiseAttainment_universal (hClassical : ClassicalSecretaryAttainment)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ policy : SecretaryPolicy m,
      SecretaryUniversalGuarantee (secretaryS m) policy := by
  change (∀ (m : ℕ) (hm : 1 ≤ m), ∃ rule : ClassicalSecretaryRule m,
    secretaryS m ≤ classicalSecretarySuccess hm rule) at hClassical
  obtain ⟨rule, hattain⟩ := hClassical m hm
  exact ⟨liftClassicalSecretaryRule rule,
    classicalRuleAttainment_universal hm rule hattain⟩

/-! ### Product first-atom event -/

/-- Finite union bound in multiplicative form. -/
theorem one_sub_sum_one_sub_le_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    1 - ∑ i ∈ s, (1 - p i) ≤ ∏ i ∈ s, p i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpa0 : 0 ≤ p a := hp0 a (Finset.mem_insert_self a s)
      have hpa1 : p a ≤ 1 := hp1 a (Finset.mem_insert_self a s)
      have ih' : 1 - ∑ i ∈ s, (1 - p i) ≤ ∏ i ∈ s, p i :=
        ih (fun i hi ↦ hp0 i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hp1 i (Finset.mem_insert_of_mem hi))
      have hsum0 : 0 ≤ ∑ i ∈ s, (1 - p i) :=
        Finset.sum_nonneg (fun i hi ↦ sub_nonneg.mpr (hp1 i (Finset.mem_insert_of_mem hi)))
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      calc
        1 - ((1 - p a) + ∑ i ∈ s, (1 - p i)) ≤
            p a * (1 - ∑ i ∈ s, (1 - p i)) := by nlinarith
        _ ≤ p a * ∏ i ∈ s, p i := mul_le_mul_of_nonneg_left ih' hpa0

/-- The atom of a finite independent product is the product of the coordinate atoms. -/
theorem independentValues_singleton_toReal {m : ℕ} (laws : Fin m → Distribution)
    (x : ProphetPath m) :
    (((independentValues laws : ProbabilityMeasure (ProphetPath m)) : Measure _)
      {x}).toReal =
      ∏ i : Fin m, ((((laws i : Distribution) : Measure ℝ≥0) {x i}).toReal) := by
  change (Measure.pi (fun i ↦ ((laws i : Distribution) : Measure ℝ≥0)) {x}).toReal = _
  rw [Measure.pi_singleton, ENNReal.toReal_prod]

/-- Product first-atom event / union bound.  If every coordinate hits its designated atom with
probability at least `1-δ`, then all coordinates hit simultaneously with probability at least
`1-mδ`. -/
theorem independentValues_firstAtom_unionBound {m : ℕ} (laws : Fin m → Distribution)
    (x : ProphetPath m) (δ : ℝ)
    (hatom : ∀ i : Fin m,
      1 - δ ≤ ((((laws i : Distribution) : Measure ℝ≥0) {x i}).toReal)) :
    1 - m * δ ≤
      (((independentValues laws : ProbabilityMeasure (ProphetPath m)) : Measure _)
        {x}).toReal := by
  let p : Fin m → ℝ := fun i ↦
    ((((laws i : Distribution) : Measure ℝ≥0) {x i}).toReal)
  have hp0 : ∀ i : Fin m, 0 ≤ p i := fun i ↦ ENNReal.toReal_nonneg
  have hp1 : ∀ i : Fin m, p i ≤ 1 := by
    intro i
    have hle : (((laws i : Distribution) : Measure ℝ≥0) {x i}) ≤ (1 : ℝ≥0∞) := by
      calc
        (((laws i : Distribution) : Measure ℝ≥0) {x i}) ≤
            ((laws i : Distribution) : Measure ℝ≥0) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    simpa [p] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hle
  have hdefect : (∑ i : Fin m, (1 - p i)) ≤ m * δ := by
    calc
      (∑ i : Fin m, (1 - p i)) ≤ ∑ _i : Fin m, δ :=
        Finset.sum_le_sum (fun i _ ↦ by dsimp [p]; linarith [hatom i])
      _ = m * δ := by simp [mul_comm]
  rw [independentValues_singleton_toReal laws x]
  calc
    1 - m * δ ≤ 1 - ∑ i : Fin m, (1 - p i) := sub_le_sub_left hdefect 1
    _ ≤ ∏ i : Fin m, p i :=
      one_sub_sum_one_sub_le_prod Finset.univ p
        (fun i _ ↦ hp0 i) (fun i _ ↦ hp1 i)
    _ = ∏ i : Fin m,
        ((((laws i : Distribution) : Measure ℝ≥0) {x i}).toReal) := rfl

/-! ### Bounded-integral transfer from a large atom -/

/-- A `[0,1]`-valued statistic under a probability measure is at most its value at a chosen
atom plus the probability of missing that atom. -/
theorem integral_le_point_add_failure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : ProbabilityMeasure α) (f : α → ℝ) (x : α)
    (hf : StronglyMeasurable f) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) :
    (∫ y, f y ∂(μ : Measure α)) ≤
      f x + (1 - ((μ : Measure α) {x}).toReal) := by
  have hfint : Integrable f (μ : Measure α) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
      exact hf1 y)
  have hp0 : 0 ≤ (μ : Measure α).real {x} := measureReal_nonneg
  have hp1 : (μ : Measure α).real {x} ≤ 1 := by
    have hle : (μ : Measure α) {x} ≤ (1 : ℝ≥0∞) := by
      calc
        (μ : Measure α) {x} ≤ (μ : Measure α) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hsingle : (μ : Measure α).real {x} * f x ≤ f x := by
    nlinarith [hf0 x]
  have hcomp : (∫ y in ({x} : Set α)ᶜ, f y ∂(μ : Measure α)) ≤
      1 - (μ : Measure α).real {x} := by
    have hle : (∫ y in ({x} : Set α)ᶜ, f y ∂(μ : Measure α)) ≤
        ∫ _y in ({x} : Set α)ᶜ, (1 : ℝ) ∂(μ : Measure α) := by
      exact integral_mono hfint.integrableOn (integrable_const 1).integrableOn
        (fun y ↦ hf1 y)
    calc
      (∫ y in ({x} : Set α)ᶜ, f y ∂(μ : Measure α)) ≤
          ∫ _y in ({x} : Set α)ᶜ, (1 : ℝ) ∂(μ : Measure α) := hle
      _ = (μ : Measure α).real ({x} : Set α)ᶜ := by simp
      _ = 1 - (μ : Measure α).real {x} :=
        probReal_compl_eq_one_sub (measurableSet_singleton x)
  rw [← integral_add_compl (μ := (μ : Measure α))
    (measurableSet_singleton x) hfint, integral_singleton]
  simp only [smul_eq_mul, Measure.real]
  exact add_le_add hsingle hcomp

/-- A probability measure assigning mass one to a measurable singleton is the corresponding
Dirac probability measure. -/
theorem probabilityMeasure_eq_dirac_of_singleton_eq_one {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : ProbabilityMeasure α) (x : α)
    (hx : (μ : Measure α) {x} = 1) : μ = diracProba x := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  by_cases hxs : x ∈ s
  · have hmono : (μ : Measure α) {x} ≤ (μ : Measure α) s :=
      measure_mono (Set.singleton_subset_iff.mpr hxs)
    have hle : (μ : Measure α) s ≤ 1 := by
      calc
        (μ : Measure α) s ≤ (μ : Measure α) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have honele : (1 : ℝ≥0∞) ≤ (μ : Measure α) s := by simpa [hx] using hmono
    have heq : (μ : Measure α) s = 1 := le_antisymm hle honele
    simp [heq, diracProba_toMeasure_apply_of_mem hxs]
  · have hsubset : s ⊆ ({x} : Set α)ᶜ := by simpa [Set.subset_compl_iff_disjoint_right]
    have hcompl : (μ : Measure α) ({x} : Set α)ᶜ = 0 := by
      rw [measure_compl (measurableSet_singleton x) (measure_ne_top _ _)]
      simp [hx]
    have heq : (μ : Measure α) s = 0 := measure_mono_null hsubset hcompl
    simp [heq, diracProba_toMeasure_apply', hs, hxs]

/-- A product of deterministic coordinate laws is the deterministic vector law. -/
theorem independentValues_deterministic (m : ℕ) (x : ProphetPath m) :
    independentValues (fun i : Fin m ↦ deterministicLaw (x i)) = diracProba x := by
  apply probabilityMeasure_eq_dirac_of_singleton_eq_one
  change Measure.pi (fun i : Fin m ↦
    ((deterministicLaw (x i) : Distribution) : Measure ℝ≥0)) {x} = 1
  rw [Measure.pi_singleton]
  simp [deterministicLaw]

/-- Exact deterministic-assignment evaluation. This is the coupling/averaging step that is
kept internal rather than hidden in the finite Ramsey interface. -/
theorem secretarySuccessProbabilityAtProfile_assignedGrid {m N : ℕ} (hm : 1 ≤ m)
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (a : Fin m ↪ Fin N)
    (ha : StrictMono a) :
    secretarySuccessProbabilityAtProfile policy profile (assignedGridLaws grid a) =
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin m),
          gridStopMass policy profile grid a σ (σ.symm (secretaryLastLabel hm)) := by
  have hdet : independentValues (assignedGridLaws grid a) =
      diracProba (fun i : Fin m ↦ grid (a i)) :=
    independentValues_deterministic m (fun i ↦ grid (a i))
  unfold secretarySuccessProbabilityAtProfile secretaryPathLaw secretaryExperiment
  rw [hdet]
  change (∫ z, (∫ choice, secretarySuccessIndicator z choice
      ∂policy.kernel (profile, z))
      ∂Measure.prod (uniformPermutation m : Measure _) (Measure.dirac _)) = _
  rw [integral_prod]
  · simp only [integral_dirac]
    rw [uniformPermutation_integral_eq_average]
    apply congrArg (((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) * ·)
    apply Finset.sum_congr rfl
    intro σ hσ
    exact secretaryConditionalSuccess_gridPath hm policy profile grid hgrid a ha σ
  · have hstrong : StronglyMeasurable (fun z : SecretaryPath m ↦
        ∫ choice, secretarySuccessIndicator z choice ∂policy.kernel (profile, z)) := by
      exact stronglyMeasurable_secretaryConditionalSuccess policy profile
    apply Integrable.of_bound hstrong.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact secretaryConditionalSuccess_le_one policy profile z
      · exact secretaryConditionalSuccess_nonneg policy profile z)

/-- Exact deterministic evaluation for a bijective rank assignment `φ`; the largest value is
the label `φ⁻¹(m-1)`. -/
theorem secretarySuccessProbabilityAtProfile_permutedGrid {m N : ℕ} (hm : 1 ≤ m)
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (H : Fin m ↪ Fin N)
    (hH : StrictMono H) (φ : Equiv.Perm (Fin m)) :
    secretarySuccessProbabilityAtProfile policy profile
        (assignedGridLaws grid (permutedGridAssignment H φ)) =
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin m),
          gridStopMass policy profile grid (permutedGridAssignment H φ) σ
            (σ.symm (φ.symm (secretaryLastLabel hm))) := by
  have hdet : independentValues (assignedGridLaws grid (permutedGridAssignment H φ)) =
      diracProba (fun i : Fin m ↦ grid (permutedGridAssignment H φ i)) :=
    independentValues_deterministic m (fun i ↦ grid (permutedGridAssignment H φ i))
  unfold secretarySuccessProbabilityAtProfile secretaryPathLaw secretaryExperiment
  rw [hdet]
  change (∫ z, (∫ choice, secretarySuccessIndicator z choice
      ∂policy.kernel (profile, z))
      ∂Measure.prod (uniformPermutation m : Measure _) (Measure.dirac _)) = _
  rw [integral_prod]
  · simp only [integral_dirac]
    rw [uniformPermutation_integral_eq_average]
    apply congrArg (((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) * ·)
    apply Finset.sum_congr rfl
    intro σ hσ
    exact secretaryConditionalSuccess_permutedGrid hm policy profile grid hgrid H hH φ σ
  · have hstrong : StronglyMeasurable (fun z : SecretaryPath m ↦
        ∫ choice, secretarySuccessIndicator z choice ∂policy.kernel (profile, z)) := by
      exact stronglyMeasurable_secretaryConditionalSuccess policy profile
    apply Integrable.of_bound hstrong.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact secretaryConditionalSuccess_le_one policy profile z
      · exact secretaryConditionalSuccess_nonneg policy profile z)

/-- Quantised success for a fixed bijective assignment of the homogeneous ordered values to
the labels. -/
def permutedTableSuccess {m N q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (table : FiniteSecretaryTable m N q) (H : Fin m ↪ Fin N)
    (φ : Equiv.Perm (Fin m)) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin m),
      (table.bin (permutedGridAssignment H φ) σ
        (σ.symm (φ.symm ⟨m - 1, by omega⟩)) : ℝ) / q

/-- Average the preceding score over a uniform random bijection between selected values and
fixed labels. -/
def averagePermutedTableSuccess {m N q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (table : FiniteSecretaryTable m N q) (H : Fin m ↪ Fin N) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
    ∑ φ : Equiv.Perm (Fin m), permutedTableSuccess hm hq table H φ

/-- The deterministic policy success for assignment `φ` is at most its downward-quantized
table score plus `1/q`. -/
theorem permutedGrid_success_le_table_add {m N q : ℕ} (hm : 1 ≤ m)
    (hq : 1 ≤ q) (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (H : Fin m ↪ Fin N)
    (hH : StrictMono H) (φ : Equiv.Perm (Fin m)) :
    secretarySuccessProbabilityAtProfile policy profile
        (assignedGridLaws grid (permutedGridAssignment H φ)) ≤
      permutedTableSuccess hm hq (policyFiniteSecretaryTable q policy profile grid) H φ +
        1 / q := by
  rw [secretarySuccessProbabilityAtProfile_permutedGrid hm policy profile grid hgrid H hH φ]
  unfold permutedTableSuccess policyFiniteSecretaryTable
  let card : ℝ := Fintype.card (Equiv.Perm (Fin m))
  have hcard : 0 < card := by
    dsimp [card]
    positivity
  have hsum : (∑ σ : Equiv.Perm (Fin m),
      gridStopMass policy profile grid (permutedGridAssignment H φ) σ
        (σ.symm (φ.symm (secretaryLastLabel hm)))) ≤
      ∑ σ : Equiv.Perm (Fin m),
        ((quantizedGridStopBin q policy profile grid (permutedGridAssignment H φ) σ
            (σ.symm (φ.symm (secretaryLastLabel hm))) : ℝ) / q + 1 / q) :=
    Finset.sum_le_sum (fun σ _ ↦
      (gridStopMass_lt_quantized_add hq policy profile grid
        (permutedGridAssignment H φ) σ _).le)
  calc
    card⁻¹ * ∑ σ : Equiv.Perm (Fin m),
        gridStopMass policy profile grid (permutedGridAssignment H φ) σ
          (σ.symm (φ.symm (secretaryLastLabel hm))) ≤
        card⁻¹ * ∑ σ : Equiv.Perm (Fin m),
          ((quantizedGridStopBin q policy profile grid (permutedGridAssignment H φ) σ
              (σ.symm (φ.symm (secretaryLastLabel hm))) : ℝ) / q + 1 / q) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
    _ = card⁻¹ * ∑ σ : Equiv.Perm (Fin m),
          (quantizedGridStopBin q policy profile grid (permutedGridAssignment H φ) σ
            (σ.symm (φ.symm (secretaryLastLabel hm))) : ℝ) / q + 1 / q := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      rw [mul_add]
      congr 1
      simp only [nsmul_eq_mul, mul_one]
      change card⁻¹ * (card * (1 / (q : ℝ))) = 1 / (q : ℝ)
      rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

/-- Left composition by a fixed label-arrival permutation is a bijection on rank
assignments. -/
def leftComposePerm {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin m) where
  toFun φ := σ.trans φ
  invFun τ := σ.symm.trans τ
  left_inv φ := by ext i; simp
  right_inv τ := by ext i; simp

/-- Reindexing the random rank assignment and arrival permutation identifies the average
quantized deterministic score with the success of the averaged classical rule. -/
theorem averagePermutedTableSuccess_eq_classical {m N q : ℕ}
    (hm : 1 ≤ m) (hq : 1 ≤ q) (table : FiniteSecretaryTable m N q)
    (H : Fin m ↪ Fin N)
    (hcanonical : ∀ σ φ ψ t, SameAssignedRankPrefix t σ φ ψ →
      table.bin (permutedGridAssignment H φ) σ t =
        table.bin (permutedGridAssignment H ψ) σ t) :
    averagePermutedTableSuccess hm hq table H =
      classicalSecretarySuccess hm
        (averagedQuantizedClassicalRule hq table H hcanonical) := by
  let last : Fin m := secretaryLastLabel hm
  have hreindex :
      (∑ φ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
        (table.bin (permutedGridAssignment H φ) σ
          (σ.symm (φ.symm last)) : ℝ) / q) =
      ∑ τ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
        (table.bin (permutedGridAssignment H (rankAssignment τ σ)) σ
          (τ.symm last) : ℝ) / q := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [← Equiv.sum_comp (leftComposePerm σ) (fun τ : Equiv.Perm (Fin m) ↦
        (table.bin (permutedGridAssignment H (rankAssignment τ σ)) σ
          (τ.symm last) : ℝ) / q)]
    apply Finset.sum_congr rfl
    intro φ hφ
    have hrank : rankAssignment ((leftComposePerm σ) φ) σ = φ := by
      ext i
      simp [leftComposePerm, rankAssignment]
    have htime : ((leftComposePerm σ) φ).symm last = σ.symm (φ.symm last) := by
      simp [leftComposePerm, Equiv.symm_trans_apply]
    rw [hrank, htime]
  unfold averagePermutedTableSuccess permutedTableSuccess classicalSecretarySuccess
    averagedQuantizedClassicalRule
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  let cardInv : ℝ := (Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹
  have h := congrArg (fun x : ℝ ↦ cardInv * (cardInv * x)) hreindex
  simpa [cardInv, last, secretaryLastLabel] using h

/-- Some deterministic bijective assignment performs no better than the uniform average. -/
theorem exists_permutation_le_average {m : ℕ} (f : Equiv.Perm (Fin m) → ℝ) :
    ∃ φ : Equiv.Perm (Fin m),
      f φ ≤ ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) * ∑ ψ, f ψ := by
  obtain ⟨φ, hφmem, hφ⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨φ, ?_⟩
  let card : ℝ := Fintype.card (Equiv.Perm (Fin m))
  have hcard : 0 < card := by dsimp [card]; positivity
  have hsum : card * f φ ≤ ∑ ψ : Equiv.Perm (Fin m), f ψ := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun ψ _ ↦ hφ ψ (Finset.mem_univ ψ))
    simpa [card, nsmul_eq_mul] using h
  calc
    f φ = card⁻¹ * (card * f φ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]
    _ ≤ card⁻¹ * ∑ ψ : Equiv.Perm (Fin m), f ψ :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)

/-- `lem:ramsey-erasure`, `sections/secretary.tex`. Quantisation, policy causality,
deterministic-law coupling, averaging over random rank-to-label bijections, construction of the
classical rule, and extraction of one deterministic assignment are internal. The external
inputs are the pure combinatorial `FiniteRamseyPrinciple` and the separately named classical
finite-horizon upper bound; no attainment result is used. -/
theorem ramsey_erasure_of_external
    (hRamsey : FiniteRamseyPrinciple) (hClassical : ClassicalSecretaryUpperBound)
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, m ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ (grid : Fin N → ℝ≥0), StrictMono grid →
      ∀ (profile : MomentProfile m) (policy : SecretaryPolicy m),
        ∃ a : Fin m ↪ Fin N,
          secretarySuccessProbabilityAtProfile policy profile
              (assignedGridLaws grid a) ≤ secretaryS m + ε := by
  change (∀ (m : ℕ) (hm : 1 ≤ m) (rule : ClassicalSecretaryRule m),
    classicalSecretarySuccess hm rule ≤ secretaryS m) at hClassical
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 1 ≤ q ∧ 1 / (q : ℝ) ≤ ε := by
    obtain ⟨q, hq⟩ := exists_nat_gt (1 / ε)
    refine ⟨q + 1, by omega, ?_⟩
    have hqpos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
    have hle : 1 / ε < ((q + 1 : ℕ) : ℝ) := hq.trans_le (by norm_num)
    have hone : 1 < ((q + 1 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp hle
    exact le_of_lt ((div_lt_iff₀ hqpos).2 (by simpa [mul_comm] using hone))
  obtain ⟨N₀, hmN₀, hN₀⟩ := hRamsey m hm q hq.1
  refine ⟨N₀, hmN₀, ?_⟩
  intro N hN grid hgrid profile policy
  let table := policyFiniteSecretaryTable q policy profile grid
  obtain ⟨H, hH, hcanonical⟩ := hN₀ N hN table
  let rule := averagedQuantizedClassicalRule hq.1 table H hcanonical
  have havgEq : averagePermutedTableSuccess hm hq.1 table H =
      classicalSecretarySuccess hm rule :=
    averagePermutedTableSuccess_eq_classical hm hq.1 table H hcanonical
  obtain ⟨φ, hφ⟩ := exists_permutation_le_average
    (fun φ ↦ permutedTableSuccess hm hq.1 table H φ)
  have hquant := permutedGrid_success_le_table_add hm hq.1 policy profile grid hgrid H hH φ
  refine ⟨permutedGridAssignment H φ, ?_⟩
  calc
    secretarySuccessProbabilityAtProfile policy profile
        (assignedGridLaws grid (permutedGridAssignment H φ)) ≤
        permutedTableSuccess hm hq.1 table H φ + 1 / q := hquant
    _ ≤ averagePermutedTableSuccess hm hq.1 table H + 1 / q := by
      exact add_le_add_left hφ _
    _ = classicalSecretarySuccess hm rule + 1 / q := by rw [havgEq]
    _ ≤ secretaryS m + ε := add_le_add (hClassical m hm rule) hq.2

/-- `lem:ramsey-erasure`, `sections/secretary.tex`, with both finite combinatorial inputs
discharged internally. -/
theorem ramsey_erasure
    (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, m ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ (grid : Fin N → ℝ≥0), StrictMono grid →
      ∀ (profile : MomentProfile m) (policy : SecretaryPolicy m),
        ∃ a : Fin m ↪ Fin N,
          secretarySuccessProbabilityAtProfile policy profile
              (assignedGridLaws grid a) ≤ secretaryS m + ε :=
  ramsey_erasure_of_external finiteRamseyPrinciple classicalSecretaryUpperBound
    m hm ε hε

/-- Replacing independent values by their designated deterministic atoms changes the success
probability by at most the probability that the whole value vector misses its designated atom.
The policy and disclosed profile are held fixed. -/
theorem secretarySuccessProbabilityAtProfile_le_deterministic_add_failure {m : ℕ}
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) (x : ProphetPath m) :
    secretarySuccessProbabilityAtProfile policy profile laws ≤
      secretarySuccessProbabilityAtProfile policy profile
        (fun i : Fin m ↦ deterministicLaw (x i)) +
        (1 - (((independentValues laws : ProbabilityMeasure (ProphetPath m)) : Measure _)
          {x}).toReal) := by
  let μσ : ProbabilityMeasure (Equiv.Perm (Fin m)) := uniformPermutation m
  let μx : ProbabilityMeasure (ProphetPath m) := independentValues laws
  let F : Equiv.Perm (Fin m) × ProphetPath m → ℝ := fun z ↦
    secretaryConditionalSuccess policy profile z
  have hFstrong : StronglyMeasurable F := by
    exact stronglyMeasurable_secretaryConditionalSuccess policy profile
  have hF0 : ∀ z, 0 ≤ F z := fun z ↦
    secretaryConditionalSuccess_nonneg policy profile z
  have hF1 : ∀ z, F z ≤ 1 := fun z ↦
    secretaryConditionalSuccess_le_one policy profile z
  have hFint : Integrable F ((μσ : Measure _).prod (μx : Measure _)) := by
    apply Integrable.of_bound hFstrong.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 z)]
      exact hF1 z)
  let miss : ℝ := 1 - ((μx : Measure _) {x}).toReal
  have hpointStrong : StronglyMeasurable (fun σ ↦ F (σ, x)) :=
    hFstrong.comp_measurable (measurable_id.prodMk measurable_const)
  have hpointInt : Integrable (fun σ ↦ F (σ, x)) (μσ : Measure _) := by
    apply Integrable.of_bound hpointStrong.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun σ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (σ, x))]
      exact hF1 (σ, x))
  have hrightInt : Integrable (fun σ ↦ F (σ, x) + miss) (μσ : Measure _) :=
    hpointInt.add (integrable_const miss)
  have hinner : ∀ σ,
      (∫ y, F (σ, y) ∂(μx : Measure _)) ≤ F (σ, x) + miss := by
    intro σ
    exact integral_le_point_add_failure μx (fun y ↦ F (σ, y)) x
      (hFstrong.comp_measurable (measurable_const.prodMk measurable_id))
      (fun y ↦ hF0 (σ, y)) (fun y ↦ hF1 (σ, y))
  have hout : (∫ σ, ∫ y, F (σ, y) ∂(μx : Measure _) ∂(μσ : Measure _)) ≤
      ∫ σ, (F (σ, x) + miss) ∂(μσ : Measure _) :=
    integral_mono hFint.integral_prod_left hrightInt hinner
  have hiter : (∫ σ, ∫ y, F (σ, y) ∂(μx : Measure _) ∂(μσ : Measure _)) ≤
      (∫ σ, F (σ, x) ∂(μσ : Measure _)) + miss := by
    calc
      (∫ σ, ∫ y, F (σ, y) ∂(μx : Measure _) ∂(μσ : Measure _)) ≤
          ∫ σ, (F (σ, x) + miss) ∂(μσ : Measure _) := hout
      _ = (∫ σ, F (σ, x) ∂(μσ : Measure _)) +
          ∫ _σ : Equiv.Perm (Fin m), miss ∂(μσ : Measure _) :=
        integral_add hpointInt (integrable_const miss)
      _ = (∫ σ, F (σ, x) ∂(μσ : Measure _)) + miss := by
        rw [integral_const]
        simp [Measure.real]
  have hactual : secretarySuccessProbabilityAtProfile policy profile laws =
      ∫ z, F z ∂((μσ : Measure _).prod (μx : Measure _)) := by
    simp only [secretarySuccessProbabilityAtProfile, secretaryPathLaw, secretaryExperiment,
      μσ, μx, ProbabilityMeasure.toMeasure_prod]
    rfl
  have hdetValues : independentValues (fun i : Fin m ↦ deterministicLaw (x i)) =
      diracProba x := independentValues_deterministic m x
  have hFintDet : Integrable F
      ((μσ : Measure _).prod ((diracProba x : ProbabilityMeasure _) : Measure _)) := by
    apply Integrable.of_bound hFstrong.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 z)]
      exact hF1 z)
  have hdet : secretarySuccessProbabilityAtProfile policy profile
        (fun i : Fin m ↦ deterministicLaw (x i)) =
      ∫ σ, F (σ, x) ∂(μσ : Measure _) := by
    simp only [secretarySuccessProbabilityAtProfile, secretaryPathLaw, secretaryExperiment,
      μσ, ProbabilityMeasure.toMeasure_prod]
    rw [hdetValues]
    change (∫ z, F z ∂(Measure.prod (μσ : Measure _) (Measure.dirac x))) = _
    have hFintDet' : Integrable F
        ((μσ : Measure _).prod (Measure.dirac x)) := by
      simpa [diracProba] using hFintDet
    rw [integral_prod F hFintDet']
    simp [μσ]
  rw [hactual, integral_prod F hFint, hdet]
  exact hiter

/-! ### Concrete hard family -/

/-- The geometric grid used by the `N`-way construction is strictly increasing. -/
theorem strictMono_nwayGrid (B N : ℕ) (hB : 2 ≤ B) :
    StrictMono (fun h : Fin N ↦ nwayNode B h.val) := by
  intro a b hab
  simp only [nwayNode]
  exact pow_lt_pow_right₀ (by exact_mod_cast (show 1 < B by omega)) hab

/-- The internally constructed hard family.  No hard-family hypothesis remains: the only
parameters are the named finite-Ramsey and classical finite-secretary interfaces. -/
theorem secretaryMomentUpperBound_of_external
    (hRamsey : FiniteRamseyPrinciple) (hClassical : ClassicalSecretaryUpperBound)
    (m : ℕ) (hm : 1 ≤ m) : SecretaryMomentUpperBound m := by
  intro policy ε hε
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N₀, hmN₀, hRamseyN⟩ :=
    ramsey_erasure_of_external hRamsey hClassical m hm η hη
  let N : ℕ := max N₀ 2
  have hN₀N : N₀ ≤ N := le_max_left _ _
  have hN : 2 ≤ N := le_max_right _ _
  letI : NeZero N := ⟨by omega⟩
  let δ : ℝ := ε / (2 * m)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨B, hB, hfirst⟩ := first_atom_concentration_exists N hN δ hδ
  let grid : Fin N → ℝ≥0 := fun h ↦ nwayNode B h.val
  have hgrid : StrictMono grid := strictMono_nwayGrid B N hB
  let hzero : Fin N := ⟨0, by omega⟩
  let profile : MomentProfile m := fun _ ↦
    momentSequence (nwayDistribution B N hB hN hzero)
  obtain ⟨a, ha⟩ := hRamseyN N hN₀N grid hgrid profile policy
  let laws : Fin m → Distribution := fun i ↦ nwayDistribution B N hB hN (a i)
  let x : ProphetPath m := fun i ↦ grid (a i)
  have hfinite : ∀ i, HasFiniteMoments (laws i) := by
    intro i
    exact nwayDistribution_hasFiniteMoments B N hB hN (a i)
  have hprofile : disclosedProfile laws = profile := by
    funext i
    exact (nwayDistribution_momentEquivalent B N hB hN (a i) hzero).sequence_eq
  have hatom : ∀ i : Fin m,
      1 - δ ≤ ((((laws i : Distribution) : Measure ℝ≥0) {x i}).toReal) := by
    intro i
    have hi := hfirst (a i)
    change 1 - δ ≤
      (((nwayDistribution B N hB hN (a i) : Distribution) : Measure ℝ≥0)
        {nwayNode B (a i).val}).toReal
    exact hi.le
  have hproduct := independentValues_firstAtom_unionBound laws x δ hatom
  have htransfer := secretarySuccessProbabilityAtProfile_le_deterministic_add_failure
    policy profile laws x
  have hdet : (fun i : Fin m ↦ deterministicLaw (x i)) = assignedGridLaws grid a := by
    rfl
  rw [hdet] at htransfer
  have hmiss : 1 -
      (((independentValues laws : ProbabilityMeasure (ProphetPath m)) : Measure _) {x}).toReal ≤
      m * δ := by linarith
  have hactualAtProfile : secretarySuccessProbability policy laws =
      secretarySuccessProbabilityAtProfile policy profile laws := by
    unfold secretarySuccessProbability
    rw [hprofile]
  have hmdelta : (m : ℝ) * δ = ε / 2 := by
    dsimp [δ]
    field_simp
  refine ⟨laws, hfinite, ?_⟩
  rw [hactualAtProfile]
  calc
    secretarySuccessProbabilityAtProfile policy profile laws ≤
        secretarySuccessProbabilityAtProfile policy profile (assignedGridLaws grid a) +
          (1 - (((independentValues laws : ProbabilityMeasure (ProphetPath m)) : Measure _)
            {x}).toReal) := htransfer
    _ ≤ (secretaryS m + η) + m * δ := add_le_add ha hmiss
    _ = secretaryS m + ε := by rw [hmdelta]; dsimp [η]; ring

/-- The internally closed hard-family upper bound used by the canonical secretary theorem. -/
theorem secretaryMomentUpperBound (m : ℕ) (hm : 1 ≤ m) :
    SecretaryMomentUpperBound m :=
  secretaryMomentUpperBound_of_external finiteRamseyPrinciple
    classicalSecretaryUpperBound m hm

end

end MomentAmbiguity
