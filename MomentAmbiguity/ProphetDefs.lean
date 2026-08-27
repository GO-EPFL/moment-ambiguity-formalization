import MomentAmbiguity.OnlinePolicy
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Topology.Order.Lattice

/-!
# Order-statistic prophet definitions

The `r`-th largest value is a maximum over `r`-subsets of the minimum value in the subset.
Subsets consist of indices, so repeated numerical values retain their multiplicity.  Ranks are
one-based and carry the manuscript hypotheses `1 ≤ r ≤ m` in their type.
-/

open scoped ENNReal NNReal BigOperators

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- A valid one-based order-statistic rank for a horizon `m`. -/
abbrev ValidRank (m : ℕ) := {r : ℕ // 1 ≤ r ∧ r ≤ m}

/-- All `r`-element subsets of the `m` coordinate indices. -/
def rankSubsets {m : ℕ} (r : ValidRank m) : Finset (Finset (Fin m)) :=
  Finset.univ.powersetCard r.1

theorem rankSubsets_nonempty {m : ℕ} (r : ValidRank m) :
    (rankSubsets r).Nonempty := by
  rw [rankSubsets, Finset.powersetCard_nonempty]
  simpa using r.2.2

/-- Minimum value on a finite set of indices, with a harmless zero convention for the empty
set.  Empty sets never occur in `rankSubsets` because valid ranks are positive. -/
def subsetMinimum {m : ℕ} (x : ProphetPath m) (s : Finset (Fin m)) : ℝ≥0 :=
  if hs : s.Nonempty then s.inf' hs x else 0

theorem continuous_subsetMinimum {m : ℕ} (s : Finset (Fin m)) :
    Continuous (fun x : ProphetPath m ↦ subsetMinimum x s) := by
  unfold subsetMinimum
  split
  · next h =>
    apply Continuous.finset_inf'_apply h
    intro i hi
    exact (continuous_apply i : Continuous (fun x : ProphetPath m ↦ x i))
  · exact continuous_const

/-- The decreasing, multiplicity-preserving `r`-th order statistic. -/
def descendingOrderStatistic {m : ℕ} (r : ValidRank m) (x : ProphetPath m) : ℝ≥0 :=
  (rankSubsets r).sup' (rankSubsets_nonempty r) (subsetMinimum x)

theorem continuous_descendingOrderStatistic {m : ℕ} (r : ValidRank m) :
    Continuous (descendingOrderStatistic r) := by
  unfold descendingOrderStatistic
  exact Continuous.finset_sup'_apply (rankSubsets_nonempty r)
    (fun s _ ↦ continuous_subsetMinimum s)

theorem measurable_descendingOrderStatistic {m : ℕ} (r : ValidRank m) :
    Measurable (descendingOrderStatistic r) :=
  (continuous_descendingOrderStatistic r).measurable

theorem subsetMinimum_nonneg {m : ℕ} (x : ProphetPath m) (s : Finset (Fin m)) :
    0 ≤ subsetMinimum x s := bot_le

theorem subsetMinimum_le_sum {m : ℕ} (x : ProphetPath m) {s : Finset (Fin m)}
    (hs : s.Nonempty) : subsetMinimum x s ≤ ∑ i, x i := by
  have hs' : s.Nonempty := hs
  obtain ⟨i, hi⟩ := hs
  calc
    subsetMinimum x s = s.inf' hs' x := by simp [subsetMinimum, hs']
    _ ≤ x i := Finset.inf'_le _ hi
    _ ≤ ∑ j, x j := Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)

/-- Every order statistic is bounded by the coordinate sum. -/
theorem descendingOrderStatistic_le_sum {m : ℕ} (r : ValidRank m) (x : ProphetPath m) :
    descendingOrderStatistic r x ≤ ∑ i, x i := by
  rw [descendingOrderStatistic, Finset.sup'_le_iff]
  intro s hs
  have hcard : s.card = r.1 := (Finset.mem_powersetCard.1 hs).2
  have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
  exact subsetMinimum_le_sum x hsne

theorem descendingOrderStatistic_nonneg {m : ℕ} (r : ValidRank m) (x : ProphetPath m) :
    0 ≤ descendingOrderStatistic r x := bot_le

/-- A first-moment hypothesis for every coordinate. -/
def HasFiniteFirstMoments {m : ℕ} (laws : Fin m → Distribution) : Prop :=
  ∀ i, HasFiniteMoment (laws i) 1

theorem integrable_coordinate_cast {m : ℕ} (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws) (i : Fin m) :
    Integrable (fun x : ProphetPath m ↦ (x i : ℝ))
      (independentValues laws : Measure _) := by
  have hi : Integrable (fun y : ℝ≥0 ↦ (y : ℝ)) (laws i : Measure ℝ≥0) := by
    have hi' := hfirst i
    change Integrable (fun y : ℝ≥0 ↦ (y : ℝ) ^ 1) (laws i : Measure ℝ≥0) at hi'
    simpa only [pow_one] using hi'
  exact (MeasureTheory.measurePreserving_eval
    (fun i ↦ (laws i : Measure ℝ≥0)) i).integrable_comp_of_integrable hi

theorem integrable_coordinate_sum {m : ℕ} (laws : Fin m → Distribution)
    (hfirst : HasFiniteFirstMoments laws) :
    Integrable (fun x : ProphetPath m ↦ ∑ i, (x i : ℝ))
      (independentValues laws : Measure _) := by
  exact integrable_finset_sum _ fun i _ ↦ integrable_coordinate_cast laws hfirst i

/-- Finite coordinate first moments imply integrability of every valid order statistic. -/
theorem integrable_descendingOrderStatistic {m : ℕ} (r : ValidRank m)
    (laws : Fin m → Distribution) (hfirst : HasFiniteFirstMoments laws) :
    Integrable (fun x : ProphetPath m ↦ (descendingOrderStatistic r x : ℝ))
      (independentValues laws : Measure _) := by
  apply (integrable_coordinate_sum laws hfirst).mono_nonneg
    (measurable_coe_nnreal_real.comp
      (measurable_descendingOrderStatistic r)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      exact_mod_cast descendingOrderStatistic_nonneg r x
  · exact Filter.Eventually.of_forall fun x ↦ by
      exact_mod_cast descendingOrderStatistic_le_sum r x

/-- Expected `r`-th largest benchmark. -/
def orderStatisticBenchmark {m : ℕ} (r : ValidRank m)
    (laws : Fin m → Distribution) : ℝ :=
  ∫ x, (descendingOrderStatistic r x : ℝ) ∂(independentValues laws : Measure _)

theorem orderStatisticBenchmark_nonneg {m : ℕ} (r : ValidRank m)
    (laws : Fin m → Distribution) : 0 ≤ orderStatisticBenchmark r laws := by
  exact integral_nonneg fun x ↦ by positivity

/-- A single-choice policy universally guarantees `alpha` through a multiplication inequality.
No ratio is formed, so instances with zero benchmark are included without a special branch. -/
def ProphetUniversalGuarantee {m : ℕ} (r : ValidRank m) (alpha : ℝ)
    (policy : ProphetPolicy m) : Prop :=
  ∀ laws : Fin m → Distribution, (∀ i, HasFiniteMoments (laws i)) →
    alpha * orderStatisticBenchmark r laws ≤ prophetExpectedReward policy laws

/-- Feasible nonnegative universal prophet guarantees. -/
def prophetFeasibleSet {m : ℕ} (r : ValidRank m) : Set ℝ :=
  {alpha | 0 ≤ alpha ∧ ∃ policy : ProphetPolicy m,
    ProphetUniversalGuarantee r alpha policy}

/-- `sections/prophet.tex`: the robust moment-disclosure constant, defined solely through the
universal guarantee inequality. -/
def rhoMom {m : ℕ} (r : ValidRank m) : ℝ :=
  sSup (prophetFeasibleSet r)

/-- The policy that never selects; this makes the zero guarantee feasible. -/
def neverSelectPolicy (m : ℕ) : ProphetPolicy m where
  kernel := Kernel.deterministic (fun _ ↦ (none : Option (Fin m))) measurable_const
  isMarkov := inferInstance
  causal := by
    intro profile x y t hxy
    rfl

@[simp]
theorem neverSelect_expectedReward {m : ℕ} (laws : Fin m → Distribution) :
    prophetExpectedReward (neverSelectPolicy m) laws = 0 := by
  simp [prophetExpectedReward, neverSelectPolicy]

theorem prophetFeasibleSet_nonempty {m : ℕ} (r : ValidRank m) :
    (prophetFeasibleSet r).Nonempty := by
  refine ⟨0, le_rfl, neverSelectPolicy m, ?_⟩
  intro laws hfinite
  simp

/-- Multiplicity regression: every valid order statistic of a constant vector is that
constant, even though all numerical values are repeated. -/
theorem descendingOrderStatistic_const {m : ℕ} (r : ValidRank m) (c : ℝ≥0) :
    descendingOrderStatistic r (fun _ ↦ c) = c := by
  rw [descendingOrderStatistic]
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro s hs
    have hcard : s.card = r.1 := (Finset.mem_powersetCard.1 hs).2
    have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
    simp [subsetMinimum, hsne]
  · obtain ⟨s, hs⟩ := rankSubsets_nonempty r
    have hcard : s.card = r.1 := (Finset.mem_powersetCard.1 hs).2
    have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
    calc
      c = subsetMinimum (fun _ : Fin m ↦ c) s := by simp [subsetMinimum, hsne]
      _ ≤ (rankSubsets r).sup' (rankSubsets_nonempty r)
          (subsetMinimum fun _ : Fin m ↦ c) := Finset.le_sup' _ hs

/-- The deterministic unit law used to prove that the feasible set is bounded. -/
def unitDistribution : Distribution := MeasureTheory.diracProba (1 : ℝ≥0)

def unitLaws (m : ℕ) : Fin m → Distribution := fun _ ↦ unitDistribution

theorem unitDistribution_hasFiniteMoments : HasFiniteMoments unitDistribution := by
  intro k
  rw [HasFiniteMoment]
  refine MeasureTheory.integrable_dirac' ?_ ?_
  · unfold momentIntegrand
    fun_prop
  · simp [momentIntegrand]

theorem independentValues_unit (m : ℕ) :
    (independentValues (unitLaws m) : Measure (ProphetPath m)) =
      Measure.dirac (fun _ ↦ (1 : ℝ≥0)) := by
  rw [independentValues, ProbabilityMeasure.toMeasure_pi]
  apply Measure.pi_eq
  intro s hs
  classical
  by_cases h : ∀ i, (1 : ℝ≥0) ∈ s i
  · simp [unitLaws, unitDistribution, MeasureTheory.diracProba,
      Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), Set.mem_pi, hs, h]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hnot : (fun _ : Fin m ↦ (1 : ℝ≥0)) ∉ Set.univ.pi s := by
      intro hmem
      exact hi (Set.mem_pi.mp hmem i (Set.mem_univ i))
    rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Set.indicator_of_notMem hnot]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [unitLaws, unitDistribution, MeasureTheory.diracProba,
      Measure.dirac_apply' _ (hs i), hi]

theorem orderStatisticBenchmark_unit {m : ℕ} (r : ValidRank m) :
    orderStatisticBenchmark r (unitLaws m) = 1 := by
  rw [orderStatisticBenchmark, independentValues_unit]
  simp [descendingOrderStatistic_const]

/-- On the all-one instance a single-choice policy earns at most one, including when it makes
no selection. -/
theorem prophetExpectedReward_unit_le_one {m : ℕ} (policy : ProphetPolicy m) :
    prophetExpectedReward policy (unitLaws m) ≤ 1 := by
  rw [prophetExpectedReward, independentValues_unit]
  simp only [MeasureTheory.integral_dirac]
  let reward : Option (Fin m) → ℝ := fun choice ↦
    match choice with | none => 0 | some _ => 1
  have hmeas : Measurable reward := measurable_of_finite _
  have hint : Integrable reward
      (policy.kernel (disclosedProfile (unitLaws m), fun _ ↦ (1 : ℝ≥0))) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun choice ↦ by
      cases choice <;> simp [reward]
  have hone : Integrable (fun _ : Option (Fin m) ↦ (1 : ℝ))
      (policy.kernel (disclosedProfile (unitLaws m), fun _ ↦ (1 : ℝ≥0))) :=
    integrable_const _
  have hle := integral_mono hint hone (fun choice ↦ by cases choice <;> simp [reward])
  change (∫ choice, reward choice
    ∂policy.kernel (disclosedProfile (unitLaws m), fun _ ↦ (1 : ℝ≥0))) ≤ 1
  calc
    (∫ choice, reward choice
      ∂policy.kernel (disclosedProfile (unitLaws m), fun _ ↦ (1 : ℝ≥0))) ≤
        ∫ _ : Option (Fin m), (1 : ℝ)
          ∂policy.kernel (disclosedProfile (unitLaws m), fun _ ↦ (1 : ℝ≥0)) := hle
    _ = 1 := by simp

theorem prophetFeasible_le_one {m : ℕ} (r : ValidRank m) {alpha : ℝ}
    (halpha : alpha ∈ prophetFeasibleSet r) : alpha ≤ 1 := by
  obtain ⟨halpha0, policy, hpolicy⟩ := halpha
  have hguarantee := hpolicy (unitLaws m) (fun _ ↦ unitDistribution_hasFiniteMoments)
  rw [orderStatisticBenchmark_unit] at hguarantee
  simpa using hguarantee.trans (prophetExpectedReward_unit_le_one policy)

/-- The feasible universal guarantees are bounded above; this is derived from the universal
inequality itself, not inserted into the definition of `rhoMom`. -/
theorem prophetFeasibleSet_bddAbove {m : ℕ} (r : ValidRank m) :
    BddAbove (prophetFeasibleSet r) := by
  refine ⟨1, ?_⟩
  intro alpha halpha
  exact prophetFeasible_le_one r halpha

theorem rhoMom_nonneg {m : ℕ} (r : ValidRank m) : 0 ≤ rhoMom r := by
  apply le_csSup (prophetFeasibleSet_bddAbove r)
  exact ⟨le_rfl, neverSelectPolicy m, by intro laws hfinite; simp⟩

theorem rhoMom_le_one {m : ℕ} (r : ValidRank m) : rhoMom r ≤ 1 := by
  exact csSup_le (prophetFeasibleSet_nonempty r) fun alpha halpha ↦
    prophetFeasible_le_one r halpha

end

end MomentAmbiguity
