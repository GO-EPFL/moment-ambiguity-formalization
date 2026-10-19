import MomentAmbiguity.Prophet.Averaging

/-!
# Embedding an iid block into a longer prophet instance

Order-statistic benchmarks can only increase when extra nonnegative coordinates are added.
The proof keeps multiplicities by mapping index subsets, and proves the product-law marginal
identity from mutual independence.
-/

open scoped BigOperators ENNReal NNReal

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Restrict a full path along an injective coordinate map. -/
def restrictProphetPath {n m : ℕ} (e : Fin n ↪ Fin m)
    (x : ProphetPath m) : ProphetPath n := fun i ↦ x (e i)

theorem measurable_restrictProphetPath {n m : ℕ} (e : Fin n ↪ Fin m) :
    Measurable (restrictProphetPath e) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (e i)

/-- Mapping the independent full vector to an injectively chosen subvector gives the product
of the selected marginals. -/
theorem map_restrictProphetPath_independentValues {n m : ℕ} (e : Fin n ↪ Fin m)
    (full : Fin m → Distribution) :
    Measure.map (restrictProphetPath e) (independentValues full : Measure _) =
      Measure.pi (fun i : Fin n ↦ (full (e i) : Measure ℝ≥0)) := by
  have hindep : iIndepFun (fun i : Fin n ↦ fun x : ProphetPath m ↦ x (e i))
      (independentValues full : Measure _) :=
    (independentValues_iIndep full).precomp e.injective
  have hmap := hindep.map_fun_eq_pi_map
    (fun i ↦ (measurable_pi_apply (e i)).aemeasurable)
  rw [show (fun x : ProphetPath m ↦ fun i : Fin n ↦ x (e i)) =
      restrictProphetPath e by rfl] at hmap
  calc
    Measure.map (restrictProphetPath e) (independentValues full : Measure _) =
        Measure.pi (fun i : Fin n ↦
          Measure.map (fun x : ProphetPath m ↦ x (e i))
            (independentValues full : Measure _)) := hmap
    _ = Measure.pi (fun i : Fin n ↦ (full (e i) : Measure ℝ≥0)) := by
      congr 1
      funext i
      have hmarg := independentValues_marginal full (e i)
      exact congrArg ProbabilityMeasure.toMeasure hmarg

theorem map_restrictProphetPath_independentValues_eq {n m : ℕ}
    (e : Fin n ↪ Fin m) (sub : Fin n → Distribution) (full : Fin m → Distribution)
    (hcoord : ∀ i, full (e i) = sub i) :
    Measure.map (restrictProphetPath e) (independentValues full : Measure _) =
      (independentValues sub : Measure _) := by
  rw [map_restrictProphetPath_independentValues]
  rw [independentValues, ProbabilityMeasure.toMeasure_pi]
  congr 1
  funext i
  rw [hcoord]

/-- Pointwise order-statistic monotonicity under an injective coordinate embedding. -/
theorem descendingOrderStatistic_restrict_le {n m r : ℕ}
    (hr : 1 ≤ r) (hrn : r ≤ n) (hrm : r ≤ m) (e : Fin n ↪ Fin m)
    (x : ProphetPath m) :
    descendingOrderStatistic (⟨r, hr, hrn⟩ : ValidRank n) (restrictProphetPath e x) ≤
      descendingOrderStatistic (⟨r, hr, hrm⟩ : ValidRank m) x := by
  rw [descendingOrderStatistic, Finset.sup'_le_iff]
  intro s hs
  have hcard : s.card = r := (Finset.mem_powersetCard.1 hs).2
  have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
  let se : Finset (Fin m) := s.map e
  have hsene : se.Nonempty := hsne.map
  have hsemem : se ∈ rankSubsets (⟨r, hr, hrm⟩ : ValidRank m) := by
    rw [rankSubsets, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simpa [se] using hcard⟩
  calc
    subsetMinimum (restrictProphetPath e x) s = subsetMinimum x se := by
      simp only [subsetMinimum, hsne, hsene, ↓reduceDIte]
      symm
      exact Finset.inf'_map x hsene
    _ ≤ (rankSubsets (⟨r, hr, hrm⟩ : ValidRank m)).sup'
        (rankSubsets_nonempty (⟨r, hr, hrm⟩ : ValidRank m))
        (subsetMinimum x) := Finset.le_sup' _ hsemem

/-- Expected order-statistic monotonicity for a selected independent subvector. -/
theorem orderStatisticBenchmark_subvector_le {n m r : ℕ}
    (hr : 1 ≤ r) (hrn : r ≤ n) (hrm : r ≤ m) (e : Fin n ↪ Fin m)
    (sub : Fin n → Distribution) (full : Fin m → Distribution)
    (hcoord : ∀ i, full (e i) = sub i)
    (hsub : HasFiniteFirstMoments sub) (hfull : HasFiniteFirstMoments full) :
    orderStatisticBenchmark (⟨r, hr, hrn⟩ : ValidRank n) sub ≤
      orderStatisticBenchmark (⟨r, hr, hrm⟩ : ValidRank m) full := by
  let rs : ValidRank n := ⟨r, hr, hrn⟩
  let rf : ValidRank m := ⟨r, hr, hrm⟩
  have hmap := map_restrictProphetPath_independentValues_eq e sub full hcoord
  have hsubInt := integrable_descendingOrderStatistic rs sub hsub
  have hfullInt := integrable_descendingOrderStatistic rf full hfull
  have hcompInt : Integrable (fun x : ProphetPath m ↦
      (descendingOrderStatistic rs (restrictProphetPath e x) : ℝ))
      (independentValues full : Measure _) := by
    rw [← hmap] at hsubInt
    have hf : AEStronglyMeasurable
        (fun x : ProphetPath n ↦ (descendingOrderStatistic rs x : ℝ))
        (Measure.map (restrictProphetPath e) (independentValues full : Measure _)) :=
      (measurable_coe_nnreal_real.comp
        (measurable_descendingOrderStatistic rs)).aestronglyMeasurable
    exact (integrable_map_measure hf
      (measurable_restrictProphetPath e).aemeasurable).mp hsubInt
  unfold orderStatisticBenchmark
  calc
    (∫ x, (descendingOrderStatistic rs x : ℝ)
        ∂(independentValues sub : Measure _)) =
        ∫ x, (descendingOrderStatistic rs (restrictProphetPath e x) : ℝ)
          ∂(independentValues full : Measure _) := by
      rw [← hmap]
      exact integral_map (measurable_restrictProphetPath e).aemeasurable
        (measurable_coe_nnreal_real.comp
          (measurable_descendingOrderStatistic rs)).aestronglyMeasurable
    _ ≤ ∫ x, (descendingOrderStatistic rf x : ℝ)
          ∂(independentValues full : Measure _) := by
      apply integral_mono hcompInt hfullInt
      intro x
      exact_mod_cast descendingOrderStatistic_restrict_le hr hrn hrm e x

end

end MomentAmbiguity
