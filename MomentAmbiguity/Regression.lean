import MomentAmbiguity.NWaySeparator
import MomentAmbiguity.Newsvendor
import MomentAmbiguity.Pricing
import MomentAmbiguity.Prophet
import MomentAmbiguity.Secretary

/-!
# Edge-case regression checks

These small declarations keep the boundary cases called out in the verification plan visible
to Lean's elaborator and to the project build.
-/

open scoped ENNReal NNReal BigOperators Topology

namespace MomentAmbiguity

open Filter MeasureTheory Set

noncomputable section

/-- Horizon-one secretary regression: the explicit `r=1` branch gives success one. -/
example : secretaryS 1 = 1 := secretaryS_one

/-- The concrete N-way separator works at the smallest permitted number of classes. -/
example : Nonempty (NWaySeparatorConclusion 2 2 (by norm_num) (by norm_num)) :=
  ⟨nway_separator 2 2 (by norm_num) (by norm_num)⟩

/-- Both arbitrary global quantile endpoint conventions are exercised explicitly. -/
example (mu : Distribution) : lowerQuantile mu 0 = 0 := by simp

example (mu : Distribution) : lowerQuantile mu 1 = 0 := by simp

/-- The critical-fractile characterization includes the lower endpoint `beta=0`. -/
example (mu : Distribution) (hmu : HasFiniteMoment mu 1) :
    newsvendorArgmax mu 0 = criticalFractileSet mu 0 :=
  (newsvendor_critical_fractile mu 0 hmu (by norm_num) (by norm_num)).2.2.2

/-- The same characterization includes the upper endpoint `beta=1`; no infinite-mean branch
is introduced. -/
example (mu : Distribution) (hmu : HasFiniteMoment mu 1) :
    newsvendorArgmax mu 1 = criticalFractileSet mu 1 :=
  (newsvendor_critical_fractile mu 1 hmu (by norm_num) (by norm_num)).2.2.2

/-- Repeated numerical values retain multiplicity in the index-based order statistic. -/
example {m : ℕ} (r : ValidRank m) (c : ℝ≥0) :
    descendingOrderStatistic r (fun _ ↦ c) = c :=
  descendingOrderStatistic_const r c

/-- Zero prophet benchmarks are handled directly by the universal multiplication inequality. -/
example {m : ℕ} (r : ValidRank m) (alpha reward : ℝ)
    (hreward : 0 ≤ reward) :
    alpha * orderStatisticBenchmark r (fun _ ↦ zeroDistribution) ≤ reward := by
  have hvalues :
      independentValues (fun _ : Fin m ↦ zeroDistribution) =
        MeasureTheory.diracProba (fun _ : Fin m ↦ (0 : ℝ≥0)) := by
    simpa [zeroDistribution, deterministicLaw] using
      independentValues_deterministic m (fun _ : Fin m ↦ (0 : ℝ≥0))
  have hzero : orderStatisticBenchmark r (fun _ ↦ zeroDistribution) = 0 := by
    rw [orderStatisticBenchmark, hvalues]
    simp only [MeasureTheory.diracProba, ProbabilityMeasure.coe_mk]
    rw [MeasureTheory.integral_dirac]
    change ((descendingOrderStatistic r (fun _ : Fin m ↦ (0 : ℝ≥0)) : ℝ≥0) : ℝ) = 0
    rw [descendingOrderStatistic_const]
    norm_num
  rw [hzero, mul_zero]
  exact hreward

/-- A concrete `C_N` summand really has a negative integer exponent; it remains positive
because `pricingSeriesTerm` uses integer powers rather than natural subtraction. -/
example :
    (2 * (10 : ℤ) - (nwayExponent 3 10 : ℤ) - ((3 - 2 : ℕ) : ℤ)) = -1 := by
  norm_num [nwayExponent, nwayLevel, nwayRemainder]

example : 0 < pricingSeriesTerm 3 10 := pricingSeriesTerm_pos 3 10

/-- Exact normalization constants, not merely coarse asymptotic estimates. -/
example : (9 : ℝ) / 32 ≤ ∏' m : ℕ, dyadicFactor m :=
  dyadic_infinite_product_ge_nine_thirty_two

example : (∏' m : ℕ, dyadicFactor m)⁻¹ ≤ (32 : ℝ) / 9 :=
  tprod_dyadicFactor_inv.symm ▸
    dyadic_reciprocal_infinite_product_le_thirty_two_nine

example : (32 : ℝ) / 9 < 4 := by norm_num

end

end MomentAmbiguity
