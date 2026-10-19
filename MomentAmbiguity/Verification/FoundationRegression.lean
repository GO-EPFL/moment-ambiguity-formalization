import MomentAmbiguity.Secretary.Ramsey
import MomentAmbiguity.Secretary.Limit
import MomentAmbiguity.Secretary.ClassicalLP
import MomentAmbiguity.Prophet.Bucketing

/-!
# Regression checks for Ramsey, classical secretary, and prophet foundations

These examples exercise boundary cases of the finite Ramsey theorem, the classical secretary
problem, and the finite prophet-bucketing argument. They use public declarations only.
-/

open scoped BigOperators Topology ENNReal NNReal

namespace MomentAmbiguity

open Filter MeasureTheory

noncomputable section

/-! ## Finite ordered Ramsey boundary cases -/

/-- Uniformity zero: the unique empty tuple has one colour. -/
example (l : ℕ) :
    ∃ n : ℕ, l ≤ n ∧ ∀ c : (Fin 0 ↪o Fin n) → Fin 2,
      ∃ H : Fin l ↪o Fin n, OrderedTupleHomogeneous c H :=
  finiteHypergraphRamsey (Fin 2) 0 l

/-- Target size zero is supported for every uniformity. -/
example (k : ℕ) :
    ∃ n : ℕ, 0 ≤ n ∧ ∀ c : (Fin k ↪o Fin n) → Fin 2,
      ∃ H : Fin 0 ↪o Fin n, OrderedTupleHomogeneous c H :=
  finiteHypergraphRamsey (Fin 2) k 0

/-- Every embedding is homogeneous for a one-colour target. -/
example {k n l : ℕ} (c : (Fin k ↪o Fin n) → Fin 1) (H : Fin l ↪o Fin n) :
    OrderedTupleHomogeneous c H := by
  refine ⟨0, fun e ↦ ?_⟩
  exact Subsingleton.elim _ _

/-- Once a Ramsey horizon works, every larger finite ordered horizon works as well. -/
example (k l : ℕ) :
    ∃ n₀ : ℕ, l ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ c : (Fin k ↪o Fin n) → Fin 2,
        ∃ H : Fin l ↪o Fin n, OrderedTupleHomogeneous c H :=
  finiteHypergraphRamsey_ge (Fin 2) k l

/-! ## Classical secretary interfaces and boundary branches -/

/-- The classical secretary limit satisfies its stated interface. -/
example : External.ClassicalSecretaryLimit := classicalSecretaryLimit

/-- The floor approximation used by the asymptotic threshold converges to `1 / e`. -/
example :
    Tendsto
      (fun m : ℕ ↦ ((⌊(Real.exp 1)⁻¹ * (m : ℝ)⌋₊ : ℝ) / (m : ℝ)))
      atTop (nhds ((Real.exp 1)⁻¹)) := by
  exact (tendsto_nat_floor_mul_div_atTop
    (le_of_lt (inv_pos.mpr (Real.exp_pos 1)))).comp tendsto_natCast_atTop_atTop

/-- The continuous limiting objective takes the exact value `1 / e` at its maximizer. -/
example : Real.negMulLog ((Real.exp 1)⁻¹) = 1 / Real.exp 1 := by
  simp only [Real.negMulLog_def]
  rw [Real.log_inv, Real.log_exp]
  ring

/-- The separate `r = 1` formula is retained at every horizon. -/
example (m : ℕ) : secretaryCandidate m 1 = (m : ℝ)⁻¹ := secretaryCandidate_one m

/-- At `m = 1`, the exceptional candidate and the finite optimum are both exactly one. -/
example : secretaryCandidate 1 1 = 1 ∧ secretaryS 1 = 1 := by
  exact ⟨by norm_num, secretaryS_one⟩

/-- The pure LP bridge also retains its horizon-one boundary. -/
example (q : Fin 1 → ℝ) (hq0 : ∀ t, 0 ≤ q t)
    (hcon : ∀ t, q t + ∑ i ∈ Finset.Iio t,
      q i / (((i.val + 1 : ℕ) : ℝ)) ≤ 1) :
    ((1 : ℕ) : ℝ)⁻¹ * ∑ t, q t ≤ secretaryS 1 :=
  classicalSecretaryLP_upper (by omega) q hq0 hcon

/-! ## Prophet bucketing and multiplication-form guarantees -/

/-- The smallest supported prophet horizon uses one bucket. -/
example : prophetBucketCount 2 = 1 := by norm_num [prophetBucketCount]

example : prophetBucketAlpha 2 = (1 : ℝ) / 4 := by
  norm_num [prophetBucketAlpha, prophetBucketCount]

/-- Concrete powers of two have their expected dyadic bucket counts. -/
example : prophetBucketCount 4 = 2 := by norm_num [prophetBucketCount]

example : prophetBucketCount 8 = 3 := by norm_num [prophetBucketCount]

example : prophetBucketCount 16 = 4 := by norm_num [prophetBucketCount]

/-- The universal definition is literally a multiplication inequality, with no ratio. -/
example {m : ℕ} (r : ValidRank m) (alpha : ℝ) (policy : ProphetPolicy m) :
    ProphetUniversalGuarantee r alpha policy ↔
      ∀ laws : Fin m → Distribution, (∀ i, HasFiniteMoments (laws i)) →
        alpha * orderStatisticBenchmark r laws ≤ prophetExpectedReward policy laws :=
  Iff.rfl

/-- Consequently a zero benchmark creates the inequality `0 <= reward`, never `0 / 0`. -/
example {m : ℕ} (r : ValidRank m) (alpha : ℝ) (policy : ProphetPolicy m)
    (laws : Fin m → Distribution) (hzero : orderStatisticBenchmark r laws = 0)
    (hreward : 0 ≤ prophetExpectedReward policy laws) :
    alpha * orderStatisticBenchmark r laws ≤ prophetExpectedReward policy laws := by
  rw [hzero, mul_zero]
  exact hreward

/-- Equality at the threshold counts as a hit, and the first such coordinate is selected. -/
example :
    prophetFirstAbove (5 : ℝ≥0)
      (![(1 : ℝ≥0), (5 : ℝ≥0), (9 : ℝ≥0)] : ProphetPath 3) =
        some (1 : Fin 3) := by
  rw [prophetFirstAbove_eq_some_iff]
  constructor
  · norm_num
  · intro i hi
    fin_cases i
    · norm_num
    · norm_num at hi
    · norm_num at hi

/-- Repeated maxima retain their multiplicity because ranks range over coordinate subsets. -/
example :
    descendingOrderStatistic (⟨2, by omega, by omega⟩ : ValidRank 3)
      (fun _ : Fin 3 ↦ (7 : ℝ≥0)) = 7 :=
  descendingOrderStatistic_const _ _

/-- The explicit logarithmic constant used in the bucket guarantee is strictly positive. -/
example : 0 < Real.log 2 / 8 := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- At the smallest horizon the public logarithmic factor is covered by the bucket factor. -/
example : (Real.log 2 / 8) / Real.log 2 ≤ prophetBucketAlpha 2 :=
  log_factor_le_prophetBucketAlpha (by norm_num)

end

end MomentAmbiguity
