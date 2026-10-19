import MomentAmbiguity.Foundation.OnlinePolicy

/-!
# Finite-horizon secretary definitions

The classical value is defined for every natural horizon, with value zero at horizon zero.  At
positive horizons it is the manuscript's finite maximum.  The `r = 1` candidate is a separate
branch equal to `1/m`, so no term `1/(r-1)` is ever evaluated at zero.
-/

open scoped BigOperators ENNReal NNReal

namespace MomentAmbiguity

open MeasureTheory Set

noncomputable section

/-- Success probability of the classical skip-then-record rule with threshold `r`. -/
def secretaryCandidate (m r : ℕ) : ℝ :=
  if r = 1 then (m : ℝ)⁻¹
  else ((r - 1 : ℕ) : ℝ) / m *
    ∑ t ∈ Finset.Icc r m, (((t - 1 : ℕ) : ℝ)⁻¹)

@[simp]
theorem secretaryCandidate_one (m : ℕ) : secretaryCandidate m 1 = (m : ℝ)⁻¹ := by
  simp [secretaryCandidate]

/-- The exact classical finite-horizon value `s_m`, with a total zero-horizon convention. -/
def secretaryS (m : ℕ) : ℝ :=
  if hm : 1 ≤ m then
    (Finset.Icc 1 m).sup'
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hm⟩⟩ (secretaryCandidate m)
  else 0

theorem secretaryS_eq_max {m : ℕ} (hm : 1 ≤ m) :
    secretaryS m = (Finset.Icc 1 m).sup'
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hm⟩⟩ (secretaryCandidate m) := by
  simp [secretaryS, hm]

@[simp]
theorem secretaryS_zero : secretaryS 0 = 0 := by simp [secretaryS]

@[simp]
theorem secretaryS_one : secretaryS 1 = 1 := by
  rw [secretaryS_eq_max (by omega)]
  simp [secretaryCandidate]

theorem secretaryCandidate_nonneg (m r : ℕ) : 0 ≤ secretaryCandidate m r := by
  rw [secretaryCandidate]
  split
  · positivity
  · exact mul_nonneg (div_nonneg (by positivity) (by positivity))
      (Finset.sum_nonneg fun _ _ ↦ by positivity)

theorem secretaryS_nonneg (m : ℕ) : 0 ≤ secretaryS m := by
  by_cases hm : 1 ≤ m
  · rw [secretaryS_eq_max hm]
    obtain ⟨r, hr⟩ := (show (Finset.Icc 1 m).Nonempty from
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hm⟩⟩)
    exact (secretaryCandidate_nonneg m r).trans
      (Finset.le_sup' (s := Finset.Icc 1 m) (f := secretaryCandidate m) hr)
  · simp [secretaryS, hm]

/-- A moment-based secretary policy guarantees `alpha` uniformly over all compatible
independent laws. -/
def SecretaryUniversalGuarantee {m : ℕ} (alpha : ℝ) (policy : SecretaryPolicy m) : Prop :=
  ∀ laws : Fin m → Distribution, (∀ i, HasFiniteMoments (laws i)) →
    alpha ≤ secretarySuccessProbability policy laws

def secretaryFeasibleSet (m : ℕ) : Set ℝ :=
  {alpha | 0 ≤ alpha ∧ ∃ policy : SecretaryPolicy m,
    SecretaryUniversalGuarantee alpha policy}

/-- Optimal robust success probability under exact moment disclosure. -/
def robustSecretaryValue (m : ℕ) : ℝ := sSup (secretaryFeasibleSet m)

end

end MomentAmbiguity
