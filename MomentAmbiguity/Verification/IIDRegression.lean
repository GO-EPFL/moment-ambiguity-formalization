import MomentAmbiguity.Secretary

/-!
# Regression checks for i.i.d. secretary success

These checks exercise horizon one, repeated draws, the exact birthday constant, singleton
mixtures, and the fixed-disclosure order of quantifiers through the public interfaces.
-/

open scoped BigOperators ENNReal NNReal

namespace MomentAmbiguity

open MeasureTheory

noncomputable section

/-- At the one-observation boundary, the i.i.d. robust success probability is exactly one. -/
theorem iidRegression_horizon_one : robustSecretaryIIDValue 1 = 1 := by
  rw [full_secretary_success_iid (by norm_num), secretaryS_one]

/-- The independent and i.i.d. values agree at every supported finite horizon. -/
theorem iidRegression_values_agree {m : ℕ} (hm : 1 ≤ m) :
    robustSecretaryIIDValue m = robustSecretaryValue m := by
  rw [full_secretary_success_iid hm, full_secretary_success hm]

/-- The horizon-one birthday correction vanishes for every support size. -/
theorem iidRegression_birthday_one (k : ℕ) :
    (Nat.choose 1 2 : ℝ) / k = 0 := by norm_num

/-- The exact birthday bound has no slack for two independent draws from two values:
the two constant tuples collide, while the two distinct tuples do not. -/
theorem iidRegression_two_binary_draws :
    finiteIIDAverage (finiteCollision (m := 2) (k := 2)) = (1 : ℝ) / 2 := by
  rw [finiteIIDAverage_eq_div_pow]
  have hsum : (∑ a : Fin 2 → Fin 2, finiteCollision a) = 2 := by
    calc
      _ = ∑ p : Fin 2 × Fin 2, finiteCollision ((finTwoArrowEquiv (Fin 2)).symm p) :=
        ((finTwoArrowEquiv (Fin 2)).symm.sum_comp finiteCollision).symm
      _ = 2 := by
        norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, finTwoArrowEquiv,
          finiteCollision, Function.Injective, Fin.forall_fin_two]
  rw [hsum]
  norm_num

/-- A mixture with a single component is precisely the original probability law. -/
theorem iidRegression_singleton_mixture (law : Distribution) :
    uniformMixture (fun _ : Fin 1 ↦ law) (by norm_num) = law := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [uniformMixture_toMeasure]

/-- A common moment disclosure is fixed before either of two arbitrary policies is chosen;
both resulting hard laws belong to that same class. -/
theorem iidRegression_shared_disclosure {m : ℕ} (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ seq : MomentSequence, ∀ p q : SecretaryPolicy m,
      ∃ μ ν : Distribution, μ ∈ momentClass seq ∧ ν ∈ momentClass seq ∧
        secretarySuccessProbability p (fun _ : Fin m ↦ μ) ≤ secretaryS m + ε ∧
        secretarySuccessProbability q (fun _ : Fin m ↦ ν) ≤ secretaryS m + ε := by
  obtain ⟨seq, hseq⟩ := secretaryIID_fixedMomentClass_upper m hm ε hε
  refine ⟨seq, fun p q ↦ ?_⟩
  obtain ⟨μ, hμ, hp⟩ := hseq p
  obtain ⟨ν, hν, hq⟩ := hseq q
  exact ⟨μ, ν, hμ, hν, hp, hq⟩

end
end MomentAmbiguity
