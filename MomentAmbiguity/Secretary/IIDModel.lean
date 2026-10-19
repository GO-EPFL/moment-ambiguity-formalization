import MomentAmbiguity.Secretary.IndependentUpper

/-!
# Secretary success restricted to i.i.d. inputs

The policy is chosen knowing that the input law is i.i.d. It may use cardinal values and
item labels, but its performance obligation is restricted to constant families of laws.
No guarantee on non-identically distributed inputs is imposed in this model.
-/

open scoped BigOperators ENNReal NNReal Topology

namespace MomentAmbiguity

open MeasureTheory Set Filter

noncomputable section

theorem secretarySuccessProbabilityAtProfile_nonneg {m : ℕ}
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) :
    0 ≤ secretarySuccessProbabilityAtProfile policy profile laws := by
  exact integral_nonneg (secretaryConditionalSuccess_nonneg policy profile)

theorem secretarySuccessProbabilityAtProfile_le_one {m : ℕ}
    (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (laws : Fin m → Distribution) :
    secretarySuccessProbabilityAtProfile policy profile laws ≤ 1 := by
  have hf : Integrable (secretaryConditionalSuccess policy profile)
      (secretaryPathLaw laws : Measure _) := by
    apply Integrable.of_bound
      (stronglyMeasurable_secretaryConditionalSuccess policy profile).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun path ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (secretaryConditionalSuccess_nonneg policy profile path)]
      exact secretaryConditionalSuccess_le_one policy profile path
  calc
    secretarySuccessProbabilityAtProfile policy profile laws ≤
        ∫ _path : SecretaryPath m, (1 : ℝ)
          ∂(secretaryPathLaw laws : Measure (SecretaryPath m)) :=
      integral_mono hf (integrable_const 1)
        (secretaryConditionalSuccess_le_one policy profile)
    _ = 1 := by simp

/-- A universal guarantee restricted to i.i.d. laws.  The same policy is evaluated under
every possible common moment disclosure and every law compatible with it. -/
def SecretaryIIDUniversalGuarantee {m : ℕ} (α : ℝ) (policy : SecretaryPolicy m) : Prop :=
  ∀ law : Distribution, HasFiniteMoments law →
    α ≤ secretarySuccessProbability policy (fun _ : Fin m ↦ law)

def secretaryIIDFeasibleSet (m : ℕ) : Set ℝ :=
  {α | 0 ≤ α ∧ ∃ policy : SecretaryPolicy m, SecretaryIIDUniversalGuarantee α policy}

/-- The robust i.i.d. success value in `thm:full-secretary-success`. -/
def robustSecretaryIIDValue (m : ℕ) : ℝ := sSup (secretaryIIDFeasibleSet m)

theorem SecretaryUniversalGuarantee.iid {m : ℕ} {α : ℝ} {policy : SecretaryPolicy m}
    (h : SecretaryUniversalGuarantee α policy) :
    SecretaryIIDUniversalGuarantee α policy := by
  intro law hfinite
  exact h (fun _ ↦ law) (fun _ ↦ hfinite)

theorem secretaryFeasibleSet_subset_iid (m : ℕ) :
    secretaryFeasibleSet m ⊆ secretaryIIDFeasibleSet m := by
  rintro α ⟨hα, policy, hpolicy⟩
  exact ⟨hα, policy, hpolicy.iid⟩

theorem classicalSecretary_iid_attainment {m : ℕ} (hm : 1 ≤ m) :
    ∃ policy : SecretaryPolicy m, SecretaryIIDUniversalGuarantee (secretaryS m) policy := by
  obtain ⟨policy, hpolicy⟩ :=
    classicalPointwiseAttainment_universal classicalSecretaryAttainment m hm
  exact ⟨policy, hpolicy.iid⟩

/-- A hard i.i.d. law may depend on the policy and the requested additive error. -/
def SecretaryIIDMomentUpperBound (m : ℕ) : Prop :=
  ∀ policy : SecretaryPolicy m, ∀ ε : ℝ, 0 < ε →
    ∃ law : Distribution, HasFiniteMoments law ∧
      secretarySuccessProbability policy (fun _ : Fin m ↦ law) ≤ secretaryS m + ε

theorem iid_feasible_le_secretaryS_of_hard {m : ℕ}
    (hhard : SecretaryIIDMomentUpperBound m)
    {α : ℝ} (hα : α ∈ secretaryIIDFeasibleSet m) : α ≤ secretaryS m := by
  obtain ⟨hα0, policy, hpolicy⟩ := hα
  by_contra hle
  have hgap : 0 < (α - secretaryS m) / 2 := by linarith
  obtain ⟨law, hfinite, hsuccess⟩ := hhard policy _ hgap
  have hguarantee := hpolicy law hfinite
  linarith

theorem robustSecretaryIIDValue_eq_of_bounds {m : ℕ}
    (hupper : ∀ α ∈ secretaryIIDFeasibleSet m, α ≤ secretaryS m)
    (hattain : ∃ policy : SecretaryPolicy m,
      SecretaryIIDUniversalGuarantee (secretaryS m) policy) :
    robustSecretaryIIDValue m = secretaryS m := by
  have hmem : secretaryS m ∈ secretaryIIDFeasibleSet m :=
    ⟨secretaryS_nonneg m, hattain⟩
  apply le_antisymm
  · exact csSup_le ⟨secretaryS m, hmem⟩ hupper
  · exact le_csSup ⟨secretaryS m, hupper⟩ hmem

end

end MomentAmbiguity
