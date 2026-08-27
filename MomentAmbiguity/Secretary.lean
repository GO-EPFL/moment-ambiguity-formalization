import MomentAmbiguity.SecretaryUpper
import MomentAmbiguity.SecretaryLimit

/-!
# Secretary consequences under exact moment disclosure

Finite Ramsey, the exact classical secretary theorem, and its asymptotic limit are proved
internally.  Compatibility helpers retain explicit proposition arguments.  All order of
quantifiers in the manuscript's erasure lemma is retained; assignments are represented by
embeddings `Fin m ↪ Fin N`, which are exactly ordered tuples of distinct grid indices.
-/

open scoped ENNReal NNReal BigOperators Topology

namespace MomentAmbiguity

open Filter MeasureTheory Set
open External

noncomputable section

/-- A convenient exact criterion for identifying the supremal robust secretary value. -/
theorem robustSecretaryValue_eq_of_bounds {m : ℕ}
    (hupper : ∀ α ∈ secretaryFeasibleSet m, α ≤ secretaryS m)
    (hattain : ∃ policy : SecretaryPolicy m,
      SecretaryUniversalGuarantee (secretaryS m) policy) :
    robustSecretaryValue m = secretaryS m := by
  have hmem : secretaryS m ∈ secretaryFeasibleSet m :=
    ⟨secretaryS_nonneg m, hattain⟩
  apply le_antisymm
  · exact csSup_le ⟨secretaryS m, hmem⟩ hupper
  · apply le_csSup
    · exact ⟨secretaryS m, hupper⟩
    · exact hmem

theorem feasible_le_secretaryS_of_hard {m : ℕ} (hhard : SecretaryMomentUpperBound m)
    {α : ℝ} (hα : α ∈ secretaryFeasibleSet m) : α ≤ secretaryS m := by
  obtain ⟨hα0, policy, hpolicy⟩ := hα
  by_contra hle
  have hgap : 0 < (α - secretaryS m) / 2 := by linarith
  obtain ⟨laws, hfinite, hsuccess⟩ := hhard policy _ hgap
  have hguarantee := hpolicy laws hfinite
  linarith

/-- `thm:full-secretary-success`, `sections/secretary.tex`: the hard family is constructed
internally from the `N`-way laws.  The only parameters are the explicit finite-Ramsey and
classical finite-secretary interfaces. -/
theorem full_secretary_success_of_external
    (hRamsey : FiniteRamseyPrinciple) (hClassical : ClassicalSecretaryFinite)
    {m : ℕ} (hm : 1 ≤ m) :
    robustSecretaryValue m = secretaryS m := by
  have hhard := secretaryMomentUpperBound_of_external hRamsey hClassical.1 m hm
  apply robustSecretaryValue_eq_of_bounds
  · intro α hα
    exact feasible_le_secretaryS_of_hard hhard hα
  · exact classicalPointwiseAttainment_universal hClassical.2 m hm

/-- `cor:secretary-asymptotic`, `sections/secretary.tex`.  The finite equality and the limit
are deliberately separate declarations. -/
theorem secretary_asymptotic_of_external
    (hRamsey : FiniteRamseyPrinciple) (hClassical : ClassicalSecretaryFinite)
    (hLimit : ClassicalSecretaryLimit) :
    Tendsto (fun m : ℕ ↦ robustSecretaryValue m) atTop (nhds (1 / Real.exp 1)) := by
  apply hLimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact (full_secretary_success_of_external hRamsey hClassical hm).symm

/-- `thm:full-secretary-success`, `sections/secretary.tex`, with the finite Ramsey and
classical secretary inputs discharged internally. -/
theorem full_secretary_success {m : ℕ} (hm : 1 ≤ m) :
    robustSecretaryValue m = secretaryS m :=
  full_secretary_success_of_external finiteRamseyPrinciple classicalSecretaryFinite hm

/-- `cor:secretary-asymptotic`, `sections/secretary.tex`, now unconditional on external
secretary interfaces. -/
theorem secretary_asymptotic :
    Tendsto (fun m : ℕ ↦ robustSecretaryValue m) atTop
      (nhds (1 / Real.exp 1)) :=
  secretary_asymptotic_of_external finiteRamseyPrinciple classicalSecretaryFinite
    classicalSecretaryLimit

end

end MomentAmbiguity
