import MomentAmbiguity.Secretary.IndependentUpper
import MomentAmbiguity.Secretary.Limit
import MomentAmbiguity.Secretary.IIDRamsey
import MomentAmbiguity.Secretary.Mixture

/-!
# Secretary success under full moment disclosure

The independent-input and i.i.d. models have the exact finite-horizon value `secretaryS m`,
which tends to `1 / exp 1`. The finite Ramsey theorem, classical secretary value, and its
limit are proved internally.

For the i.i.d. upper bound, a common moment sequence is fixed before the policy is chosen.
A large homogeneous grid is sampled independently with replacement; the collision error is
controlled before its designated-atom laws are uniformly mixed.
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

/-- `cor:secretary-asymptotic`, `sections/secretary.tex`, using the internally proved
finite secretary value and its limit. -/
theorem secretary_asymptotic :
    Tendsto (fun m : ℕ ↦ robustSecretaryValue m) atTop
      (nhds (1 / Real.exp 1)) :=
  secretary_asymptotic_of_external finiteRamseyPrinciple classicalSecretaryFinite
    classicalSecretaryLimit


/-- `lem:ramsey-erasure`: the actual i.i.d. uniform-grid experiment, with the manuscript's
exact `binom(m,2)/k` error.  The moment profile is kept fixed while evaluating the policy. -/
theorem ramsey_erasure_iid (m k : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, k ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ (grid : Fin N → ℝ≥0), StrictMono grid →
      ∀ (profile : MomentProfile m) (policy : SecretaryPolicy m),
        ∃ H : Fin k ↪o Fin N,
          secretarySuccessProbabilityAtProfile policy profile
            (fun _ : Fin m ↦ uniformMixture
              (fun j : Fin k ↦ deterministicLaw (grid (H j))) (hm.trans hmk)) ≤
                secretaryS m + ε + (Nat.choose m 2 : ℝ) / k := by
  obtain ⟨N₀, hkN₀, hRamsey⟩ := ramsey_erasure_iid_grid m k hm hmk ε hε
  refine ⟨N₀, hkN₀, fun N hN grid hgrid profile policy ↦ ?_⟩
  obtain ⟨H, hH⟩ := hRamsey N hN grid hgrid profile policy
  refine ⟨H, ?_⟩
  rw [secretarySuccessProbabilityAtProfile_uniformMixture]
  exact hH

/-- The i.i.d. hard instances all belong to one full moment class chosen before the policy.
The policy may depend on that common moment disclosure. -/
theorem secretaryIID_fixedMomentClass_upper (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ seq : MomentSequence, ∀ policy : SecretaryPolicy m,
      ∃ law : Distribution, law ∈ momentClass seq ∧
        secretarySuccessProbability policy (fun _ : Fin m ↦ law) ≤ secretaryS m + ε := by
  let η : ℝ := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((Nat.choose m 2 : ℝ) / η)
  let k : ℕ := max m (k₀ + 1)
  have hmk : m ≤ k := le_max_left _ _
  have hk : 1 ≤ k := hm.trans hmk
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk₀k : k₀ ≤ k := (Nat.le_succ k₀).trans (le_max_right _ _)
  have hchoose : (Nat.choose m 2 : ℝ) / k ≤ η := by
    have hratio : (Nat.choose m 2 : ℝ) / η < (k : ℝ) :=
      hk₀.trans_le (by exact_mod_cast hk₀k)
    apply le_of_lt
    apply (div_lt_iff₀ hkR).2
    simpa [mul_comm] using (div_lt_iff₀ hη).mp hratio
  obtain ⟨N₀, hkN₀, hRamsey⟩ := ramsey_erasure_iid_grid m k hm hmk η hη
  let N : ℕ := max N₀ 2
  have hN₀N : N₀ ≤ N := le_max_left _ _
  have hN : 2 ≤ N := le_max_right _ _
  letI : NeZero N := ⟨by omega⟩
  let δ : ℝ := ε / (3 * m)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hfirst⟩ := first_atom_concentration_exists N hN δ hδ
  let grid : Fin N → ℝ≥0 := fun h ↦ nwayNode B h.val
  have hgrid : StrictMono grid := strictMono_nwayGrid B N hB
  let hzero : Fin N := ⟨0, by omega⟩
  let seq := momentSequence (nwayDistribution B N hB hN hzero)
  let profile : MomentProfile m := fun _ ↦ seq
  refine ⟨seq, fun policy ↦ ?_⟩
  obtain ⟨H, hH⟩ := hRamsey N hN₀N grid hgrid profile policy
  let laws : Fin k → Distribution := fun j ↦ nwayDistribution B N hB hN (H j)
  let law := uniformMixture laws hk
  have hlaws : ∀ j, laws j ∈ momentClass seq := by
    intro j
    exact ⟨nwayDistribution_hasFiniteMoments B N hB hN (H j),
      (nwayDistribution_momentEquivalent B N hB hN (H j) hzero).sequence_eq⟩
  have hlaw : law ∈ momentClass seq := uniformMixture_mem_momentClass laws hk hlaws
  have hprofile : disclosedProfile (fun _ : Fin m ↦ law) = profile := by
    funext i
    exact hlaw.2
  have hatom : ∀ j : Fin k,
      1 - δ ≤ ((laws j : Measure ℝ≥0) {grid (H j)}).toReal := by
    intro j
    exact (hfirst (H j)).le
  have htransfer := secretarySuccessProbabilityAtProfile_uniformMixture_le_grid
    policy profile laws hk (fun j ↦ grid (H j)) δ hatom
  have hmdelta : (m : ℝ) * δ = η := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    dsimp [δ, η]
    field_simp
  refine ⟨law, hlaw, ?_⟩
  unfold secretarySuccessProbability
  rw [hprofile]
  change secretarySuccessProbabilityAtProfile policy profile
    (fun _ : Fin m ↦ uniformMixture laws hk) ≤ _
  change secretarySuccessProbabilityAtProfile policy profile
      (fun _ : Fin m ↦ uniformMixture laws hk) ≤
    finiteIIDAverage (fun a : Fin m → Fin k ↦
      secretarySuccessProbabilityAtProfile policy profile
        (fun i ↦ deterministicLaw (grid (H (a i))))) + m * δ at htransfer
  calc
    _ ≤ _ := htransfer
    _ ≤ (secretaryS m + η + (Nat.choose m 2 : ℝ) / k) + m * δ :=
      add_le_add hH le_rfl
    _ ≤ secretaryS m + ε := by rw [hmdelta]; dsimp [η] at *; linarith

/-- The internally constructed i.i.d. upper bound, with no external hypothesis. -/
theorem secretaryIIDMomentUpperBound (m : ℕ) (hm : 1 ≤ m) :
    SecretaryIIDMomentUpperBound m := by
  intro policy ε hε
  obtain ⟨seq, hseq⟩ := secretaryIID_fixedMomentClass_upper m hm ε hε
  obtain ⟨law, hlaw, hsuccess⟩ := hseq policy
  exact ⟨law, hlaw.1, hsuccess⟩

/-- `thm:full-secretary-success`: the exact robust i.i.d. value at every
positive finite horizon is the classical secretary value. -/
theorem full_secretary_success_iid {m : ℕ} (hm : 1 ≤ m) :
    robustSecretaryIIDValue m = secretaryS m := by
  apply robustSecretaryIIDValue_eq_of_bounds
  · intro α hα
    exact iid_feasible_le_secretaryS_of_hard (secretaryIIDMomentUpperBound m hm) hα
  · exact classicalSecretary_iid_attainment hm

/-- The independent-input and i.i.d. models have the same finite-horizon value. -/
theorem full_secretary_success_both {m : ℕ} (hm : 1 ≤ m) :
    robustSecretaryValue m = secretaryS m ∧
      robustSecretaryIIDValue m = secretaryS m :=
  ⟨full_secretary_success hm, full_secretary_success_iid hm⟩

/-- `cor:secretary-asymptotic`, for the i.i.d. robust success value. -/
theorem secretary_iid_asymptotic :
    Tendsto (fun m : ℕ ↦ robustSecretaryIIDValue m) atTop
      (nhds (1 / Real.exp 1)) := by
  apply classicalSecretaryLimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact (full_secretary_success_iid hm).symm

end

end MomentAmbiguity
