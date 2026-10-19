import MomentAmbiguity.Secretary.LargeRamsey
import MomentAmbiguity.Foundation.FiniteIID
import MomentAmbiguity.Secretary.IIDModel

/-!
# Ramsey erasure for a large uniformly sampled grid

Every distinct tuple from the homogeneous set satisfies the classical secretary bound after
averaging its assignments to item labels.  Permutation symmetrization then transfers this bound
to sampling with replacement, at the cost of the probability of a repeated grid value.
-/

open scoped BigOperators NNReal

namespace MomentAmbiguity

open External

noncomputable section

/-- On a canonical ordered subset, the uniform assignment average costs only one quantization
error beyond the optimal classical success probability. -/
theorem average_permutedGrid_success_le {m N q : ℕ} (hm : 1 ≤ m)
    (hq : 1 ≤ q) (policy : SecretaryPolicy m) (profile : MomentProfile m)
    (grid : Fin N → ℝ≥0) (hgrid : StrictMono grid) (H : Fin m ↪o Fin N)
    (hcanonical : ∀ σ φ ψ t, SameAssignedRankPrefix t σ φ ψ →
      (policyFiniteSecretaryTable q policy profile grid).bin
          (permutedGridAssignment H.toEmbedding φ) σ t =
        (policyFiniteSecretaryTable q policy profile grid).bin
          (permutedGridAssignment H.toEmbedding ψ) σ t) :
    (∑ φ : Equiv.Perm (Fin m), secretarySuccessProbabilityAtProfile policy profile
      (assignedGridLaws grid (permutedGridAssignment H.toEmbedding φ))) /
        (m.factorial : ℝ) ≤ secretaryS m + 1 / q := by
  let table := policyFiniteSecretaryTable q policy profile grid
  let card : ℝ := Fintype.card (Equiv.Perm (Fin m))
  have hcard : 0 < card := by dsimp [card]; positivity
  rw [finite_permutation_average_eq]
  calc
    _ ≤ card⁻¹ * ∑ φ : Equiv.Perm (Fin m),
        (permutedTableSuccess hm hq table H.toEmbedding φ + 1 / q) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun φ _ ↦ permutedGrid_success_le_table_add hm hq
          policy profile grid hgrid H.toEmbedding H.strictMono φ))
        (inv_nonneg.mpr hcard.le)
    _ = averagePermutedTableSuccess hm hq table H.toEmbedding + 1 / q := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, mul_add]
      simp only [nsmul_eq_mul]
      change card⁻¹ * _ + card⁻¹ * (card * (1 / (q : ℝ))) = _
      rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]
      rfl
    _ = classicalSecretarySuccess hm
        (averagedQuantizedClassicalRule hq table H.toEmbedding hcanonical) + 1 / q := by
      rw [averagePermutedTableSuccess_eq_classical hm hq table H.toEmbedding hcanonical]
    _ ≤ secretaryS m + 1 / q :=
      add_le_add (classicalSecretaryUpperBound m hm _) le_rfl

/-- A homogeneous set of any prescribed size gives the classical upper bound for i.i.d.
uniform grid values, up to quantization and collision errors. -/
theorem ramsey_erasure_iid_grid (m k : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, k ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ (grid : Fin N → ℝ≥0), StrictMono grid →
      ∀ (profile : MomentProfile m) (policy : SecretaryPolicy m),
        ∃ H : Fin k ↪o Fin N,
          finiteIIDAverage (fun a : Fin m → Fin k ↦
            secretarySuccessProbabilityAtProfile policy profile
              (fun i ↦ deterministicLaw (grid (H (a i))))) ≤
                secretaryS m + ε + (Nat.choose m 2 : ℝ) / k := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 1 ≤ q ∧ 1 / (q : ℝ) ≤ ε := by
    obtain ⟨q, hq⟩ := exists_nat_gt (1 / ε)
    refine ⟨q + 1, by omega, ?_⟩
    have hqpos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
    have hle : 1 / ε < ((q + 1 : ℕ) : ℝ) := hq.trans_le (by norm_num)
    have hone : 1 < ((q + 1 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp hle
    exact le_of_lt ((div_lt_iff₀ hqpos).2 (by simpa [mul_comm] using hone))
  obtain ⟨N₀, hkN₀, hN₀⟩ := finiteRamsey_largeHomogeneousSet m k q hm hmk hq.1
  refine ⟨N₀, hkN₀, fun N hN grid hgrid profile policy ↦ ?_⟩
  let table := policyFiniteSecretaryTable q policy profile grid
  obtain ⟨H, hcanonical⟩ := hN₀ N hN table
  refine ⟨H, ?_⟩
  let f : (Fin m → Fin k) → ℝ := fun a ↦
    secretarySuccessProbabilityAtProfile policy profile
      (fun i ↦ deterministicLaw (grid (H (a i))))
  have hf : ∀ a, f a ≤ 1 := fun a ↦
    secretarySuccessProbabilityAtProfile_le_one policy profile _
  have hperm (a : Fin m → Fin k) (ha : Function.Injective a) :
      (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) / (m.factorial : ℝ) ≤
        secretaryS m + ε := by
    let embedding : Fin m ↪ Fin k := ⟨a, ha⟩
    let J := sortedEmbeddingRange embedding
    let p := finiteRelativeRankPerm embedding
    let F : Equiv.Perm (Fin m) → ℝ := fun φ ↦
      secretarySuccessProbabilityAtProfile policy profile
        (assignedGridLaws grid (permutedGridAssignment (J.trans H).toEmbedding φ))
    have hreindex : (∑ φ : Equiv.Perm (Fin m), f (a ∘ φ)) = ∑ φ, F φ := by
      calc
        _ = ∑ φ : Equiv.Perm (Fin m), F (rightComposePerm p φ) := by
          apply Finset.sum_congr rfl
          intro φ _
          apply congrArg (secretarySuccessProbabilityAtProfile policy profile)
          funext i
          change deterministicLaw (grid (H (a (φ i)))) =
            deterministicLaw (grid (H (J (p (φ i)))))
          rw [show J (p (φ i)) = a (φ i) from
            sortedEmbeddingRange_relativeRank embedding (φ i)]
        _ = _ := (rightComposePerm p).sum_comp F
    rw [hreindex]
    exact (average_permutedGrid_success_le hm hq.1 policy profile grid hgrid
      (J.trans H) (hcanonical J)).trans (add_le_add le_rfl hq.2)
  exact finiteIIDAverage_le_of_permutation_average_choose hm (by omega) f hf
    (add_nonneg (secretaryS_nonneg m) hε.le) hperm

end

end MomentAmbiguity
