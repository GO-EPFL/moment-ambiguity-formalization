import MomentAmbiguity.BinarySeparator
import MomentAmbiguity.NWaySeparator

/-!
# Maximal total-variation consequences

This module bundles the two concrete halves of the manuscript corollary and proves its final
existential consequence about one full moment class containing arbitrarily many pairwise
maximally separated laws.
-/

namespace MomentAmbiguity

noncomputable section

/-- `cor:maximal-total-variation`, `sections/impossibility.tex`: for every `N ≥ 2`, one
full moment class contains an `N`-indexed family whose distinct members have manuscript-
normalized total-variation distance one.  Pairwise distance one also proves that the indexing
map is injective, so the class really contains at least `N` distinct distributions. -/
theorem exists_full_momentClass_pairwise_maximalTV (N : ℕ) (hN : 2 ≤ N) :
    ∃ (m : MomentSequence) (mu : Fin N → Distribution),
      (∀ h, mu h ∈ momentClass m) ∧
      (∀ h h', h ≠ h' → manuscriptTV (mu h) (mu h') = 1) := by
  letI : NeZero N := ⟨by omega⟩
  let h₀ : Fin N := ⟨0, by omega⟩
  let mu : Fin N → Distribution :=
    fun h ↦ nwayDistribution 2 N (by omega) hN h
  let m : MomentSequence := momentSequence (mu h₀)
  refine ⟨m, mu, ?_, ?_⟩
  · intro h
    refine ⟨nwayDistribution_hasFiniteMoments 2 N (by omega) hN h, ?_⟩
    exact (nwayDistribution_momentEquivalent 2 N (by omega) hN h h₀).sequence_eq
  · intro h h' hne
    exact nwayDistribution_manuscriptTV_eq_one 2 N (by omega) hN hne

/-- The preceding family consists of `N` genuinely distinct laws. -/
theorem exists_full_momentClass_injective_pairwise_maximalTV (N : ℕ) (hN : 2 ≤ N) :
    ∃ (m : MomentSequence) (mu : Fin N → Distribution),
      Function.Injective mu ∧ (∀ h, mu h ∈ momentClass m) ∧
      (∀ h h', h ≠ h' → manuscriptTV (mu h) (mu h') = 1) := by
  obtain ⟨m, mu, hmem, hTV⟩ := exists_full_momentClass_pairwise_maximalTV N hN
  refine ⟨m, mu, ?_, hmem, hTV⟩
  intro h h' heq
  by_contra hne
  have hone := hTV h h' hne
  rw [heq, manuscriptTV_self] at hone
  norm_num at hone

end

end MomentAmbiguity
