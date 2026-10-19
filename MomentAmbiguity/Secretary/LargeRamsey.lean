import MomentAmbiguity.Secretary.Ramsey

/-!
# Arbitrarily large homogeneous secretary sets

For i.i.d. sampling the homogeneous set must be larger than the number of arrivals, so that
repeated draws are rare.  Apply the same finite colouring as in `Secretary/Ramsey.lean` to a set of
`k + m` positions.  The upper `m` positions complete observed prefixes for every `m`-subset
of the lower `k` positions.
-/

namespace MomentAmbiguity

open External

noncomputable section

/-- Embed one lower `m`-subset together with the common upper padding block. -/
def secretarySubsetWithPadding {m k : ℕ} (J : Fin m ↪o Fin k) :
    Fin (m + m) ↪o Fin (k + m) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ if hi : i.val < m then
      Fin.castAdd m (J ⟨i.val, hi⟩)
    else
      Fin.natAdd k ⟨i.val - m, by omega⟩) (by
        intro i j hij
        by_cases hi : i.val < m
        · by_cases hj : j.val < m
          · simp only [hi, hj, dite_true]
            exact (Fin.castAddOrderEmb m).strictMono
              (J.strictMono (by exact hij))
          · simp only [hi, hj, dite_true, dite_false]
            apply Fin.mk_lt_mk.mpr
            have hleft := (J ⟨i.val, hi⟩).isLt
            omega
        · have hj : ¬j.val < m := by omega
          simp only [hi, hj, dite_false]
          apply Fin.mk_lt_mk.mpr
          change k + (i.val - m) < k + (j.val - m)
          omega)

@[simp]
theorem secretarySubsetWithPadding_castAdd {m k : ℕ} (J : Fin m ↪o Fin k)
    (i : Fin m) :
    secretarySubsetWithPadding J (Fin.castAdd m i) = Fin.castAdd m (J i) := by
  simp [secretarySubsetWithPadding]

/-- Every `m`-subset of one sufficiently large homogeneous set has the canonical assignment
property.  The set size `k` is freely chosen, independently of the horizon `m`. -/
theorem finiteRamsey_largeHomogeneousSet (m k q : ℕ)
    (_hm : 1 ≤ m) (_hmk : m ≤ k) (_hq : 1 ≤ q) :
    ∃ N₀ : ℕ, k ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ table : FiniteSecretaryTable m N q,
        ∃ H : Fin k ↪o Fin N,
          ∀ (J : Fin m ↪o Fin k) σ φ ψ t, SameAssignedRankPrefix t σ φ ψ →
            table.bin (permutedGridAssignment (J.trans H).toEmbedding φ) σ t =
              table.bin (permutedGridAssignment (J.trans H).toEmbedding ψ) σ t := by
  obtain ⟨N₀, hlarge, hRamsey⟩ :=
    finiteHypergraphRamsey_ge (SecretaryRamseyColour m q) m (k + m)
  refine ⟨N₀, (Nat.le_add_right k m).trans hlarge, fun N hN table ↦ ?_⟩
  obtain ⟨G, colour, hG⟩ := hRamsey N hN (secretaryTableColour table)
  let H : Fin k ↪o Fin N := (Fin.castAddOrderEmb m).trans G
  refine ⟨H, fun J σ φ ψ t hsame ↦ ?_⟩
  let padding := secretarySubsetWithPadding J
  let GJ : Fin (m + m) ↪o Fin N := padding.trans G
  have hlower : secretaryLowerHalfTuple GJ = J.trans H := by
    ext i
    simp [secretaryLowerHalfTuple, GJ, padding, H]
  have hcolourFunctions :
      secretaryTableColour table ((secretaryCompletedTuple t σ φ).trans GJ) =
        secretaryTableColour table ((secretaryCompletedTuple t σ ψ).trans GJ) := by
    simpa only [GJ, RelEmbedding.trans_assoc] using
      (hG ((secretaryCompletedTuple t σ φ).trans padding)).trans
        (hG ((secretaryCompletedTuple t σ ψ).trans padding)).symm
  have hp := secretaryPrefixRankPerm_eq_of_same t σ φ ψ hsame
  rw [← hlower, tableBin_eq_completedColour, tableBin_eq_completedColour, hp]
  exact congrArg (fun c ↦ (c σ t (secretaryPrefixRankPerm t σ ψ)).val) hcolourFunctions

end

end MomentAmbiguity
