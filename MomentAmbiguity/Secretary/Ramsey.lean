import MomentAmbiguity.Foundation.FiniteHypergraphRamsey
import MomentAmbiguity.Secretary.RamseyInterface

/-!
# Internal proof of the secretary finite-Ramsey interface

The generic ordered-hypergraph theorem is applied to a finite colour containing every arrival
history, stopping time, and relative-rank pattern.  Table causality transfers between partial
prefix assignments and arbitrary full extensions.
-/

open scoped BigOperators

namespace MomentAmbiguity

open External

noncomputable section

/-- The number of observations through time `t`, inclusive. -/
def secretaryPrefixLength {m : ℕ} (t : Fin m) : ℕ := t.val + 1

theorem secretaryPrefixLength_le {m : ℕ} (t : Fin m) : secretaryPrefixLength t ≤ m := by
  exact Nat.succ_le_of_lt t.isLt

/-- Increasing inclusion of prefix times into all arrival times. -/
def secretaryPrefixTimeOrderEmb {m : ℕ} (t : Fin m) :
    Fin (secretaryPrefixLength t) ↪o Fin m :=
  Fin.castLEOrderEmb (secretaryPrefixLength_le t)

theorem secretaryPrefixTimeOrderEmb_le {m : ℕ} (t : Fin m)
    (i : Fin (secretaryPrefixLength t)) : secretaryPrefixTimeOrderEmb t i ≤ t := by
  apply Fin.mk_le_mk.mpr
  exact Nat.le_of_lt_succ i.isLt

/-- Labels revealed in the observed prefix, as a finset. -/
def secretaryPrefixLabels {m : ℕ} (t : Fin m) (σ : Equiv.Perm (Fin m)) :
    Finset (Fin m) :=
  Finset.univ.map
    ((secretaryPrefixTimeOrderEmb t).toEmbedding.trans σ.toEmbedding)

/-- The requested prefix placement associated with a relative-rank permutation. Outside the
observed labels its value is irrelevant. -/
def secretaryPrefixPlacement {m : ℕ} (t : Fin m) (σ : Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin (secretaryPrefixLength t))) (label : Fin m) : Fin m :=
  if h : σ.symm label ≤ t then
    Fin.castLE (secretaryPrefixLength_le t)
      (π ⟨(σ.symm label).val, Nat.lt_succ_of_le h⟩)
  else label

theorem secretaryPrefixPlacement_arrived {m : ℕ} (t : Fin m)
    (σ : Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin (secretaryPrefixLength t)))
    (i : Fin (secretaryPrefixLength t)) :
    secretaryPrefixPlacement t σ π (σ (secretaryPrefixTimeOrderEmb t i)) =
      Fin.castLE (secretaryPrefixLength_le t) (π i) := by
  simp only [secretaryPrefixPlacement, Equiv.symm_apply_apply]
  rw [dif_pos (secretaryPrefixTimeOrderEmb_le t i)]
  rfl

theorem secretaryPrefixPlacement_injOn {m : ℕ} (t : Fin m)
    (σ : Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin (secretaryPrefixLength t))) :
    Set.InjOn (secretaryPrefixPlacement t σ π) (secretaryPrefixLabels t σ) := by
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
  change secretaryPrefixPlacement t σ π
      (σ (secretaryPrefixTimeOrderEmb t i)) =
    secretaryPrefixPlacement t σ π
      (σ (secretaryPrefixTimeOrderEmb t j)) at hab
  rw [secretaryPrefixPlacement_arrived, secretaryPrefixPlacement_arrived] at hab
  have hp : π i = π j := Fin.castLE_injective _ hab
  have hij : i = j := π.injective hp
  subst j
  rfl

/-- Extend a prescribed placement of observed labels to a permutation of all labels. -/
theorem exists_secretaryPrefixExtension {m : ℕ} (t : Fin m)
    (σ : Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin (secretaryPrefixLength t))) :
    ∃ θ : Equiv.Perm (Fin m), ∀ i : Fin (secretaryPrefixLength t),
      θ (σ (secretaryPrefixTimeOrderEmb t i)) =
        Fin.castLE (secretaryPrefixLength_le t) (π i) := by
  classical
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq
    (s := secretaryPrefixLabels t σ)
    (t := (Finset.univ : Finset (Fin m)))
    (f := secretaryPrefixPlacement t σ π)
    (by simp) (by simp) (secretaryPrefixPlacement_injOn t σ π)
  let θ : Equiv.Perm (Fin m) := Equiv.ofBijective
    (fun i ↦ (g i : Fin m)) ⟨
      (Subtype.val_injective.comp g.injective),
      fun y ↦ ⟨g.symm ⟨y, Finset.mem_univ y⟩, by simp⟩⟩
  refine ⟨θ, fun i ↦ ?_⟩
  change (g (σ (secretaryPrefixTimeOrderEmb t i)) : Fin m) = _
  rw [hg]
  · exact secretaryPrefixPlacement_arrived t σ π i
  · exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- A fixed classical extension of the requested observed-prefix placement. -/
def secretaryPrefixExtension {m : ℕ} (t : Fin m) (σ : Equiv.Perm (Fin m))
    (π : Equiv.Perm (Fin (secretaryPrefixLength t))) : Equiv.Perm (Fin m) :=
  Classical.choose (exists_secretaryPrefixExtension t σ π)

theorem secretaryPrefixExtension_arrived {m : ℕ} (t : Fin m)
    (σ : Equiv.Perm (Fin m)) (π : Equiv.Perm (Fin (secretaryPrefixLength t)))
    (i : Fin (secretaryPrefixLength t)) :
    secretaryPrefixExtension t σ π (σ (secretaryPrefixTimeOrderEmb t i)) =
      Fin.castLE (secretaryPrefixLength_le t) (π i) :=
  Classical.choose_spec (exists_secretaryPrefixExtension t σ π) i

/-- The finite colour used for secretary-table homogenisation. -/
abbrev SecretaryRamseyColour (m q : ℕ) :=
  (sigma : Equiv.Perm (Fin m)) →
    (t : Fin m) → Equiv.Perm (Fin (secretaryPrefixLength t)) → Fin (q + 1)

/-- Encode every finite table entry for every relative prefix in one finite colour. -/
def secretaryTableColour {m N q : ℕ} (table : FiniteSecretaryTable m N q)
    (K : Fin m ↪o Fin N) : SecretaryRamseyColour m q :=
  fun σ t π ↦ ⟨
    table.bin
      (permutedGridAssignment K.toEmbedding (secretaryPrefixExtension t σ π)) σ t,
    Nat.lt_succ_of_le (table.bin_le _ _ _)⟩

/-- Prefix values after applying a rank assignment to the arriving labels. -/
def secretaryPrefixAssignedEmbedding {m : ℕ} (t : Fin m)
    (σ φ : Equiv.Perm (Fin m)) : Fin (secretaryPrefixLength t) ↪ Fin m :=
  ((secretaryPrefixTimeOrderEmb t).toEmbedding.trans σ.toEmbedding).trans φ.toEmbedding

/-- The increasing enumeration of a finite embedding's range. -/
def sortedEmbeddingRange {k m : ℕ} (v : Fin k ↪ Fin m) : Fin k ↪o Fin m :=
  (Finset.univ.map v).orderEmbOfFin (by simp)

/-- The relative rank permutation of the entries of an injective finite vector. -/
def finiteRelativeRankPerm {k m : ℕ} (v : Fin k ↪ Fin m) :
    Equiv.Perm (Fin k) :=
  Equiv.ofBijective
    (fun i ↦ ((Finset.univ.map v).orderIsoOfFin (by simp)).symm
      ⟨v i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) (by
        apply (Fintype.bijective_iff_injective_and_card _).2
        refine ⟨?_, rfl⟩
        intro i j hij
        apply v.injective
        exact congrArg Subtype.val
          (((Finset.univ.map v).orderIsoOfFin (by simp)).symm.injective hij))

theorem sortedEmbeddingRange_relativeRank {k m : ℕ} (v : Fin k ↪ Fin m)
    (i : Fin k) :
    sortedEmbeddingRange v (finiteRelativeRankPerm v i) = v i := by
  change (((Finset.univ.map v).orderIsoOfFin (by simp))
    (((Finset.univ.map v).orderIsoOfFin (by simp)).symm
      ⟨v i, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) :
        (Finset.univ.map v : Finset (Fin m))) = v i
  simp

theorem finiteRelativeRankPerm_lt_iff {k m : ℕ} (v : Fin k ↪ Fin m)
    (i j : Fin k) :
    finiteRelativeRankPerm v i < finiteRelativeRankPerm v j ↔ v i < v j := by
  rw [← (sortedEmbeddingRange v).lt_iff_lt]
  simp only [sortedEmbeddingRange_relativeRank]

/-- Relative ranks of the assigned values in the observed arrival prefix. -/
def secretaryPrefixRankPerm {m : ℕ} (t : Fin m) (σ φ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (secretaryPrefixLength t)) :=
  finiteRelativeRankPerm (secretaryPrefixAssignedEmbedding t σ φ)

theorem secretaryPrefixRankPerm_lt_iff {m : ℕ} (t : Fin m)
    (σ φ : Equiv.Perm (Fin m)) (i j : Fin (secretaryPrefixLength t)) :
    secretaryPrefixRankPerm t σ φ i < secretaryPrefixRankPerm t σ φ j ↔
      φ (σ (secretaryPrefixTimeOrderEmb t i)) <
        φ (σ (secretaryPrefixTimeOrderEmb t j)) := by
  exact finiteRelativeRankPerm_lt_iff _ _ _

theorem secretaryPrefixRankPerm_eq_of_same {m : ℕ} (t : Fin m)
    (σ φ ψ : Equiv.Perm (Fin m))
    (h : SameAssignedRankPrefix t σ φ ψ) :
    secretaryPrefixRankPerm t σ φ = secretaryPrefixRankPerm t σ ψ := by
  let p := secretaryPrefixRankPerm t σ φ
  let q := secretaryPrefixRankPerm t σ ψ
  have hpq : ∀ i j, p i < p j ↔ q i < q j := by
    intro i j
    rw [secretaryPrefixRankPerm_lt_iff, secretaryPrefixRankPerm_lt_iff]
    exact h _ _ (secretaryPrefixTimeOrderEmb_le t i)
      (secretaryPrefixTimeOrderEmb_le t j)
  let e : Fin (secretaryPrefixLength t) ≃o Fin (secretaryPrefixLength t) :=
    { toEquiv := p.symm.trans q
      map_rel_iff' := by
        intro a b
        simp only [Equiv.trans_apply]
        constructor
        · intro hqle
          apply le_of_not_gt
          intro hba
          have hqba : q (p.symm b) < q (p.symm a) :=
            (hpq (p.symm b) (p.symm a)).mp (by simpa using hba)
          exact (not_lt_of_ge hqle) hqba
        · intro hab
          apply le_of_not_gt
          intro hqba
          have hba : b < a := by
            simpa using (hpq (p.symm b) (p.symm a)).mpr hqba
          exact (not_lt_of_ge hab) hba }
  apply Equiv.ext
  intro i
  apply Fin.ext
  have he := Fin.coe_orderIso_apply e (p i)
  simpa [e, p, q] using he.symm

/-- Complete `k` selected lower-block positions to an `m`-tuple by appending fixed positions in
the disjoint upper block. -/
def paddedPrefixOrderEmb {k m : ℕ} (_hkm : k ≤ m) (v : Fin k ↪ Fin m) :
    Fin m ↪o Fin (m + m) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ if hi : i.val < k then
      Fin.castAdd m (sortedEmbeddingRange v ⟨i.val, hi⟩)
    else
      Fin.natAdd m ⟨i.val - k, by omega⟩) (by
        intro i j hij
        by_cases hi : i.val < k
        · by_cases hj : j.val < k
          · simp only [hi, hj, dite_true]
            exact (Fin.castAddOrderEmb m).strictMono
              ((sortedEmbeddingRange v).strictMono (by exact hij))
          · simp only [hi, hj, dite_true, dite_false]
            apply Fin.mk_lt_mk.mpr
            have hleft := (sortedEmbeddingRange v ⟨i.val, hi⟩).isLt
            omega
        · have hj : ¬j.val < k := by omega
          simp only [hi, hj, dite_false]
          apply Fin.mk_lt_mk.mpr
          change m + (i.val - k) < m + (j.val - k)
          omega)

theorem paddedPrefixOrderEmb_castLE {k m : ℕ} (hkm : k ≤ m)
    (v : Fin k ↪ Fin m) (i : Fin k) :
    paddedPrefixOrderEmb hkm v (Fin.castLE hkm i) =
      Fin.castAdd m (sortedEmbeddingRange v i) := by
  simp [paddedPrefixOrderEmb]

theorem paddedPrefixOrderEmb_relativeRank {k m : ℕ} (hkm : k ≤ m)
    (v : Fin k ↪ Fin m) (i : Fin k) :
    paddedPrefixOrderEmb hkm v
        (Fin.castLE hkm (finiteRelativeRankPerm v i)) = Fin.castAdd m (v i) := by
  rw [paddedPrefixOrderEmb_castLE, sortedEmbeddingRange_relativeRank]

/-- The completed `m`-tuple associated with a concrete observed-prefix rank assignment. -/
def secretaryCompletedTuple {m : ℕ} (t : Fin m) (σ φ : Equiv.Perm (Fin m)) :
    Fin m ↪o Fin (m + m) :=
  paddedPrefixOrderEmb (secretaryPrefixLength_le t)
    (secretaryPrefixAssignedEmbedding t σ φ)

theorem secretaryCompletedTuple_prefixExtension {m : ℕ} (t : Fin m)
    (σ φ : Equiv.Perm (Fin m)) (i : Fin (secretaryPrefixLength t)) :
    secretaryCompletedTuple t σ φ
        (secretaryPrefixExtension t σ (secretaryPrefixRankPerm t σ φ)
          (σ (secretaryPrefixTimeOrderEmb t i))) =
      Fin.castAdd m (φ (σ (secretaryPrefixTimeOrderEmb t i))) := by
  rw [secretaryPrefixExtension_arrived]
  exact paddedPrefixOrderEmb_relativeRank
    (secretaryPrefixLength_le t) (secretaryPrefixAssignedEmbedding t σ φ) i

/-- The lower half of a homogeneous `2m`-tuple is the final ordered `m`-tuple. -/
def secretaryLowerHalfTuple {m N : ℕ} (G : Fin (m + m) ↪o Fin N) :
    Fin m ↪o Fin N :=
  (Fin.castAddOrderEmb m).trans G

/-- Table causality identifies an original lower-half assignment with its completed-prefix
representative used by the Ramsey colour. -/
theorem tableBin_eq_completedColour {m N q : ℕ}
    (table : FiniteSecretaryTable m N q) (G : Fin (m + m) ↪o Fin N)
    (σ φ : Equiv.Perm (Fin m)) (t : Fin m) :
    table.bin
        (permutedGridAssignment (secretaryLowerHalfTuple G).toEmbedding φ) σ t =
      (secretaryTableColour table ((secretaryCompletedTuple t σ φ).trans G) σ t
        (secretaryPrefixRankPerm t σ φ)).val := by
  apply table.causal
  intro time htime
  refine ⟨rfl, ?_⟩
  let i : Fin (secretaryPrefixLength t) :=
    ⟨time.val, Nat.lt_succ_of_le (Fin.mk_le_mk.mp htime)⟩
  have hi : secretaryPrefixTimeOrderEmb t i = time := Fin.ext rfl
  change G (Fin.castAdd m (φ (σ time))) =
    G (secretaryCompletedTuple t σ φ
      (secretaryPrefixExtension t σ (secretaryPrefixRankPerm t σ φ) (σ time)))
  apply congrArg G
  rw [← hi]
  exact (secretaryCompletedTuple_prefixExtension t σ φ i).symm

/-- Internal closure of the finite combinatorial interface used by `lem:ramsey-erasure`. -/
theorem finiteRamseyPrinciple : External.FiniteRamseyPrinciple := by
  intro m hm q hq
  obtain ⟨N₀, htwoN₀, hRamsey⟩ :=
    finiteHypergraphRamsey_ge (SecretaryRamseyColour m q) m (m + m)
  refine ⟨N₀, ?_, fun N hN table ↦ ?_⟩
  · exact (Nat.le_add_right m m).trans htwoN₀
  · obtain ⟨G, colour, hG⟩ := hRamsey N hN (secretaryTableColour table)
    refine ⟨(secretaryLowerHalfTuple G).toEmbedding,
      (secretaryLowerHalfTuple G).strictMono, ?_⟩
    intro σ φ ψ t hsame
    let Kφ : Fin m ↪o Fin (m + m) := secretaryCompletedTuple t σ φ
    let Kψ : Fin m ↪o Fin (m + m) := secretaryCompletedTuple t σ ψ
    let pφ : Equiv.Perm (Fin (secretaryPrefixLength t)) :=
      secretaryPrefixRankPerm t σ φ
    let pψ : Equiv.Perm (Fin (secretaryPrefixLength t)) :=
      secretaryPrefixRankPerm t σ ψ
    have hp : pφ = pψ := secretaryPrefixRankPerm_eq_of_same t σ φ ψ hsame
    have hcolourFunctions :
        secretaryTableColour table (Kφ.trans G) =
          secretaryTableColour table (Kψ.trans G) :=
      (hG Kφ).trans (hG Kψ).symm
    have hentry :
        (secretaryTableColour table (Kφ.trans G) σ t pφ).val =
          (secretaryTableColour table (Kψ.trans G) σ t pψ).val := by
      rw [hp]
      exact congrArg (fun c ↦ (c σ t pψ).val) hcolourFunctions
    calc
      table.bin
          (permutedGridAssignment (secretaryLowerHalfTuple G).toEmbedding φ) σ t =
          (secretaryTableColour table (Kφ.trans G) σ t pφ).val := by
            simpa [Kφ, pφ] using tableBin_eq_completedColour table G σ φ t
      _ = (secretaryTableColour table (Kψ.trans G) σ t pψ).val := hentry
      _ = table.bin
          (permutedGridAssignment (secretaryLowerHalfTuple G).toEmbedding ψ) σ t := by
            simpa [Kψ, pψ] using
              (tableBin_eq_completedColour table G σ ψ t).symm

end

end MomentAmbiguity
