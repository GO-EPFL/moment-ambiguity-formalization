import MomentAmbiguity.SecretaryDefs

/-!
# Finite-Ramsey provenance interface

The specification in this file is deliberately finite and combinatorial. A
`FiniteSecretaryTable` is a table of integer colours (bounded by `q`) indexed by finite grid
assignments, arrival permutations, and times. It contains no measures, moment sequences, or
online policies. `FiniteRamseyPrinciple` is the finite homogenisation statement for such
tables. The conversion of a measurable secretary policy to this table, including
quantisation and the deterministic-law coupling, is proved internally in
`MomentAmbiguity.SecretaryUpper`; `MomentAmbiguity.SecretaryRamsey` proves an inhabitant of the
finite combinatorial specification itself.
-/

open scoped BigOperators

namespace MomentAmbiguity.External

noncomputable section

/-- Two permutations have the same observed relative-order history through time `t`. -/
def SameRelativePrefix {m : ℕ} (t : Fin m) (σ τ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i j : Fin m, i ≤ t → j ≤ t → (σ i < σ j ↔ τ i < τ j)

/-- A classical secretary rule specified by prefix-causal terminal stopping masses, including
a possible no-selection probability.  Only relative ranks in the observed prefix may influence
the mass assigned to stopping at `t`. -/
structure ClassicalSecretaryRule (m : ℕ) where
  stopProb : Equiv.Perm (Fin m) → Fin m → ℝ
  nonneg : ∀ σ t, 0 ≤ stopProb σ t
  total_le_one : ∀ σ, ∑ t, stopProb σ t ≤ 1
  causal : ∀ σ τ t, SameRelativePrefix t σ τ → stopProb σ t = stopProb τ t

/-- Success probability in the uniform-permutation classical game. Rank `m-1` is largest. -/
def classicalSecretarySuccess {m : ℕ} (hm : 1 ≤ m) (rule : ClassicalSecretaryRule m) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin m),
      rule.stopProb σ (σ.symm ⟨m - 1, by omega⟩)

/-- Exact equality of the finite labelled grid observations through time `t`. This is the
purely finite relation to which policy causality is transferred before Ramsey is invoked. -/
def GridAgreeThrough {m N : ℕ} (t : Fin m) (a b : Fin m ↪ Fin N)
    (σ τ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i : Fin m, i ≤ t → σ i = τ i ∧ a (σ i) = b (τ i)

/-- Assign the ordered homogeneous grid positions to the fixed labels through a bijection. -/
def permutedGridAssignment {m N : ℕ} (H : Fin m ↪ Fin N)
    (φ : Equiv.Perm (Fin m)) : Fin m ↪ Fin N :=
  φ.toEmbedding.trans H

/-- Two rank assignments induce the same relative value order along the same observed label
history through time `t`. -/
def SameAssignedRankPrefix {m : ℕ} (t : Fin m) (σ : Equiv.Perm (Fin m))
    (φ ψ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i j : Fin m, i ≤ t → j ≤ t →
    (φ (σ i) < φ (σ j) ↔ ψ (σ i) < ψ (σ j))

/-- A finite table of quantised stopping probabilities. The entries are finite colours in
`{0,…,q}`; `total_le` is the corresponding subprobability constraint. -/
structure FiniteSecretaryTable (m N q : ℕ) where
  bin : (Fin m ↪ Fin N) → Equiv.Perm (Fin m) → Fin m → ℕ
  bin_le : ∀ a σ t, bin a σ t ≤ q
  total_le : ∀ a σ, ∑ t, bin a σ t ≤ q
  causal : ∀ a b σ τ t, GridAgreeThrough t a b σ τ → bin a σ t = bin b τ t

/-- Success of a quantised table on an ordered grid assignment. -/
def finiteTableSuccess {m N q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (table : FiniteSecretaryTable m N q) (a : Fin m ↪ Fin N) : ℝ :=
  ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin m),
      (table.bin a σ (σ.symm ⟨m - 1, by omega⟩) : ℝ) / q

/-- The finite combinatorial Ramsey principle used by `lem:ramsey-erasure`. It produces an
ordered homogeneous value set. The fixed item-label arrival history `σ` is retained, while the
colour becomes insensitive to the actual chosen grid locations and depends only on the relative
rank pattern induced by their bijective assignment to labels. Thus label-aware policies are not
incorrectly identified. The conclusion contains no probability law, measurable kernel, moment
profile, classical policy, success functional, or coupling. -/
def FiniteRamseyPrinciple : Prop :=
  ∀ (m : ℕ), ∀ hm : 1 ≤ m, ∀ (q : ℕ), ∀ hq : 1 ≤ q,
    ∃ N₀ : ℕ, m ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N →
      ∀ table : FiniteSecretaryTable m N q,
        ∃ H : Fin m ↪ Fin N, StrictMono H ∧
          ∀ σ φ ψ t, SameAssignedRankPrefix t σ φ ψ →
            table.bin (permutedGridAssignment H φ) σ t =
              table.bin (permutedGridAssignment H ψ) σ t

end

end MomentAmbiguity.External
