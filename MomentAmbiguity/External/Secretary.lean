import MomentAmbiguity.External.FiniteRamsey

/-!
# Classical secretary interfaces

These named propositions specify the two classical facts unavailable in mathlib: the exact
finite value (upper bound and an attaining relative-rank rule) and its separate asymptotic
limit.  `ClassicalSecretary.lean` and `SecretaryLimit.lean` prove internal inhabitants; the
specifications remain here for provenance and compatibility helpers.
-/

open scoped Topology BigOperators

namespace MomentAmbiguity.External

open Filter MeasureTheory

noncomputable section

/-- Pointwise success of a cardinal-value policy at a fixed value vector, averaging only the
uniform random arrival order. This contains no distributional or moment-class quantifier. -/
def pointwiseSecretarySuccess {m : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (values : ProphetPath m) : ℝ :=
  ∫ σ, ∫ choice, secretarySuccessIndicator (σ, values) choice
      ∂policy.kernel (profile, (σ, values))
    ∂(uniformPermutation m : Measure _)

/-- Classical finite-horizon upper bound, separated because `lem:ramsey-erasure` uses no
attainment result. -/
def ClassicalSecretaryUpperBound : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (rule : ClassicalSecretaryRule m),
    classicalSecretarySuccess hm rule ≤ secretaryS m

/-- Classical finite-horizon attainment in the relative-rank model only.  The lift from an
attaining rule to a measurable, tie-safe cardinal-value policy is proved internally in
`MomentAmbiguity.SecretaryUpper`. -/
def ClassicalSecretaryAttainment : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∃ rule : ClassicalSecretaryRule m,
    secretaryS m ≤ classicalSecretarySuccess hm rule

/-- Exact finite classical secretary theorem, bundled as upper bound plus attainment. -/
def ClassicalSecretaryFinite : Prop :=
  ClassicalSecretaryUpperBound ∧ ClassicalSecretaryAttainment

/-- The limit is kept separate from the exact equality at every finite horizon. -/
def ClassicalSecretaryLimit : Prop :=
  Tendsto (fun m : ℕ ↦ secretaryS m) atTop (nhds (1 / Real.exp 1))

end

end MomentAmbiguity.External
