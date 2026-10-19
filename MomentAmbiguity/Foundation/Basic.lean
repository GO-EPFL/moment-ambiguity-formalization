import Mathlib

/-!
Foundational definitions for the moment-ambiguity formalization.

The manuscript works throughout with Borel probability laws on `ℝ≥0`.  Moments are
real-valued Bochner integrals of the coercion `ℝ≥0 → ℝ`; finiteness is recorded separately,
so equality of moments can never hide Lean's convention that a non-integrable integral is zero.
-/

open scoped ENNReal NNReal

namespace MomentAmbiguity

open MeasureTheory Set

/-- The probability distributions used by the manuscript. -/
abbrev Distribution := ProbabilityMeasure ℝ≥0

/-- The real integrand defining the `k`-th moment of a nonnegative law. -/
def momentIntegrand (k : ℕ) (x : ℝ≥0) : ℝ := (x : ℝ) ^ k

/-- A distribution has a finite `k`-th moment when the corresponding real function is
Bochner-integrable. -/
def HasFiniteMoment (mu : Distribution) (k : ℕ) : Prop :=
  Integrable (momentIntegrand k) (mu : Measure ℝ≥0)

/-- A distribution has finite moments of every nonnegative integer order. -/
def HasFiniteMoments (mu : Distribution) : Prop :=
  ∀ k : ℕ, HasFiniteMoment mu k

/-- The `k`-th moment.  Results using this value also carry `HasFiniteMoment`; this prevents
non-integrability from being silently identified with the value zero. -/
noncomputable def moment (mu : Distribution) (k : ℕ) : ℝ :=
  ∫ x, momentIntegrand k x ∂(mu : Measure ℝ≥0)

/-- A full moment sequence. -/
abbrev MomentSequence := ℕ → ℝ

/-- The disclosed full moment sequence of a distribution. -/
noncomputable def momentSequence (mu : Distribution) : MomentSequence :=
  fun k ↦ moment mu k

@[simp]
theorem hasFiniteMoment_zero (mu : Distribution) : HasFiniteMoment mu 0 := by
  change Integrable (fun _ : ℝ≥0 ↦ (1 : ℝ)) (mu : Measure ℝ≥0)
  exact integrable_const (1 : ℝ)

@[simp]
theorem moment_zero (mu : Distribution) : moment mu 0 = 1 := by
  simp [moment, momentIntegrand]

/-- `sections/preliminaries.tex`, lines 19--23: distributions agree on all moments iff all
moments on both sides are finite and their full moment sequences agree. -/
structure MomentEquivalent (mu nu : Distribution) : Prop where
  left_finite : HasFiniteMoments mu
  right_finite : HasFiniteMoments nu
  sequence_eq : momentSequence mu = momentSequence nu

namespace MomentEquivalent

protected theorem refl {mu : Distribution} (hmu : HasFiniteMoments mu) :
    MomentEquivalent mu mu :=
  ⟨hmu, hmu, rfl⟩

protected theorem symm {mu nu : Distribution} (h : MomentEquivalent mu nu) :
    MomentEquivalent nu mu :=
  ⟨h.right_finite, h.left_finite, h.sequence_eq.symm⟩

protected theorem trans {mu nu xi : Distribution} (hmunu : MomentEquivalent mu nu)
    (hnuxi : MomentEquivalent nu xi) : MomentEquivalent mu xi :=
  ⟨hmunu.left_finite, hnuxi.right_finite, hmunu.sequence_eq.trans hnuxi.sequence_eq⟩

theorem moment_eq {mu nu : Distribution} (h : MomentEquivalent mu nu) (k : ℕ) :
    moment mu k = moment nu k :=
  congrFun h.sequence_eq k

end MomentEquivalent

/-- `def:stieltjes-type-class`: the full moment class associated with a prescribed sequence. -/
def momentClass (m : MomentSequence) : Set Distribution :=
  {mu | HasFiniteMoments mu ∧ momentSequence mu = m}

/-- `def:stieltjes-type-class`: for the prescribed moment sequence `m`, a Stieltjes-type class
is a non-singleton subfamily of `momentClass m`.  The sequence remains an explicit argument to
preserve the manuscript's quantifier order. -/
def IsStieltjesTypeClass (m : MomentSequence) (S : Set Distribution) : Prop :=
  S ⊆ momentClass m ∧ ∃ mu ∈ S, ∃ nu ∈ S, mu ≠ nu

/-- Existential wrapper for statements where the common moment sequence is not named. -/
def IsSomeStieltjesTypeClass (S : Set Distribution) : Prop :=
  ∃ m : MomentSequence, IsStieltjesTypeClass m S

theorem mem_momentClass_iff {m : MomentSequence} {mu : Distribution} :
    mu ∈ momentClass m ↔ HasFiniteMoments mu ∧ momentSequence mu = m :=
  Iff.rfl

theorem momentEquivalent_iff_same_momentClass {mu nu : Distribution} :
    MomentEquivalent mu nu ↔
      ∃ m : MomentSequence, mu ∈ momentClass m ∧ nu ∈ momentClass m := by
  constructor
  · intro h
    exact ⟨momentSequence mu, ⟨h.left_finite, rfl⟩,
      h.right_finite, h.sequence_eq.symm⟩
  · rintro ⟨m, ⟨hmu, hm⟩, ⟨hnu, hn⟩⟩
    exact ⟨hmu, hnu, hm.trans hn.symm⟩

/-- `def:moment-based-policy`: an abstract policy is moment-based when its dependence on the
unknown distribution factors through the disclosed full moment sequence.  `Observation`
contains all online history, so this definition is reusable for each application. -/
def IsMomentBased {Observation Action : Type*}
    [MeasurableSpace Observation] [MeasurableSpace Action]
    (policy : Distribution → Observation → Action) : Prop :=
  ∃ rule : MomentSequence → Observation → Action,
    Measurable (Function.uncurry rule) ∧
      ∀ (mu : Distribution), HasFiniteMoments mu →
        ∀ observation, policy mu observation = rule (momentSequence mu) observation

/-- Moment-based policies cannot distinguish moment-equivalent laws before receiving different
online observations. -/
theorem IsMomentBased.eq_of_momentEquivalent {Observation Action : Type*}
    [MeasurableSpace Observation] [MeasurableSpace Action]
    {policy : Distribution → Observation → Action} (hpolicy : IsMomentBased policy)
    {mu nu : Distribution} (hmunu : MomentEquivalent mu nu) (observation : Observation) :
    policy mu observation = policy nu observation := by
  obtain ⟨rule, _hrule_measurable, hrule⟩ := hpolicy
  rw [hrule mu hmunu.left_finite observation, hrule nu hmunu.right_finite observation,
    hmunu.sequence_eq]

/-- Probability gap on one measurable event.  The `max - min` expression is the nonnegative
version of the manuscript's absolute difference. -/
def probabilityGap (a b : ℝ≥0) : ℝ≥0 :=
  (a ⊔ b) - (a ⊓ b)

/-- `sections/preliminaries.tex`, lines 10--14: manuscript-normalized total variation,
`sup_A |mu(A)-nu(A)|`, valued in `ℝ≥0∞` so the supremum is definitionally available. -/
noncomputable def manuscriptTV {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : ProbabilityMeasure Omega) : ℝ≥0∞ :=
  ⨆ A : {s : Set Omega // MeasurableSet s},
    ((probabilityGap (mu A.1) (nu A.1) : ℝ≥0) : ℝ≥0∞)

theorem probabilityGap_le_one {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : ProbabilityMeasure Omega) (s : Set Omega) :
    probabilityGap (mu s) (nu s) ≤ 1 := by
  exact tsub_le_self.trans (max_le (mu.apply_le_one s) (nu.apply_le_one s))

/-- The manuscript normalization places total variation in `[0,1]`. -/
theorem manuscriptTV_le_one {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : ProbabilityMeasure Omega) : manuscriptTV mu nu ≤ 1 := by
  refine iSup_le fun A ↦ ?_
  exact ENNReal.coe_le_coe.mpr (probabilityGap_le_one mu nu A.1)

/-- The probability gap of any measurable event is bounded by manuscript total variation. -/
theorem probabilityGap_le_manuscriptTV {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : ProbabilityMeasure Omega) {s : Set Omega} (hs : MeasurableSet s) :
    ((probabilityGap (mu s) (nu s) : ℝ≥0) : ℝ≥0∞) ≤ manuscriptTV mu nu := by
  exact le_iSup (fun A : {t : Set Omega // MeasurableSet t} ↦
    ((probabilityGap (mu A.1) (nu A.1) : ℝ≥0) : ℝ≥0∞)) ⟨s, hs⟩

@[simp]
theorem manuscriptTV_self {Omega : Type*} [MeasurableSpace Omega]
    (mu : ProbabilityMeasure Omega) : manuscriptTV mu mu = 0 := by
  apply le_antisymm
  · refine iSup_le fun A ↦ ?_
    simp [probabilityGap]
  · exact bot_le

theorem manuscriptTV_comm {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : ProbabilityMeasure Omega) : manuscriptTV mu nu = manuscriptTV nu mu := by
  unfold manuscriptTV probabilityGap
  congr 1
  funext A
  rw [max_comm (mu A.1) (nu A.1), min_comm (mu A.1) (nu A.1)]

/-- A measurable event carrying all mass of one law and no mass of another witnesses maximal
manuscript total variation.  This is the generic support-separation lemma used later. -/
theorem manuscriptTV_eq_one_of_separating_set {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : ProbabilityMeasure Omega) {s : Set Omega} (hs : MeasurableSet s)
    (hmu : mu s = 1) (hnu : nu s = 0) : manuscriptTV mu nu = 1 := by
  apply le_antisymm (manuscriptTV_le_one mu nu)
  have hgap := probabilityGap_le_manuscriptTV mu nu hs
  simpa [hmu, hnu, probabilityGap] using hgap

/-- Exact measure-one support on a specified carrier.  This is the measure-theoretic meaning of
"supported on" used for the manuscript's discrete separators; no topological closure is intended.
-/
def SupportedOn {Omega : Type*} [MeasurableSpace Omega]
    (mu : ProbabilityMeasure Omega) (s : Set Omega) : Prop :=
  mu s = 1

/-- Descriptive synonym emphasizing that this is exact, rather than quantitative,
concentration. -/
abbrev ConcentratedExactlyOn {Omega : Type*} [MeasurableSpace Omega]
    (mu : ProbabilityMeasure Omega) (s : Set Omega) : Prop :=
  SupportedOn mu s

theorem SupportedOn.mono {Omega : Type*} [MeasurableSpace Omega]
    {mu : ProbabilityMeasure Omega} {s t : Set Omega}
    (h : SupportedOn mu s) (hst : s ⊆ t) : SupportedOn mu t := by
  unfold SupportedOn at h ⊢
  apply le_antisymm (mu.apply_le_one t)
  exact h ▸ mu.apply_mono hst

/-- A quantitative support-concentration predicate. -/
def ConcentratedOn {Omega : Type*} [MeasurableSpace Omega]
    (mu : ProbabilityMeasure Omega) (s : Set Omega) (epsilon : ℝ≥0) : Prop :=
  1 - epsilon ≤ mu s

/-- Concentration at a designated atom. -/
def ConcentratedAt {Omega : Type*} [MeasurableSpace Omega]
    (mu : ProbabilityMeasure Omega) (x : Omega) (epsilon : ℝ≥0) : Prop :=
  ConcentratedOn mu {x} epsilon

theorem ConcentratedOn.mono {Omega : Type*} [MeasurableSpace Omega]
    {mu : ProbabilityMeasure Omega} {s t : Set Omega} {epsilon : ℝ≥0}
    (h : ConcentratedOn mu s epsilon) (hst : s ⊆ t) : ConcentratedOn mu t epsilon := by
  unfold ConcentratedOn at h ⊢
  exact le_trans h (mu.apply_mono hst)

end MomentAmbiguity
