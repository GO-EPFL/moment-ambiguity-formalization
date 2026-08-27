import MomentAmbiguity.Discrete
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Measurable online policies and finite product experiments

The paper's online rules are represented extensionally by Markov kernels from the disclosed
moment profile and the complete realized path to a (possibly absent) selection.  The causality
field says that the probability of selecting at time `t` depends only on the prefix through
`t`.  These kernels are the formal single-choice policy model and record prefix-adapted terminal
selection masses; `none` makes the no-selection outcome explicit.  The development does not
separately define hazard-based behavioral rules or prove an equivalence theorem for them.
-/

open scoped ENNReal NNReal BigOperators

namespace MomentAmbiguity

open MeasureTheory ProbabilityTheory Set

noncomputable section

/- Finite labels and finite action spaces carry their full σ-algebras.  These instances are
local to the formalization namespace and make every singleton decision event measurable. -/
instance measurableSpaceFin (m : ℕ) : MeasurableSpace (Fin m) := ⊤
instance measurableSingletonClassFin (m : ℕ) : MeasurableSingletonClass (Fin m) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
instance measurableSpaceOptionFin (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
instance measurableSingletonClassOptionFin (m : ℕ) :
    MeasurableSingletonClass (Option (Fin m)) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
instance measurableSpaceFinsetFin (m : ℕ) : MeasurableSpace (Finset (Fin m)) := ⊤
instance measurableSpacePermFin (m : ℕ) : MeasurableSpace (Equiv.Perm (Fin m)) := ⊤
instance measurableSingletonClassPermFin (m : ℕ) :
    MeasurableSingletonClass (Equiv.Perm (Fin m)) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

/-- The disclosed sequence for each of `m` labeled coordinates. -/
abbrev MomentProfile (m : ℕ) := Fin m → MomentSequence

/-- A fixed-order prophet path. -/
abbrev ProphetPath (m : ℕ) := Fin m → ℝ≥0

/-- A random-order secretary path consists of an arrival permutation and the labeled values. -/
abbrev SecretaryPath (m : ℕ) := Equiv.Perm (Fin m) × ProphetPath m

/-- The label and cardinal value observed at a secretary arrival time. -/
def secretaryObservation {m : ℕ} (path : SecretaryPath m) (t : Fin m) : Fin m × ℝ≥0 :=
  (path.1 t, path.2 (path.1 t))

/-- Two paths agree through (and including) time `t`. -/
def AgreeThrough {m : ℕ} {A : Type*} (t : Fin m) (x y : Fin m → A) : Prop :=
  ∀ i : Fin m, i ≤ t → x i = y i

theorem AgreeThrough.refl {m : ℕ} {A : Type*} (t : Fin m) (x : Fin m → A) :
    AgreeThrough t x x := by
  intro i hi
  rfl

theorem AgreeThrough.symm {m : ℕ} {A : Type*} {t : Fin m} {x y : Fin m → A}
    (h : AgreeThrough t x y) : AgreeThrough t y x := by
  intro i hi
  exact (h i hi).symm

/-- Secretary paths agree through `t` when all label/value observations through `t` agree. -/
def SecretaryAgreeThrough {m : ℕ} (t : Fin m) (x y : SecretaryPath m) : Prop :=
  ∀ i : Fin m, i ≤ t → secretaryObservation x i = secretaryObservation y i

/-- A measurable causal randomized single-choice rule for the fixed-order prophet problem.
The output `none` means that the rule never selects. -/
structure ProphetPolicy (m : ℕ) where
  kernel : Kernel (MomentProfile m × ProphetPath m) (Option (Fin m))
  isMarkov : IsMarkovKernel kernel
  causal : ∀ (profile : MomentProfile m) (x y : ProphetPath m) (t : Fin m),
    AgreeThrough t x y → kernel (profile, x) {some t} = kernel (profile, y) {some t}

attribute [instance] ProphetPolicy.isMarkov

/-- A measurable causal randomized secretary rule.  It receives labels and cardinal values;
the selected `Fin m` is an arrival time, rather than an ex-ante label. -/
structure SecretaryPolicy (m : ℕ) where
  kernel : Kernel (MomentProfile m × SecretaryPath m) (Option (Fin m))
  isMarkov : IsMarkovKernel kernel
  causal : ∀ (profile : MomentProfile m) (x y : SecretaryPath m) (t : Fin m),
    SecretaryAgreeThrough t x y →
      kernel (profile, x) {some t} = kernel (profile, y) {some t}

attribute [instance] SecretaryPolicy.isMarkov

/-- A terminal-set policy selecting at most `r` arrival times.  Causality is imposed on each
membership event, rather than on the full joint law, so the formal class may include more joint
laws than a sequential implementation.  The cardinality condition holds with probability one. -/
structure MultiSelectionPolicy (m r : ℕ) where
  kernel : Kernel (MomentProfile m × ProphetPath m) (Finset (Fin m))
  isMarkov : IsMarkovKernel kernel
  causal : ∀ (profile : MomentProfile m) (x y : ProphetPath m) (t : Fin m),
    AgreeThrough t x y →
      kernel (profile, x) {s | t ∈ s} = kernel (profile, y) {s | t ∈ s}
  card_le : ∀ (profile : MomentProfile m) (x : ProphetPath m),
    kernel (profile, x) {s | s.card ≤ r} = 1

attribute [instance] MultiSelectionPolicy.isMarkov

/-- The product law of independent labeled values. -/
def independentValues {m : ℕ} (laws : Fin m → Distribution) :
    ProbabilityMeasure (ProphetPath m) :=
  ProbabilityMeasure.pi laws

/-- Every coordinate of the finite product has its prescribed marginal. -/
theorem independentValues_marginal {m : ℕ} (laws : Fin m → Distribution) (i : Fin m) :
    (independentValues laws).map (measurable_pi_apply i).aemeasurable = laws i := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [ProbabilityMeasure.toMeasure_map, independentValues,
    ProbabilityMeasure.toMeasure_pi] using
    (MeasureTheory.measurePreserving_eval (fun i ↦ (laws i : Measure ℝ≥0)) i).map_eq

/-- Coordinate projections of the finite product are mutually independent. -/
theorem independentValues_iIndep {m : ℕ} (laws : Fin m → Distribution) :
    iIndepFun (fun i (x : ProphetPath m) ↦ x i) (independentValues laws : Measure _) := by
  simpa only [independentValues, ProbabilityMeasure.toMeasure_pi, id_eq] using
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun i ↦ (laws i : Measure ℝ≥0))
      (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id))

/-- The uniform law on permutations of the labels. -/
def uniformPermutation (m : ℕ) : ProbabilityMeasure (Equiv.Perm (Fin m)) :=
  pmfProbabilityMeasure (PMF.uniformOfFintype (Equiv.Perm (Fin m)))

/-- The independent product of a uniform arrival permutation and the labeled values. -/
def secretaryExperiment {m : ℕ} (laws : Fin m → Distribution) :
    ProbabilityMeasure (SecretaryPath m) :=
  (uniformPermutation m).prod (independentValues laws)

@[simp]
theorem secretaryExperiment_permutation_marginal {m : ℕ} (laws : Fin m → Distribution) :
    (secretaryExperiment laws).map measurable_fst.aemeasurable = uniformPermutation m := by
  simp [secretaryExperiment]

@[simp]
theorem secretaryExperiment_values_marginal {m : ℕ} (laws : Fin m → Distribution) :
    (secretaryExperiment laws).map measurable_snd.aemeasurable = independentValues laws := by
  simp [secretaryExperiment]

/-- Uniform arrival is independent of the entire vector of labeled values. -/
theorem secretaryExperiment_independent {m : ℕ} (laws : Fin m → Distribution) :
    IndepFun (fun x : SecretaryPath m ↦ x.1) (fun x : SecretaryPath m ↦ x.2)
      (secretaryExperiment laws : Measure _) := by
  simpa [secretaryExperiment, ProbabilityMeasure.toMeasure_prod, id_eq] using
    (ProbabilityTheory.indepFun_prod
      (μ := (uniformPermutation m : Measure (Equiv.Perm (Fin m))))
      (ν := (independentValues laws : Measure (ProphetPath m)))
      (X := id) (Y := id) measurable_id measurable_id)

/-- The actual random-order observation law. -/
def secretaryPathLaw {m : ℕ} (laws : Fin m → Distribution) :
    ProbabilityMeasure (SecretaryPath m) :=
  secretaryExperiment laws

/-- The disclosed profile of a family of laws. -/
def disclosedProfile {m : ℕ} (laws : Fin m → Distribution) : MomentProfile m :=
  fun i ↦ momentSequence (laws i)

/-- Expected reward of a single-choice prophet kernel.  Integrability is always stated by the
theorems using this real-valued integral. -/
def prophetExpectedReward {m : ℕ} (policy : ProphetPolicy m)
    (laws : Fin m → Distribution) : ℝ :=
  ∫ x, ∫ choice,
      (match choice with | none => 0 | some i => (x i : ℝ))
      ∂policy.kernel (disclosedProfile laws, x)
    ∂(independentValues laws : Measure _)

/-- Expected total reward of a policy selecting at most `r` items. -/
def multiExpectedReward {m r : ℕ} (policy : MultiSelectionPolicy m r)
    (laws : Fin m → Distribution) : ℝ :=
  ∫ x, ∫ selected, (∑ i ∈ selected, (x i : ℝ))
      ∂policy.kernel (disclosedProfile laws, x)
    ∂(independentValues laws : Measure _)

/-- Secretary success permits selecting any maximizer; `none` is failure. -/
def secretarySuccessIndicator {m : ℕ} (path : SecretaryPath m)
    (choice : Option (Fin m)) : ℝ :=
  match choice with
  | none => 0
  | some t => if ∀ s, (secretaryObservation path s).2 ≤
      (secretaryObservation path t).2 then 1 else 0

/-- Success probability of a secretary policy under independent values and uniform arrival. -/
def secretarySuccessProbabilityAtProfile {m : ℕ} (policy : SecretaryPolicy m)
    (profile : MomentProfile m) (laws : Fin m → Distribution) : ℝ :=
  ∫ path, ∫ choice, secretarySuccessIndicator path choice
      ∂policy.kernel (profile, path)
    ∂(secretaryPathLaw laws : Measure _)

/-- Success probability when the policy receives the laws' actual disclosed moments. -/
def secretarySuccessProbability {m : ℕ} (policy : SecretaryPolicy m)
    (laws : Fin m → Distribution) : ℝ :=
  secretarySuccessProbabilityAtProfile policy (disclosedProfile laws) laws

end

end MomentAmbiguity
