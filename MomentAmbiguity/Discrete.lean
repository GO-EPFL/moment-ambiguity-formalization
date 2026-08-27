import MomentAmbiguity.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
Reusable discrete-law infrastructure for both separator constructions.

The manuscript specifies its laws by atoms and weights.  We build those laws as `PMF`s and then
bundle their associated measures as `ProbabilityMeasure`s.  The integral lemmas below make the
translation from manuscript sums to measure-theoretic moments explicit.
-/

open scoped ENNReal NNReal Classical

namespace MomentAmbiguity

open MeasureTheory Set

universe u v

/-- Bundle the measure associated with a probability mass function as a probability measure. -/
noncomputable def pmfProbabilityMeasure {alpha : Type u} [MeasurableSpace alpha]
    (p : PMF alpha) : ProbabilityMeasure alpha :=
  ⟨p.toMeasure, inferInstance⟩

@[simp]
theorem coe_pmfProbabilityMeasure {alpha : Type u} [MeasurableSpace alpha] (p : PMF alpha) :
    ((pmfProbabilityMeasure p : ProbabilityMeasure alpha) : Measure alpha) = p.toMeasure :=
  rfl

/-- A PMF constructed directly from a summable family of ENNReal weights. -/
def pmfOfHasSum {alpha : Type u} (w : alpha → ℝ≥0∞) (hw : HasSum w 1) : PMF alpha :=
  ⟨w, hw⟩

@[simp]
theorem pmfOfHasSum_apply {alpha : Type u} (w : alpha → ℝ≥0∞) (hw : HasSum w 1)
    (a : alpha) : pmfOfHasSum w hw a = w a :=
  rfl

/-- A finite PMF from NNReal weights with total mass one. -/
noncomputable def pmfOfFintype {alpha : Type u} [Fintype alpha]
    (w : alpha → ℝ≥0) (hw : ∑ a, w a = 1) : PMF alpha :=
  PMF.ofFintype (fun a ↦ (w a : ℝ≥0∞)) (by exact_mod_cast hw)

@[simp]
theorem pmfOfFintype_apply {alpha : Type u} [Fintype alpha]
    (w : alpha → ℝ≥0) (hw : ∑ a, w a = 1) (a : alpha) :
    pmfOfFintype w hw a = w a :=
  rfl

/-- The atomic law obtained by putting PMF mass `p i` at the point `x i`.  The map need not be
injective; coincident atoms are automatically combined by `PMF.map`. -/
noncomputable def atomicLaw {iota : Type u} {alpha : Type v} [MeasurableSpace alpha]
    (p : PMF iota) (x : iota → alpha) : ProbabilityMeasure alpha :=
  pmfProbabilityMeasure (p.map x)

@[simp]
theorem coe_atomicLaw {iota : Type u} {alpha : Type v} [MeasurableSpace alpha]
    (p : PMF iota) (x : iota → alpha) :
    ((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) = (p.map x).toMeasure :=
  rfl

/-- The mass of a measurable set under an atomic law is the PMF mass of its preimage. -/
theorem atomicLaw_toMeasure_apply {iota : Type u} {alpha : Type v}
    [MeasurableSpace iota] [MeasurableSpace alpha] (p : PMF iota) (x : iota → alpha)
    (hx : Measurable x) {s : Set alpha} (hs : MeasurableSet s) :
    ((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) s =
      p.toMeasure (x ⁻¹' s) := by
  exact PMF.toMeasure_map_apply x p s hx hs

/-- Atom formula for an arbitrary (not necessarily injective) atomic realization. -/
theorem atomicLaw_toMeasure_singleton {iota : Type u} {alpha : Type v}
    [MeasurableSpace iota] [MeasurableSpace alpha] [MeasurableSingletonClass iota]
    [MeasurableSingletonClass alpha] (p : PMF iota) (x : iota → alpha)
    (_hx : Measurable x) (a : alpha) :
    ((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) {a} =
      ∑' i, if x i = a then p i else 0 := by
  classical
  rw [coe_atomicLaw,
    PMF.toMeasure_apply_singleton (p.map x) a (MeasurableSet.singleton a)]
  simp only [PMF.map_apply, eq_comm]

/-- For injective support nodes, the mass at `x i` is exactly the original PMF weight. -/
theorem atomicLaw_toMeasure_singleton_of_injective {iota : Type u} {alpha : Type v}
    [MeasurableSpace iota] [MeasurableSpace alpha] [MeasurableSingletonClass iota]
    [MeasurableSingletonClass alpha] (p : PMF iota) (x : iota → alpha)
    (hx : Measurable x) (hinj : Function.Injective x) (i : iota) :
    ((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) {x i} = p i := by
  classical
  rw [atomicLaw_toMeasure_singleton p x hx]
  rw [tsum_eq_single i]
  · simp
  · intro j hji
    have hne : x j ≠ x i := fun h ↦ hji (hinj h)
    simp [hne]

/-- The atomic law is supported on the image of the PMF support. -/
theorem atomicLaw_toMeasure_image_support {iota : Type u} {alpha : Type v}
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p : PMF iota) (x : iota → alpha) :
    ((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) (x '' p.support) = 1 := by
  have hs : (x '' p.support).Countable := p.support_countable.image x
  apply (PMF.toMeasure_apply_eq_one_iff (p.map x) hs.measurableSet).2
  rw [PMF.support_map]

/-- Integral of a function under an atomic law as a weighted infinite sum. -/
theorem integral_atomicLaw_eq_tsum {iota : Type u} {alpha : Type v}
    [MeasurableSpace iota] [MeasurableSpace alpha] [MeasurableSingletonClass iota]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF iota) (x : iota → alpha) (f : alpha → E)
    (hx : Measurable x) (hf : StronglyMeasurable f)
    (hfi : Integrable (f ∘ x) p.toMeasure) :
    ∫ a, f a ∂((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) =
      ∑' i, (p i).toReal • f (x i) := by
  rw [coe_atomicLaw, ← PMF.toMeasure_map x p hx,
    integral_map_of_stronglyMeasurable hx hf]
  simpa only [Function.comp_apply] using PMF.integral_eq_tsum p (f ∘ x) hfi

/-- Finite version of `integral_atomicLaw_eq_tsum`; integrability is automatic. -/
theorem integral_atomicLaw_eq_sum {iota : Type u} {alpha : Type v}
    [MeasurableSpace iota] [MeasurableSpace alpha] [MeasurableSingletonClass iota]
    [Fintype iota] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : PMF iota) (x : iota → alpha) (f : alpha → E)
    (hx : Measurable x) (hf : StronglyMeasurable f) :
    ∫ a, f a ∂((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) =
      ∑ i, (p i).toReal • f (x i) := by
  rw [coe_atomicLaw, ← PMF.toMeasure_map x p hx,
    integral_map_of_stronglyMeasurable hx hf]
  simpa only [Function.comp_apply] using PMF.integral_eq_sum p (f ∘ x)

/-- Every function on a finite atomic realization is integrable after pushforward.  This records
the finiteness fact used implicitly whenever the manuscript integrates a polynomial against a
finitely supported law. -/
theorem integrable_atomicLaw_fintype {iota : Type u} {alpha : Type v}
    [MeasurableSpace iota] [MeasurableSpace alpha] [MeasurableSingletonClass iota]
    [Fintype iota] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : PMF iota) (x : iota → alpha) (f : alpha → E)
    (hx : Measurable x) (hf : StronglyMeasurable f) :
    Integrable f ((atomicLaw p x : ProbabilityMeasure alpha) : Measure alpha) := by
  rw [coe_atomicLaw, ← PMF.toMeasure_map x p hx]
  apply (integrable_map_measure hf.aestronglyMeasurable hx.aemeasurable).2
  have hfinite : IntegrableOn (f ∘ x) Set.univ p.toMeasure :=
    IntegrableOn.of_finite Set.finite_univ
  exact integrableOn_univ.mp hfinite

/-- Moment formula for an atomic nonnegative law. -/
theorem moment_atomicLaw_eq_tsum {iota : Type u} [MeasurableSpace iota]
    [MeasurableSingletonClass iota] (p : PMF iota) (x : iota → ℝ≥0)
    (hx : Measurable x) (k : ℕ)
    (hfi : Integrable (fun i ↦ ((x i : ℝ≥0) : ℝ) ^ k) p.toMeasure) :
    moment (atomicLaw p x) k = ∑' i, (p i).toReal * ((x i : ℝ≥0) : ℝ) ^ k := by
  have hf : StronglyMeasurable (momentIntegrand k) := by
    unfold momentIntegrand
    fun_prop
  simpa [moment, momentIntegrand, Function.comp_def, smul_eq_mul] using
    integral_atomicLaw_eq_tsum p x (momentIntegrand k) hx hf hfi

/-- Finite moment formula for an atomic nonnegative law. -/
theorem moment_atomicLaw_eq_sum {iota : Type u} [MeasurableSpace iota]
    [MeasurableSingletonClass iota] [Fintype iota] (p : PMF iota) (x : iota → ℝ≥0)
    (hx : Measurable x) (k : ℕ) :
    moment (atomicLaw p x) k = ∑ i, (p i).toReal * ((x i : ℝ≥0) : ℝ) ^ k := by
  have hf : StronglyMeasurable (momentIntegrand k) := by
    unfold momentIntegrand
    fun_prop
  simpa [moment, momentIntegrand, smul_eq_mul] using
    integral_atomicLaw_eq_sum p x (momentIntegrand k) hx hf

/-- Every finite atomic nonnegative law has finite moments of all orders. -/
theorem hasFiniteMoments_atomicLaw_fintype {iota : Type u} [MeasurableSpace iota]
    [MeasurableSingletonClass iota] [Fintype iota] (p : PMF iota) (x : iota → ℝ≥0)
    (hx : Measurable x) : HasFiniteMoments (atomicLaw p x) := by
  intro k
  apply integrable_atomicLaw_fintype p x (momentIntegrand k) hx
  unfold momentIntegrand
  fun_prop

end MomentAmbiguity
