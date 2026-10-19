import MomentAmbiguity.Prophet.Model

/-!
# Logarithmic prophet lower-bound specification

This file specifies the logarithmic lower bound used by the prophet results.
`Prophet/LogLowerBound.lean` proves this proposition using the dyadic-bucketing argument in
`Prophet/Bucketing.lean`. Parameterized theorems can use the named specification directly.
-/

namespace MomentAmbiguity.External

open MomentAmbiguity

/-- A valid first rank at every positive horizon. -/
def firstRank (m : ℕ) (hm : 1 ≤ m) : ValidRank m := ⟨1, le_rfl, hm⟩

/-- `prop:log-lowerbound`, the exact literature interface used by the manuscript. -/
def CorreaLogLowerBound : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ m_lb : ℕ, ∃ hm_lb : 2 ≤ m_lb,
    ∀ (m : ℕ) (hm : m_lb ≤ m),
      a / Real.log m ≤ rhoMom (firstRank m (by omega))

/-- Explicit-parameter compatibility restatement with the LaTeX label. -/
theorem correa_log_lower_bound
    (hCorrea : CorreaLogLowerBound) :
    ∃ a : ℝ, 0 < a ∧ ∃ m_lb : ℕ, ∃ hm_lb : 2 ≤ m_lb,
      ∀ (m : ℕ) (hm : m_lb ≤ m),
        a / Real.log m ≤ rhoMom (firstRank m (by omega)) :=
  hCorrea

end MomentAmbiguity.External
