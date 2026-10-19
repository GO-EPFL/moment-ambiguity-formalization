import MomentAmbiguity.Prophet.Bucketing
import MomentAmbiguity.Prophet.LogLowerBoundInterface

/-!
# Closing the Correa logarithmic prophet interface

This module supplies the previously external `CorreaLogLowerBound` interface from the
measurable uniform exponential-bucketing policy formalized in `Prophet/Bucketing.lean`.

Source correspondence in the cited STOC manuscript:

* `lem:baseline` is `prophet_baseline`;
* `alg:bucket` is `prophetBucketPolicy`;
* `thm:random-bucket-threshold` is
  `prophetBucket_expectedReward_lower` together with `log_factor_le_prophetBucketAlpha`.

The weak first-crossing rule accepts values equal to the threshold.  The reward decomposition
uses strict-below indicators, so atoms at the threshold are included exactly.  The universal
guarantee is multiplication-form and therefore also covers a zero expected-maximum benchmark.
-/

namespace MomentAmbiguity

noncomputable section

/-- Internal proof of `prop:log-lowerbound`, with explicit constants `a = log(2)/8` and lower
horizon `m_lb = 2`. -/
theorem correaLogLowerBound : External.CorreaLogLowerBound := by
  refine ⟨Real.log 2 / 8, ?_, 2, le_rfl, ?_⟩
  · exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  · intro m hm
    have hfactor := log_factor_le_prophetBucketAlpha (m := m) hm
    have hrho := prophetBucketAlpha_le_rhoMom (m := m) hm
    simpa [External.firstRank, prophetFirstRank] using hfactor.trans hrho

end

end MomentAmbiguity
