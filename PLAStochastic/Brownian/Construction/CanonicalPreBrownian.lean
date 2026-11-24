import PLAStochastic.ForMathlib.MeasureTheory.Constructions.Projective.RealExtension
import Mathlib.Probability.BrownianMotion.Basic

/-! A canonical pre-Brownian probability space, constructed from its finite laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The actual projective measure on all real-valued functions of nonnegative time. -/
def canonicalPreBrownianMeasure : Measure (ℝ≥0 → ℝ) :=
  realProjectiveMeasure BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily

instance : IsProbabilityMeasure canonicalPreBrownianMeasure := by
  unfold canonicalPreBrownianMeasure
  infer_instance

/-- The coordinate process on the canonical path space. Continuity is a separate theorem. -/
def canonicalPreBrownian (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := ω t

theorem measurable_canonicalPreBrownian (t : ℝ≥0) : Measurable (canonicalPreBrownian t) :=
  measurable_pi_apply t

theorem canonicalPreBrownianMeasure_map_restrict (I : Finset ℝ≥0) :
    canonicalPreBrownianMeasure.map I.restrict = BrownianReal.projectiveFamily I :=
  realProjectiveMeasure_isProjectiveLimit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily I

/-- Existence of the genuine Gaussian process with covariance `min s t`. -/
theorem isPreBrownianReal_canonicalPreBrownian :
    IsPreBrownianReal canonicalPreBrownian canonicalPreBrownianMeasure where
  hasLaw I := ⟨(Finset.measurable_restrict I).aemeasurable,
    canonicalPreBrownianMeasure_map_restrict I⟩

theorem canonicalPreBrownian_hasLaw_sub (s t : ℝ≥0) :
    HasLaw (fun ω => canonicalPreBrownian s ω - canonicalPreBrownian t ω)
      (gaussianReal 0 (nndist (s : ℝ) (t : ℝ))) canonicalPreBrownianMeasure :=
  isPreBrownianReal_canonicalPreBrownian.hasLaw_sub s t

end BrownianAffine
