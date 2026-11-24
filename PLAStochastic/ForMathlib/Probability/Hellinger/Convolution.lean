import PLAStochastic.ForMathlib.Probability.Hellinger.Marginal
import Mathlib.Analysis.Convolution

/-!
# Translation and positive convolution of actual densities

Convolution is built by attaching translated probability densities and taking
the actual marginal integral. It is a probability density, and a common positive
smoothing kernel contracts Hellinger distance.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

def translate (p : HellingerDensity (volume : Measure ℝ)) (s : ℝ) :
    HellingerDensity (volume : Measure ℝ) where
  density x := p.density (x - s)
  measurable := p.measurable.comp (measurable_id.sub_const s)
  nonneg _ := p.nonneg _
  integrable := p.integrable.comp_sub_right s
  integral_eq_one := (integral_sub_right_eq_self p.density s).trans p.integral_eq_one

theorem hellinger_translate (p q : HellingerDensity (volume : Measure ℝ)) (s : ℝ) :
    (p.translate s).hellinger (q.translate s) = p.hellinger q := by
  have he : (p.translate s).hellinger (q.translate s) ^ 2 = p.hellinger q ^ 2 := by
    rw [hellinger_sq, hellinger_sq]
    exact integral_sub_right_eq_self
      (fun x => (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2) s
  nlinarith [(p.translate s).hellinger_nonneg (q.translate s), p.hellinger_nonneg q]

def addConvolution (p q : HellingerDensity (volume : Measure ℝ)) :
    HellingerDensity (volume : Measure ℝ) :=
  (p.joint (fun x => q.translate x)
    (q.measurable.comp (measurable_snd.sub measurable_fst))).marginalRight

theorem addConvolution_density (p q : HellingerDensity (volume : Measure ℝ)) (y : ℝ) :
    (p.addConvolution q).density y = ∫ x, p.density x * q.density (y - x) := rfl

theorem hellinger_addConvolution_le (p r q : HellingerDensity (volume : Measure ℝ)) :
    (p.addConvolution q).hellinger (r.addConvolution q) ≤ p.hellinger r :=
  hellinger_common_kernel_le p r (fun x => q.translate x)
    (q.measurable.comp (measurable_snd.sub measurable_fst))

end

end ProbabilityTheory.HellingerDensity
