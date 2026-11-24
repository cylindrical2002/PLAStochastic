import PLAStochastic.Index.GEP.Response.Score.UniformBounds
import PLAStochastic.Index.GEP.Response.KappaBound

/-!
# The output reward in the boundary flux

For a fixed base scale `C`, the boundary reward is the expected increment of
`testFn ψ` over one gap.  The bound in `influence-lipschitz.md`, Section 6, uses
only `OutTest`, never a second derivative of the output test.

This file proves the reward bound uniformly on the original regular input
class.  The coarea identity identifying the full output boundary kernel is a
separate, still open step.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

/-- The fixed-scale one-gap reward in the occupation representation. -/
def kernelBoundaryReward (ν : ProbabilityMeasure ℝ) (C : ℝ) (ψ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x, testFn ψ ((s + x) / C) - testFn ψ (s / C) ∂(ν : Measure ℝ)

/-- The increment estimate requires only an exponentially bounded first derivative. -/
theorem kernelReward_increment_le {η M C s x : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) (hs : 0 ≤ s) (hx : 0 ≤ x) :
    |testFn ψ ((s + x) / C) - testFn ψ (s / C)| ≤
      (M / C * Real.exp (η * s / C)) * (x * Real.exp (η / C * x)) := by
  have h := hψ.abs_testFn_sub_le hη (div_nonneg (add_nonneg hs hx) hC.le)
    (div_nonneg hs hC.le)
  have hle : s / C ≤ (s + x) / C := (div_le_div_iff_of_pos_right hC).2 (by linarith)
  rw [max_eq_left hle, show (s + x) / C - s / C = x / C by ring,
    abs_of_nonneg (div_nonneg hx hC.le)] at h
  calc
    _ ≤ M * Real.exp (η * ((s + x) / C)) * (x / C) := h
    _ = _ := by
      rw [show η * ((s + x) / C) = η * s / C + η / C * x by ring, Real.exp_add]
      ring

/-- A uniform tilted first-moment majorant on the regular class. -/
theorem kernelReward_tilted_first_le {θ l x : ℝ} (hθ : 0 < θ) (hl : l ≤ θ / 4) :
    x * Real.exp (l * x) ≤ (4 / θ) * Real.exp (θ / 2 * x) := by
  have hlt : l < θ / 2 := by linarith
  refine (mul_exp_le_exp_div hlt).trans ?_
  rw [div_le_iff₀ (by linarith : 0 < θ / 2 - l)]
  have hcoef : 1 ≤ (4 / θ) * (θ / 2 - l) := by
    have hdiv : 4 * l / θ ≤ 1 := (div_le_one hθ).2 (by linarith)
    have he : (4 / θ) * (θ / 2 - l) = 2 - 4 * l / θ := by field_simp; ring
    rw [he]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (θ / 2 * x)).le]

/-- The actual reward integrand is integrable; its bound is uniform in the output test. -/
theorem kernelReward_integrable {D θ vlo vhi η M C s : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η / C ≤ θ / 4) (hs : 0 ≤ s) :
    Integrable (fun x => testFn ψ ((s + x) / C) - testFn ψ (s / C)) (ν : Measure ℝ) := by
  have hM := hψ.nonneg
  have hconst : 0 ≤ M / C * Real.exp (η * s / C) := by positivity
  refine ((hν.expMom hθ).integrable.const_mul
    ((M / C * Real.exp (η * s / C)) * (4 / θ))).mono'
    ((hψ.measurable_testFn.comp ((measurable_const.add measurable_id).div_const C)).sub
      measurable_const).aestronglyMeasurable ?_
  filter_upwards [hν.ae_pos] with x hx
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (M / C * Real.exp (η * s / C)) * (x * Real.exp (η / C * x)) :=
      kernelReward_increment_le hψ hη hC hs hx.le
    _ ≤ (M / C * Real.exp (η * s / C)) * ((4 / θ) * Real.exp (θ / 2 * x)) :=
      mul_le_mul_of_nonneg_left (kernelReward_tilted_first_le hθ hscale) hconst
    _ = _ := by ring

/-- The output boundary reward is `O(M/C) exp(η s/C)` with an explicit class constant.
The statement is uniform over all measurable tests allowed by the original `OutTest`. -/
theorem kernelBoundaryReward_le {D θ vlo vhi η M C s : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η / C ≤ θ / 4) (hs : 0 ≤ s) :
    |kernelBoundaryReward ν C ψ s| ≤ M * (8 * D / θ ^ 2) / C * Real.exp (η * s / C) := by
  have hM := hψ.nonneg
  have hconst : 0 ≤ (M / C * Real.exp (η * s / C)) * (4 / θ) := by positivity
  have hpoint : ∀ᵐ x ∂(ν : Measure ℝ),
      ‖testFn ψ ((s + x) / C) - testFn ψ (s / C)‖ ≤
        ((M / C * Real.exp (η * s / C)) * (4 / θ)) * Real.exp (θ / 2 * x) := by
    filter_upwards [hν.ae_pos] with x hx
    rw [Real.norm_eq_abs]
    exact (kernelReward_increment_le hψ hη hC hs hx.le).trans (by
      calc
        _ ≤ (M / C * Real.exp (η * s / C)) * ((4 / θ) * Real.exp (θ / 2 * x)) :=
          mul_le_mul_of_nonneg_left (kernelReward_tilted_first_le hθ hscale) (by positivity)
        _ = _ := by ring)
  have hb := norm_integral_le_of_norm_le ((hν.expMom hθ).integrable.const_mul
    ((M / C * Real.exp (η * s / C)) * (4 / θ))) hpoint
  rw [integral_const_mul] at hb
  calc
    |kernelBoundaryReward ν C ψ s| ≤
        ((M / C * Real.exp (η * s / C)) * (4 / θ)) *
          ∫ x, Real.exp (θ / 2 * x) ∂(ν : Measure ℝ) := hb
    _ ≤ ((M / C * Real.exp (η * s / C)) * (4 / θ)) * (2 * D / θ) :=
      mul_le_mul_of_nonneg_left (hν.expMom hθ).le hconst
    _ = _ := by ring

/-- Measurability is joint in the physical start sum and the next gap. -/
theorem measurable_kernelBoundaryReward {η M : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (ν : ProbabilityMeasure ℝ) (C : ℝ) :
    Measurable (kernelBoundaryReward ν C ψ) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      testFn ψ ((p.1 + p.2) / C) - testFn ψ (p.1 / C)) :=
    (hψ.measurable_testFn.comp ((measurable_fst.add measurable_snd).div_const C)).sub
      (hψ.measurable_testFn.comp (measurable_fst.div_const C))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- On a band-constrained path, the physical-sum weight becomes a time weight.
The explicit factor `1/a` is retained, so this does not silently apply the
compact-slope estimate at very small slopes. -/
theorem kernelBoundaryReward_le_of_residual {D θ vlo vhi η M C s a k u v w : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η / C ≤ θ / 4) (hs : 0 ≤ s) (ha : 0 < a)
    (hu : u ≤ w) (hv : 0 ≤ v) (hres : a * s = k + u - v) :
    |kernelBoundaryReward ν C ψ s| ≤
      M * (8 * D / θ ^ 2) / C * Real.exp (η * (k + w) / (a * C)) := by
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hsum : s ≤ (k + w) / a := (le_div_iff₀ ha).2 (by nlinarith)
  have hexp : η * s / C ≤ η * (k + w) / (a * C) := by
    calc
      η * s / C ≤ η * ((k + w) / a) / C :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hη) hC.le
      _ = _ := by ring
  exact (kernelBoundaryReward_le hν hθ hψ hη hC hscale hs).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))

end

end PGM
