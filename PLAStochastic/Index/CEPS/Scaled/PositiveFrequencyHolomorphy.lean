import PLAStochastic.Index.CEPS.Scaled.PositiveFrequencyRoots

/-! # Actual positive-tail root holomorphy on a common frequency disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledPositiveFrequency_roots_differentiableOn (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ 1 b)
      (ball z dom.positiveFrequencyRadius) ∧
    DifferentiableOn ℂ (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ (-1) b)
      (ball z dom.positiveFrequencyRadius) := by
  let μ := b * lam
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  have hμ := (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs).1
  have hμn : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [μ, norm_real, Real.norm_eq_abs] using hμ
  have hμc := dom.μ_lt_chart hμn
  have hqnorm : ∀ ζ ∈ ball z dom.positiveFrequencyRadius, ‖q ζ‖ ≤ dom.q₀ := fun ζ hζ =>
    (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs
      (ball_subset_ball (positiveFrequencyRadius_le dom) hζ)).1.le
  have hqd : Differentiable ℂ q := by unfold q cepsComplexScaledDiscount; fun_prop
  have hsq : DifferentiableOn ℂ (fun ζ => cepsRootR D θ ρW μ (q ζ))
      (ball z dom.positiveFrequencyRadius) := by
    intro ζ hζ
    exact ((differentiableAt_sqrt
      (cepsScaledPositiveFrequency_mem_slitPlane dom hW hθ hD M lam hlam hz hb hbs hζ)).comp ζ
        ((hqd ζ).sub_const (cepsMorseMin D θ ρW μ))).differentiableWithinAt
  have hΘ : DifferentiableOn ℂ (cepsMorseRoot D θ ρW (μ : ℂ))
      (ball 0 (cepsChartRho D θ)) :=
    (differentiableOn_cepsMorseRoot hW hθ hD).comp
      ((differentiableOn_const (μ : ℂ)).prodMk differentiableOn_id)
      (fun r hr => ⟨mem_ball_zero_iff.mpr hμc, hr⟩)
  have hrmap : MapsTo (fun ζ => cepsRootR D θ ρW μ (q ζ))
      (ball z dom.positiveFrequencyRadius) (ball 0 (cepsChartRho D θ)) :=
    fun ζ hζ => mem_ball_zero_iff.mpr (dom.norm_cepsRootR_lt hW hθ hD hμn (hqnorm ζ hζ))
  have hp := (hΘ.comp hsq hrmap).div_const (b : ℂ)
  have hrneg : MapsTo (fun ζ => -cepsRootR D θ ρW μ (q ζ))
      (ball z dom.positiveFrequencyRadius) (ball 0 (cepsChartRho D θ)) := by
    intro ζ hζ
    simpa only [mem_ball_zero_iff, norm_neg] using hrmap hζ
  have ha := (hΘ.comp hsq.neg hrneg).div_const (b : ℂ)
  constructor
  · apply hp.congr
    intro ζ _
    simpa only [Function.comp_apply, cepsRootPlus, q, μ, cepsComplexScaledDiscount,
      cepsScaledDiscount, ofReal_mul] using
      cepsScaledSignedRoot_plus_actual hW hθ hD hb (z := ζ) hμc
  · apply ha.congr
    intro ζ _
    simpa only [Function.comp_apply, Pi.neg_apply, cepsRootMinus, q, μ, cepsComplexScaledDiscount,
      cepsScaledDiscount, ofReal_mul] using
      cepsScaledSignedRoot_minus_actual hW hθ hD hb (z := ζ) hμc

end PGM
