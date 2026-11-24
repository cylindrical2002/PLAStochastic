import PLAStochastic.Index.CEPS.Scaled.MorseCoordinateDerivative
import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyDisc
import PLAStochastic.Index.CEPS.Scaled.CoordinateBudgets

/-! # Actual scaled root frequency derivatives away from the joint origin

The bound retains the scaled root coordinate as a multiplier. Its only
possible inverse drift loss is then absorbed by the real-drift Taylor error.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRoot_frequency_hasDerivAt (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    HasDerivAt (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b)
      (deriv (cepsMorseRoot D θ ρW ((b : ℂ) * lam))
        ((b : ℂ) * sign * cepsScaledRootCoordinate D θ ρW lam z b) * sign *
          (1 + (b : ℂ) * lam) / (2 * cepsScaledRootCoordinate D θ ρW lam z b)) z := by
  let r := cepsScaledRootCoordinate D θ ρW lam z (b : ℂ)
  let w : ℂ := 1 + (b : ℂ) * lam
  obtain ⟨hμ, _, _, _, _, _, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hμn : ‖(b : ℂ) * (lam : ℂ)‖ ≤ dom.μ₀ := by simpa only [← ofReal_mul, norm_real, Real.norm_eq_abs] using hμ
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z)
      (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs))
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  have hbA := ball_subset_ball (min_le_left _ _) hbC
  have hbR := ball_subset_ball (min_le_left _ _) hbA
  have hslit := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne hbR
  have hr0 : r ≠ 0 := by
    intro he
    have hs := sqrt_sq_eq (cepsScaledMorseRadicand D θ ρW lam z b)
    change r ^ 2 = _ at hs
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at hs
    rw [← hs] at hslit
    simp [mem_slitPlane_iff] at hslit
  have hrad : HasDerivAt (fun ζ => cepsScaledMorseRadicand D θ ρW lam ζ b) w z := by
    simpa only [cepsScaledMorseRadicand, w, one_mul] using!
      ((hasDerivAt_id' z).mul_const (1 + (b : ℂ) * lam)).sub_const
        ((lam : ℂ) ^ 2 * cepsMorseMinUnit D θ ρW ((b : ℂ) * lam))
  have hcoord : DifferentiableAt ℂ (fun ζ => cepsScaledRootCoordinate D θ ρW lam ζ b) z :=
    (differentiableAt_sqrt hslit).comp z hrad.differentiableAt
  have hsq := hcoord.hasDerivAt.pow 2
  have hsqFun : (fun ζ => cepsScaledRootCoordinate D θ ρW lam ζ b) ^ 2 =
      (fun ζ => cepsScaledMorseRadicand D θ ρW lam ζ b) := by
    funext ζ
    exact sqrt_sq_eq (cepsScaledMorseRadicand D θ ρW lam ζ b)
  rw [hsqFun] at hsq
  have he := hsq.unique hrad
  have hdR : HasDerivAt (fun ζ => cepsScaledRootCoordinate D θ ρW lam ζ b) (w / (2 * r)) z := by
    apply hcoord.hasDerivAt.congr_deriv
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hr0)).mpr
    change deriv (fun ζ => cepsScaledRootCoordinate D θ ρW lam ζ b) z * (2 * r) = w
    linear_combination he
  have hcoordB := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbR
  have hB0 : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  have hprod := (lt_div_iff₀ (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp
    ((mem_ball_zero_iff.mp hbA).trans_le (min_le_right _ _))
  have hrphys : ‖(b : ℂ) * sign * r‖ < dom.rmax := by
    rw [norm_mul, norm_mul]
    have hle : ‖(b : ℂ)‖ * ‖sign‖ * ‖r‖ ≤ ‖(b : ℂ)‖ * dom.scaledRootCoordinateBound lam z := by
      calc
        _ ≤ ‖(b : ℂ)‖ * 1 * dom.scaledRootCoordinateBound lam z := by gcongr
        _ = _ := by ring
    exact hle.trans_lt (by nlinarith [norm_nonneg (b : ℂ), mul_nonneg (norm_nonneg (b : ℂ)) hB0])
  have hΘ : DifferentiableAt ℂ (cepsMorseRoot D θ ρW ((b : ℂ) * lam)) ((b : ℂ) * sign * r) := by
    have hm := mem_ball_zero_iff.mpr (dom.μ_lt_chart hμn)
    have hr := mem_ball_zero_iff.mpr (hrphys.trans_le
      (by have := dom.rmax_r1; have := dom.rmax_pos; linarith : dom.rmax ≤ cepsChartRho D θ))
    have hd : DifferentiableOn ℂ (cepsMorseRoot D θ ρW ((b : ℂ) * lam))
        (ball 0 (cepsChartRho D θ)) :=
      (differentiableOn_cepsMorseRoot hW hθ hD).comp
        (f := fun r : ℂ => ((b : ℂ) * lam, r)) (by fun_prop) (fun r hr => ⟨hm, hr⟩)
    exact (hd _ hr).differentiableAt (isOpen_ball.mem_nhds hr)
  have hd := (hΘ.hasDerivAt.comp z (hdR.const_mul ((b : ℂ) * sign))).div_const (b : ℂ)
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have heq : (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) =
      (fun ζ => cepsMorseRoot D θ ρW ((b : ℂ) * lam)
        ((b : ℂ) * sign * cepsScaledRootCoordinate D θ ρW lam ζ b) / (b : ℂ)) :=
    funext fun ζ => cepsScaledSignedRoot_eq_div hW hθ hD lam ζ sign hb0
  rw [heq]
  have hcoeff : deriv (cepsMorseRoot D θ ρW ((b : ℂ) * lam)) ((b : ℂ) * sign * r) *
      ((b : ℂ) * sign * (w / (2 * r))) / (b : ℂ) =
        deriv (cepsMorseRoot D θ ρW ((b : ℂ) * lam)) ((b : ℂ) * sign * r) * sign * w / (2 * r) := by
    field_simp [hb0, hr0]
  simpa only [Function.comp_def, r, w] using hd.congr_deriv hcoeff

end PGM
