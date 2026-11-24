import PLAStochastic.Index.CEPS.Scaled.ChartCoordinateDerivative
import PLAStochastic.Index.CEPS.Scaled.SignedRootJoint
import PLAStochastic.Index.CEPS.Scaled.CanonScaleCurve

/-! # Genuine root frequency derivatives on a complex scale disk -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledSignedRoot_eventuallyEq_frequency_chart (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) (sign b : ℂ) :
    (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) =ᶠ[𝓝 z]
      (fun ζ => cepsScaledMorseChart D θ ρW lam
        (sign * cepsScaledRootCoordinate D θ ρW lam ζ b) b) := by
  have hs := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne
    (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)
  have hc : Continuous (fun ζ : ℂ => cepsScaledMorseRadicand D θ ρW lam ζ 0) := by
    unfold cepsScaledMorseRadicand
    fun_prop
  have he := hc.tendsto z (isOpen_slitPlane.mem_nhds hs)
  filter_upwards [he] with ζ hζ
  have hd := (cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) ζ).1
  have hcoord : DifferentiableAt ℂ (cepsScaledRootCoordinate D θ ρW lam ζ) 0 :=
    (differentiableAt_sqrt hζ).comp 0
      ((hd 0 (mem_ball_self (dom.minimumScaleRadius_pos lam))).differentiableAt
        (ball_mem_nhds _ (dom.minimumScaleRadius_pos lam)))
  exact cepsScaledSignedRoot_eq_fixed_chart_of_differentiable hW hθ hD lam ζ sign hcoord b

include hW hθ hD in
theorem cepsScaledSignedRoot_complex_frequency_hasDerivAt (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b sign : ℂ}
    (hsign : ‖sign‖ ≤ 1) (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    HasDerivAt (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b)
      (deriv (cepsMorseRoot D θ ρW (b * lam))
        (b * sign * cepsScaledRootCoordinate D θ ρW lam z b) * sign *
          (1 + b * lam) / (2 * cepsScaledRootCoordinate D θ ρW lam z b)) z := by
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  let w : ℂ := 1 + b * lam
  have hbA := ball_subset_ball (min_le_left _ _) hb
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
      ((hasDerivAt_id' z).mul_const (1 + b * lam)).sub_const
        ((lam : ℂ) ^ 2 * cepsMorseMinUnit D θ ρW (b * lam))
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
  obtain ⟨hμ, _, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
  have hrbound := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbR
  have hB0 : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  have hprod := (lt_div_iff₀ (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp
    ((mem_ball_zero_iff.mp hbA).trans_le (min_le_right _ _))
  have hrphys : ‖b * (sign * r)‖ < dom.rmax := by
    rw [norm_mul, norm_mul]
    have hle : ‖b‖ * (‖sign‖ * ‖r‖) ≤ ‖b‖ * dom.scaledRootCoordinateBound lam z := by
      calc
        _ ≤ ‖b‖ * (1 * dom.scaledRootCoordinateBound lam z) := by gcongr
        _ = _ := by ring
    exact hle.trans_lt (by nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hB0])
  have hchart := cepsScaledMorseChart_coordinate_hasDerivAt dom hW hθ hD
    (lam := (lam : ℂ)) (r := sign * r) (b := b)
    (hμ.le.trans (by linarith [dom.μ₀_pos])) hrphys
  have hd := hchart.comp z (hdR.const_mul sign)
  have hc : deriv (cepsMorseRoot D θ ρW (b * lam)) (b * (sign * r)) *
      (sign * (w / (2 * r))) =
        deriv (cepsMorseRoot D θ ρW (b * lam)) (b * sign * r) * sign * w / (2 * r) := by
    rw [mul_assoc b sign r]
    ring
  have hd' := hd.congr_deriv hc
  exact (hd'.congr_of_eventuallyEq
    (cepsScaledSignedRoot_eventuallyEq_frequency_chart dom hW hθ hD lam hz hne sign b))

end PGM
