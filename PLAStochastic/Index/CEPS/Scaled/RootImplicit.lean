import PLAStochastic.Index.CEPS.Scaled.CgfUnitJets
import PLAStochastic.Index.CEPS.Scaled.RootCurvePair

/-! # The genuine scaled-root equation in the removable quadratic CGF unit -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRoot_cgf_equation (lam : ℝ) {z sign b : ℂ}
    (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1)
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    cepsCgf ρW (b * cepsScaledSignedRoot D θ ρW lam z sign b) +
      b ^ 2 * (lam : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b =
        b ^ 2 * z * (1 + b * lam) := by
  have hs : ‖sign‖ ≤ 1 := by
    have hn := congrArg norm hsign
    rw [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg sign]
  have hbA := ball_subset_ball (min_le_left _ _) hb
  have hbR := ball_subset_ball (min_le_left _ _) hbA
  have hμ := (canonScaleCurve_bounds dom hW hθ hD lam hz hs hb).1
  have hμc := dom.μ_lt_chart (hμ.le.trans (by linarith [dom.μ₀_pos]))
  have hcoord := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbR
  have hbnd := mem_ball_zero_iff.mp hbA
  have hbr : ‖b‖ < dom.rmax / (4 * (1 + dom.scaledRootCoordinateBound lam z)) :=
    hbnd.trans_le (min_le_right _ _)
  have hS : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  have hprod := (lt_div_iff₀ (by positivity :
    0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp hbr
  have hr : ‖b * sign * cepsScaledRootCoordinate D θ ρW lam z b‖ < cepsChartRho D θ := by
    rw [norm_mul, norm_mul]
    have hn : ‖b‖ * ‖sign‖ * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤
        ‖b‖ * dom.scaledRootCoordinateBound lam z := by
      calc
        _ ≤ ‖b‖ * 1 * dom.scaledRootCoordinateBound lam z := by gcongr
        _ = _ := by ring
    have hm : ‖b‖ * dom.scaledRootCoordinateBound lam z < dom.rmax := by
      nlinarith [norm_nonneg b]
    exact (hn.trans_lt hm).trans_le (by linarith [dom.rmax_r1, dom.rmax_pos])
  have he := cepsCgfShift_cepsMorseRoot hW hθ hD hμc hr
  rw [← cepsScaledRootCurve_eq_morse hW hθ hD lam z sign b, cepsCgfShift] at he
  rw [mul_pow, mul_pow, hsign, mul_one, cepsScaledRootCoordinate, sqrt_sq_eq,
    ← cepsScaledMorseRadicand_actual hW hθ hD hμc] at he
  linear_combination he

include dom hW hθ hD in
theorem cepsScaledSignedRoot_unit_equation_eventually (lam : ℝ) {z sign : ℂ}
    (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    ∀ᶠ b : ℂ in 𝓝 0,
      cepsScaledSignedRoot D θ ρW lam z sign b ^ 2 *
          cepsCgfUnit ρW (b * cepsScaledSignedRoot D θ ρW lam z sign b) +
        (lam : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b = z * (1 + b * lam) := by
  let ξ := cepsScaledSignedRoot D θ ρW lam z sign
  have hs : ‖sign‖ ≤ 1 := by
    have hn := congrArg norm hsign
    rw [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg sign]
  have hR := actualRootScaleRadius_pos dom hW hθ hD lam z
  have hcξ : ContinuousAt ξ 0 :=
    (((cepsScaledSignedRoot_budget dom hW hθ hD lam hz hs).1 0
      (mem_ball_self hR)).differentiableAt (ball_mem_nhds 0 hR)).continuousAt
  have hc : ContinuousAt (fun b : ℂ => b * ξ b) 0 := continuousAt_id.mul hcξ
  have hunit := cepsCgfUnit_differentiableOn hW hθ hD
  have hu0 : (0 : ℂ) ∈ ball (0 : ℂ) (cepsCgfRadius D θ) :=
    mem_ball_self (cepsCgfRadius_pos hD hθ)
  have hcu := ((hunit 0 hu0).differentiableAt (isOpen_ball.mem_nhds hu0)).continuousAt
  have hc0 : Tendsto (fun b : ℂ => b * ξ b) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto
  have hmap : ∀ᶠ b : ℂ in 𝓝 0, b * ξ b ∈ ball (0 : ℂ) (cepsCgfRadius D θ) :=
    hc0.eventually (isOpen_ball.mem_nhds hu0)
  let F : ℂ → ℂ := fun b => ξ b ^ 2 * cepsCgfUnit ρW (b * ξ b) +
    (lam : ℂ) * ξ b - z * (1 + b * lam)
  have hcF : ContinuousAt F 0 := by
    have hcomp : ContinuousAt (fun b : ℂ => cepsCgfUnit ρW (b * ξ b)) 0 :=
      hcu.comp_of_eq hc (by simp)
    dsimp only [F]
    fun_prop
  have he : ∀ᶠ b : ℂ in 𝓝 0, b ≠ 0 → F b = 0 := by
    filter_upwards [hmap, ball_mem_nhds (0 : ℂ) (canonScaleRadius_pos dom hW hθ hD lam z)]
      with b hbU hb hb0
    have heq := cepsScaledSignedRoot_cgf_equation dom hW hθ hD lam hz hsign hb
    rw [cepsCgf_eq_mul_unit hW hθ hD hbU, mul_pow] at heq
    have ht : b ^ 2 * F b = 0 := by
      dsimp only [F, ξ]
      linear_combination heq
    exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero 2 hb0)
  have he0 : F 0 = 0 := by
    have ht : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds] with b hb hbe
      exact (hbe hb).symm)
    exact tendsto_nhds_unique (hcF.tendsto.mono_left nhdsWithin_le_nhds) ht
  filter_upwards [he] with b hb
  have hf : F b = 0 := by
    by_cases hb0 : b = 0
    · simpa only [hb0] using he0
    · exact hb hb0
  exact sub_eq_zero.mp hf

end PGM
