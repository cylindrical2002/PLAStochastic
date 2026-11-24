import PLAStochastic.Index.CEPS.Scaled.TruePhysicalDisc
import PLAStochastic.Index.CEPS.Normal.ActualHalfDiscHolomorphy

/-! # Genuine frequency differentiation of the true scaled bridge

The physical discount derivative is taken with drift and width fixed.
Full-disc physical identification pays the open neighborhood at imaginary
frequency points, including the merged zero-discount point.
-/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridge_hasDerivAt_frequency {b lam : ℝ} (hb : 0 < b)
    (hμ : |b * lam| ≤ dom.μ₀) {z : ℂ}
    (hq : ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀)
    (hre : 0 ≤ (cepsComplexScaledDiscount lam z b).re)
    (hl : dom.normalWidthThreshold ≤ (1 + b * lam) / b) :
    HasDerivAt (fun z => cepsScaledTrueBridge dom ρW lam z b)
      ((b : ℂ) * (1 + (b : ℂ) * lam) *
        deriv (fun q => (cepsWHNormalData D θ ρW ((b * lam : ℝ) : ℂ) q).regularBridge
          (dom.canonL ρW) ((b * lam : ℝ) : ℂ) q (((1 + b * lam) / b : ℝ) : ℂ))
            (cepsComplexScaledDiscount lam z b)) z := by
  let μ := b * lam
  let l := (1 + b * lam) / b
  let q : ℂ → ℂ := fun z => cepsComplexScaledDiscount lam z b
  let F : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨ε, hε, _, hFb⟩ := cepsNormal_actual_holomorphic_near_halfDisc dom hW hθ hD hμ hq hre
    (t := 0) (by simpa using half_pos dom.c₀_pos) hl
  have hF : DifferentiableAt ℂ F (q z) := (hFb _ (mem_ball_self hε)).differentiableAt (ball_mem_nhds _ hε)
  have hqderiv : HasDerivAt q ((b : ℂ) ^ 2 * (1 + (b : ℂ) * lam)) z := by
    simpa only [q, cepsComplexScaledDiscount, mul_one] using!
      (((hasDerivAt_id' z).const_mul ((b : ℂ) ^ 2)).mul_const (1 + (b : ℂ) * lam))
  have h := (hF.hasDerivAt.comp z hqderiv).div_const (b : ℂ)
  have hev : (fun z => cepsScaledTrueBridge dom ρW lam z b) =ᶠ[𝓝 z] fun z => F (q z) / (b : ℂ) := by
    have hset : ∀ᶠ z' in 𝓝 z, q z' ∈ ball (0 : ℂ) dom.q₀ :=
      hqderiv.continuousAt.tendsto (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq))
    filter_upwards [hset] with z' hz'
    have he := cepsScaledTrueBridge_eq_actual_on_discount_disc dom hW hθ hD hb hμ
      (mem_ball_zero_iff.mp hz').le
    have he' : (b : ℂ) * cepsScaledTrueBridge dom ρW lam z' b = F (q z') := by
      simpa only [F, q, μ, l, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using! he
    apply (eq_div_iff hb0).mpr
    simpa only [mul_comm] using he'
  convert! h.congr_of_eventuallyEq hev using 1
  field_simp
  ring

include hW hθ hD in
theorem cepsScaledTrueBridge_deriv_frequency {b lam : ℝ} (hb : 0 < b)
    (hμ : |b * lam| ≤ dom.μ₀) {z : ℂ}
    (hq : ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀)
    (hre : 0 ≤ (cepsComplexScaledDiscount lam z b).re)
    (hl : dom.normalWidthThreshold ≤ (1 + b * lam) / b) :
    deriv (fun z => cepsScaledTrueBridge dom ρW lam z b) z =
      (b : ℂ) * (1 + (b : ℂ) * lam) *
        deriv (fun q => (cepsWHNormalData D θ ρW ((b * lam : ℝ) : ℂ) q).regularBridge
          (dom.canonL ρW) ((b * lam : ℝ) : ℂ) q (((1 + b * lam) / b : ℝ) : ℂ))
            (cepsComplexScaledDiscount lam z b) :=
  (cepsScaledTrueBridge_hasDerivAt_frequency dom hW hθ hD hb hμ hq hre hl).deriv

end PGM
