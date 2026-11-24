import PLAStochastic.Index.CEPS.Scaled.TrueHalfPhysicalDisc

/-! # Fixed physical discount differentiation of the actual half-line bridge -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_deriv_frequency (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    deriv (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) z =
      (b : ℂ) * (1 + (b : ℂ) * lam) *
        deriv (fun q => (cepsWHNormalData D θ ρW ((b : ℂ) * lam) q).halfBridge
          (dom.canonL ρW) ((b : ℂ) * lam) q ((1 + (b : ℂ) * lam) / b))
            (cepsComplexScaledDiscount lam z b) := by
  let w : ℂ := 1 + (b : ℂ) * lam
  let k : ℂ := (b : ℂ) ^ 2 * w
  let q := cepsComplexScaledDiscount lam z b
  let U : ℂ → ℂ := fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b
  let F : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW ((b : ℂ) * lam) q).halfBridge
    (dom.canonL ρW) ((b : ℂ) * lam) q (w / b)
  obtain ⟨hμ, hq, _, _, hwlo, _, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hw0 : w ≠ 0 := by
    have hwr : w.re = 1 + b * lam := by simp [w, mul_re]
    intro he
    rw [he, zero_re] at hwr
    linarith [hwlo]
  have hk0 : k ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0) hw0
  have hq0 : ‖q‖ < dom.q₀ := hq.trans_lt (by linarith [dom.q₀_pos])
  have hqeq : q = k * z := by dsimp [q, k, w, cepsComplexScaledDiscount]; ring
  have heval : q / k = z := by rw [hqeq]; exact mul_div_cancel_left₀ z hk0
  have hU : DifferentiableAt ℂ U z :=
    ((cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M lam hlam hz hb hbs)
      z (mem_ball_self (positiveFrequencyRadius_pos dom hW hθ hD))).differentiableAt
      (ball_mem_nhds z (positiveFrequencyRadius_pos dom hW hθ hD))
  have hUZ : HasDerivAt U (deriv U z) (q / k) := by rw [heval]; exact hU.hasDerivAt
  have h := (hUZ.comp q ((hasDerivAt_id' q).div_const k)).const_mul (b : ℂ)
  have he : F =ᶠ[𝓝 q] fun q' => (b : ℂ) * U (q' / k) := by
    have hset : ∀ᶠ q' in 𝓝 q, q' ∈ ball (0 : ℂ) dom.q₀ :=
      isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq0)
    filter_upwards [hset] with q' hq'
    have heq : cepsComplexScaledDiscount lam (q' / k) b = q' := by
      unfold cepsComplexScaledDiscount
      change (b : ℂ) ^ 2 * (q' / k) * w = q'
      have hk : k = (b : ℂ) ^ 2 * w := rfl
      rw [show (b : ℂ) ^ 2 * (q' / k) * w = k * (q' / k) by rw [hk]; ring]
      exact mul_div_cancel₀ _ hk0
    have hp := cepsScaledTrueHalfBridge_eq_actual_on_discount_disc dom hW hθ hD hb hμ
      (show ‖cepsComplexScaledDiscount lam (q' / k) b‖ ≤ dom.q₀ by rw [heq]; exact (mem_ball_zero_iff.mp hq').le)
    simpa only [F, U, w, heq] using hp.symm
  have hd := (h.congr_of_eventuallyEq he).deriv
  change deriv U z = (b : ℂ) * w * deriv F q
  rw [hd]
  dsimp [k]
  field_simp

end PGM
