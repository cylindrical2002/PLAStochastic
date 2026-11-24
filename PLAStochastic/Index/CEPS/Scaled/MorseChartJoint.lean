import PLAStochastic.Index.CEPS.Scaled.MorseChart
import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope

/-! # Joint scale and signed-coordinate holomorphy of the removable Morse chart -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.scaledMorseJointRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (lam : ℂ) (R : ℝ) : ℝ :=
  min dom.μ₀ dom.rmax / (1 + ‖lam‖ + R)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem scaledMorseJointRadius_pos (lam : ℂ) {R : ℝ} (hR : 0 < R) :
    0 < dom.scaledMorseJointRadius lam R := by
  unfold CepsCanonDomain.scaledMorseJointRadius
  exact div_pos (lt_min dom.μ₀_pos dom.rmax_pos) (by positivity)

include hW hθ hD in
theorem cepsScaledMorseChart_differentiableOn_joint (lam : ℂ) {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam x.2 x.1)
      (ball 0 (dom.scaledMorseJointRadius lam R) ×ˢ ball 0 R) := by
  let B := dom.scaledMorseJointRadius lam R
  let G : ℂ → ℂ → ℂ := fun r b => cepsMorseRoot D θ ρW (b * lam) (b * r)
  have hB := scaledMorseJointRadius_pos dom lam hR
  have hcoords : ∀ x ∈ ball (0 : ℂ) R ×ˢ ball 0 B,
      ‖x.2 * lam‖ < dom.μ₀ ∧ ‖x.2 * x.1‖ < dom.rmax := by
    intro x hx
    have hr := mem_ball_zero_iff.mp hx.1
    have hb := (lt_div_iff₀ (by positivity : 0 < 1 + ‖lam‖ + R)).mp (mem_ball_zero_iff.mp hx.2)
    have hm : ‖x.2‖ * ‖lam‖ < min dom.μ₀ dom.rmax := by
      exact (mul_le_mul_of_nonneg_left (by linarith : ‖lam‖ ≤ 1 + ‖lam‖ + R) (norm_nonneg _)).trans_lt hb
    have hn : ‖x.2‖ * ‖x.1‖ < min dom.μ₀ dom.rmax := by
      exact (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg lam] : ‖x.1‖ ≤ 1 + ‖lam‖ + R) (norm_nonneg _)).trans_lt hb
    rw [norm_mul, norm_mul]
    exact ⟨hm.trans_le (min_le_left _ _), hn.trans_le (min_le_right _ _)⟩
  have hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 R ×ˢ ball 0 B) := by
    apply (differentiableOn_cepsMorseRoot hW hθ hD).comp
      ((differentiableOn_snd.mul_const lam).prodMk (differentiableOn_snd.mul differentiableOn_fst))
    intro x hx
    obtain ⟨hm, hn⟩ := hcoords x hx
    exact ⟨mem_ball_zero_iff.mpr (dom.μ_lt_chart hm.le), mem_ball_zero_iff.mpr
      (hn.trans_le (by have := dom.rmax_r1; have := dom.rmax_pos; linarith))⟩
  have hS := cepsNormal_joint_moving_dslope_of_differentiable isOpen_ball hG
    (differentiableOn_const (0 : ℂ)) (fun _ _ => mem_ball_self hB)
  exact hS.comp (differentiableOn_snd.prodMk differentiableOn_fst) (fun _ hx => ⟨hx.2, hx.1⟩)

end PGM
