import PLAStochastic.Index.CEPS.Scaled.MorseChartIdentification
import PLAStochastic.Index.CEPS.Scaled.SurrogateOrigin
import PLAStochastic.Index.CEPS.Canonical.JointDifferential
import PLAStochastic.Index.CEPS.Normal.ActualQuotientDisc

/-! # The actual zero-drift spatial family before square-root descent

The signed coordinate is free: the discount is `(b*r)^2`. At zero drift
every canonical Taylor surrogate equals this actual family.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledZeroDriftLiftG {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b r ξ : ℂ) : ℂ :=
  exp (-ξ) * cepsQ D θ ρW 0 ((b * r) ^ 2) (b * ξ) *
    exp (-2 * dom.canonL ρW 0 ((b * r) ^ 2) (b * ξ))

def CepsCanonDomain.zeroDriftLiftScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (R S : ℝ) : ℝ :=
  min (dom.scaledMorseJointRadius 0 R)
    (min (dom.rmax / (2 * (1 + R))) (dom.c₀ / (2 * (1 + S))))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem zeroDriftLiftScaleRadius_pos {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    0 < dom.zeroDriftLiftScaleRadius R S := by
  have := dom.rmax_pos
  have := dom.c₀_pos
  unfold CepsCanonDomain.zeroDriftLiftScaleRadius
  exact lt_min (scaledMorseJointRadius_pos dom 0 hR)
    (lt_min (by positivity) (by positivity))

theorem cepsScaledZeroDriftLiftG_eq_surrogate (N : ℕ) (b r : ℂ) :
    cepsScaledZeroDriftLiftG dom ρW b r = cepsScaledSurrogateG dom ρW N 0 (r ^ 2) b := by
  funext ξ
  unfold cepsScaledZeroDriftLiftG cepsScaledSurrogateG cepsCanonSurrogateWeight
  simp only [ofReal_zero, mul_zero, add_zero, mul_one, cepsCanonDriftTaylor_zero,
    cepsComplexScaledDiscount]
  rw [show (b * r) ^ 2 = b ^ 2 * r ^ 2 by ring]
  exact mul_assoc _ _ _

include hW hθ hD in
theorem cepsScaledZeroDriftLiftG_differentiableOn {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => cepsScaledZeroDriftLiftG dom ρW x.1.1 x.1.2 x.2)
      ((ball 0 (dom.zeroDriftLiftScaleRadius R S) ×ˢ ball 0 R) ×ˢ ball 0 S) := by
  let U := (ball (0 : ℂ) (dom.zeroDriftLiftScaleRadius R S) ×ˢ ball (0 : ℂ) R) ×ˢ ball (0 : ℂ) S
  have hcoords : ∀ x ∈ U, ‖(x.1.1 * x.1.2) ^ 2‖ < dom.q₀ ∧ ‖x.1.1 * x.2‖ < dom.c₀ / 2 := by
    intro x hx
    have hb := mem_ball_zero_iff.mp hx.1.1
    have hr := mem_ball_zero_iff.mp hx.1.2
    have hξ := mem_ball_zero_iff.mp hx.2
    have hbR := hb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hbS := hb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hbr : ‖x.1.1‖ * ‖x.1.2‖ < dom.rmax / 2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + R))).mp hbR
      nlinarith [norm_nonneg x.1.1]
    have hbξ : ‖x.1.1‖ * ‖x.2‖ < dom.c₀ / 2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + S))).mp hbS
      nlinarith [norm_nonneg x.1.1]
    rw [norm_pow, norm_mul, norm_mul]
    refine ⟨?_, hbξ⟩
    rw [dom.q₀_def]
    nlinarith [mul_nonneg (norm_nonneg x.1.1) (norm_nonneg x.1.2), dom.rmax_pos]
  have hp : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => ((x.1.1 * x.1.2) ^ 2, x.1.1 * x.2)) U := by
    fun_prop
  have hQ := (cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD
    (show ‖(0 : ℂ)‖ ≤ dom.μ₀ by simpa using dom.μ₀_pos.le)).comp hp (by
      intro x hx
      obtain ⟨hq, hξ⟩ := hcoords x hx
      refine ⟨?_, mem_ball_zero_iff.mpr ?_⟩
      change ‖(x.1.1 * x.1.2) ^ 2 - cepsMorseMin D θ ρW 0‖ < dom.rmax ^ 2
      rw [(cepsMorseMin_zero_jets hW hθ hD).1, sub_zero]
      exact hq.trans_le (by rw [dom.q₀_def]; nlinarith [sq_nonneg dom.rmax])
      have := dom.c₀_le
      have := dom.ρA_pos
      linarith)
  have hL : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ =>
      dom.canonL ρW 0 ((x.1.1 * x.1.2) ^ 2) (x.1.1 * x.2)) U := by
    intro x hx
    obtain ⟨hq, hξ⟩ := hcoords x hx
    exact ((dom.differentiableAt_canonL_qz hW hθ hD
      (show |(0 : ℝ)| ≤ dom.μ₀ by simpa using dom.μ₀_pos.le) hq
      ((re_le_norm _).trans_lt (hξ.trans (half_lt_self dom.c₀_pos)))).comp x
        ((hp x hx).differentiableAt (((isOpen_ball.prod isOpen_ball).prod isOpen_ball).mem_nhds hx))).differentiableWithinAt
  have hE : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => exp (-x.2)) U := by fun_prop
  exact (hE.mul hQ).mul ((hL.const_mul (-2)).cexp)

end PGM
