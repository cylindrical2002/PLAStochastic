import PLAStochastic.Index.CEPS.Scaled.ZeroDriftLift
import PLAStochastic.Index.CEPS.Normal.TwoParameterSlopes
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry

/-! # Actual zero-drift first and second slopes in scale and signed coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.zeroDriftLiftSpatialRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (R : ℝ) : ℝ :=
  1 + (cepsChartK D + dom.rmax) * R

def CepsCanonDomain.zeroDriftKernelScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (R : ℝ) : ℝ :=
  dom.zeroDriftLiftScaleRadius R (dom.zeroDriftLiftSpatialRadius R)

def cepsScaledZeroDriftLiftDenominator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b r : ℂ) : ℂ :=
  dslope (cepsScaledZeroDriftLiftG dom ρW b r)
    (cepsScaledMorseChart D θ ρW 0 (-r) b) (cepsScaledMorseChart D θ ρW 0 r b)

def cepsScaledZeroDriftLiftNumerator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b r : ℂ) : ℂ :=
  dslope (dslope (cepsScaledZeroDriftLiftG dom ρW b r)
    (cepsScaledMorseChart D θ ρW 0 (-r) b)) (cepsScaledMorseChart D θ ρW 0 r b) (b * r ^ 2)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem zeroDriftLiftSpatialRadius_pos {R : ℝ} (hR : 0 < R) :
    0 < dom.zeroDriftLiftSpatialRadius R := by
  have := cepsChartK_pos hD
  have := dom.rmax_pos
  unfold CepsCanonDomain.zeroDriftLiftSpatialRadius
  positivity

include hD in
theorem zeroDriftKernelScaleRadius_pos {R : ℝ} (hR : 0 < R) :
    0 < dom.zeroDriftKernelScaleRadius R :=
  zeroDriftLiftScaleRadius_pos dom hR (zeroDriftLiftSpatialRadius_pos dom hD hR)

include hW hθ hD in
theorem cepsScaledZeroDriftLift_chart_budget {R : ℝ} (hR : 0 < R) {b r : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R)) (hr : r ∈ ball (0 : ℂ) R) :
    ‖cepsScaledMorseChart D θ ρW 0 r b‖ < dom.zeroDriftLiftSpatialRadius R := by
  have hK := cepsChartK_pos hD
  have hn := mem_ball_zero_iff.mp hr
  have hbb := (mem_ball_zero_iff.mp hb).trans_le (min_le_left _ _)
  simp only [CepsCanonDomain.scaledMorseJointRadius, norm_zero, add_zero] at hbb
  have hsmall : ‖b‖ * (1 + R) < min dom.μ₀ dom.rmax := by
    exact (lt_div_iff₀ (by positivity : 0 < 1 + R)).mp hbb
  have hbf : b ∈ ball (0 : ℂ) (dom.scaledMorseRadius 0 r) := by
    rw [mem_ball_zero_iff, CepsCanonDomain.scaledMorseRadius, norm_zero, add_zero]
    apply (lt_div_iff₀ (by positivity : 0 < 1 + ‖r‖)).mpr
    nlinarith [norm_nonneg b]
  have h := (cepsScaledMorseChart_budget dom hW hθ hD 0 r).2 b hbf
  simp only [CepsCanonDomain.scaledMorseBound, norm_zero, mul_zero, zero_add] at h
  apply h.trans_lt
  unfold CepsCanonDomain.zeroDriftLiftSpatialRadius
  nlinarith [mul_pos dom.rmax_pos hR]

include hW hθ hD in
theorem cepsScaledZeroDriftLift_roots_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW 0 x.2 x.1)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) ∧
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW 0 (-x.2) x.1)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) := by
  have hp : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW 0 x.2 x.1)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) :=
    (cepsScaledMorseChart_differentiableOn_joint dom hW hθ hD 0 hR).mono
    (fun x hx => ⟨ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩)
  exact ⟨hp, hp.comp (differentiableOn_fst.prodMk differentiableOn_snd.neg)
    (fun x hx => ⟨hx.1, mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2)⟩)⟩

include hW hθ hD in
theorem cepsScaledZeroDriftLiftDenominator_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftDenominator dom ρW x.1 x.2)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) := by
  let U := ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R)
  let V := ball (0 : ℂ) R
  let S := dom.zeroDriftLiftSpatialRadius R
  have hG := cepsScaledZeroDriftLiftG_differentiableOn dom hW hθ hD hR
    (zeroDriftLiftSpatialRadius_pos dom hD hR)
  have hG₁ : ∀ r ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftG dom ρW x.1 r x.2)
      (U ×ˢ ball 0 S) := fun r hr => hG.comp
    (f := fun x : ℂ × ℂ => ((x.1, r), x.2))
    (by fun_prop) (fun x hx => ⟨⟨hx.1, hr⟩, hx.2⟩)
  have hG₂ : ∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftG dom ρW b x.1 x.2)
      (V ×ˢ ball 0 S) := fun b hb => hG.comp
    (f := fun x : ℂ × ℂ => ((b, x.1), x.2))
    (by fun_prop) (fun x hx => ⟨⟨hb, hx.1⟩, hx.2⟩)
  obtain ⟨hp, ha⟩ := cepsScaledZeroDriftLift_roots_differentiableOn dom hW hθ hD hR
  exact cepsNormal_differentiableOn_two_parameter_moving_dslope
    (G := fun x ξ => cepsScaledZeroDriftLiftG dom ρW x.1 x.2 ξ) isOpen_ball isOpen_ball
    hG.continuousOn hG₁ hG₂ ha hp
    (fun x hx => mem_ball_zero_iff.mpr (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hx.1
      (mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2))))
    (fun x hx => mem_ball_zero_iff.mpr (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hx.1 hx.2))

theorem cepsScaledZeroDriftLiftG_even (b r : ℂ) :
    cepsScaledZeroDriftLiftG dom ρW b (-r) = cepsScaledZeroDriftLiftG dom ρW b r := by
  funext ξ
  unfold cepsScaledZeroDriftLiftG
  rw [mul_neg, neg_sq]

theorem cepsScaledZeroDriftLiftDenominator_even (b r : ℂ) :
    cepsScaledZeroDriftLiftDenominator dom ρW b (-r) = cepsScaledZeroDriftLiftDenominator dom ρW b r := by
  unfold cepsScaledZeroDriftLiftDenominator
  rw [cepsScaledZeroDriftLiftG_even, neg_neg]
  exact cepsNormal_dslope_swap _ _ _

end PGM
