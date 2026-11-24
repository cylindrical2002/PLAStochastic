import PLAStochastic.Index.CEPS.Scaled.ZeroDriftLiftSlopes

/-! # The actual marked second spatial slope before zero-drift descent -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem cepsScaledZeroDriftLift_marker_mem {R : ℝ} (hR : 0 < R) {b r : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R)) (hr : r ∈ ball (0 : ℂ) R) :
    b * r ^ 2 ∈ ball (0 : ℂ) (dom.zeroDriftLiftSpatialRadius R) := by
  have hK := cepsChartK_pos hD
  have hnr := mem_ball_zero_iff.mp hr
  have hbb := (mem_ball_zero_iff.mp hb).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hprod := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + R))).mp hbb
  have hbr : ‖b‖ * R < dom.rmax / 2 := by nlinarith [norm_nonneg b]
  rw [mem_ball_zero_iff, norm_mul, norm_pow]
  calc
    _ ≤ ‖b‖ * R ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hnr.le 2) (norm_nonneg b)
    _ < dom.rmax / 2 * R := by nlinarith
    _ < dom.zeroDriftLiftSpatialRadius R := by
      unfold CepsCanonDomain.zeroDriftLiftSpatialRadius
      nlinarith [mul_pos dom.rmax_pos hR, mul_pos hK hR]

include hW hθ hD in
theorem cepsScaledZeroDriftLiftNumerator_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftNumerator dom ρW x.1 x.2)
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
  exact cepsNormal_differentiableOn_two_parameter_moving_second_dslope
    (G := fun x ξ => cepsScaledZeroDriftLiftG dom ρW x.1 x.2 ξ)
    (a := fun x => cepsScaledMorseChart D θ ρW 0 (-x.2) x.1)
    (b := fun x => cepsScaledMorseChart D θ ρW 0 x.2 x.1) (c := fun x => x.1 * x.2 ^ 2)
    isOpen_ball isOpen_ball hG.continuousOn hG₁ hG₂ ha hp (by fun_prop)
    (fun x hx => mem_ball_zero_iff.mpr (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hx.1
      (mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2))))
    (fun x hx => mem_ball_zero_iff.mpr (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hx.1 hx.2))
    (fun x hx => cepsScaledZeroDriftLift_marker_mem dom hD hR hx.1 hx.2)

include hW hθ hD in
theorem cepsScaledZeroDriftLiftNumerator_even {R : ℝ} (hR : 0 < R) {b r : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.zeroDriftKernelScaleRadius R)) (hr : r ∈ ball (0 : ℂ) R) :
    cepsScaledZeroDriftLiftNumerator dom ρW b (-r) = cepsScaledZeroDriftLiftNumerator dom ρW b r := by
  let S := dom.zeroDriftLiftSpatialRadius R
  have hG := cepsScaledZeroDriftLiftG_differentiableOn dom hW hθ hD hR
    (zeroDriftLiftSpatialRadius_pos dom hD hR)
  have hd : DifferentiableOn ℂ (cepsScaledZeroDriftLiftG dom ρW b r) (ball 0 S) :=
    hG.comp (f := fun ξ : ℂ => ((b, r), ξ)) (by fun_prop) (fun ξ hξ => ⟨⟨hb, hr⟩, hξ⟩)
  have hp : cepsScaledMorseChart D θ ρW 0 r b ∈ ball (0 : ℂ) S :=
    mem_ball_zero_iff.mpr (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hb hr)
  have ha : cepsScaledMorseChart D θ ρW 0 (-r) b ∈ ball (0 : ℂ) S :=
    mem_ball_zero_iff.mpr (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hb
      (mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr)))
  unfold cepsScaledZeroDriftLiftNumerator
  rw [cepsScaledZeroDriftLiftG_even, neg_neg, neg_sq]
  exact cepsNormal_second_dslope_swap ((hd _ ha).differentiableAt (isOpen_ball.mem_nhds ha))
    ((hd _ hp).differentiableAt (isOpen_ball.mem_nhds hp)) _

end PGM
