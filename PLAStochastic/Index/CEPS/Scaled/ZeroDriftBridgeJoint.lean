import PLAStochastic.Index.CEPS.Scaled.ZeroDriftLiftSlopes
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridge
import PLAStochastic.Index.CEPS.Normal.LocalEvenQuotient
import PLAStochastic.Index.CEPS.Normal.JointSpatialDerivative

/-! # Actual zero-drift bridge joint holomorphy through the origin

Every surrogate has the same actual zero-drift spatial family. The signed
coordinate lift is even; local nonzero denominators and square-root descent
pay the joint origin and the actual frequency derivative there.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledZeroDriftLiftBridgeNumerator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b r : ℂ) : ℂ :=
  -cepsScaledZeroDriftLiftG dom ρW b r (cepsScaledMorseChart D θ ρW 0 r b) *
    cepsScaledZeroDriftLiftG dom ρW b r (cepsScaledMorseChart D θ ρW 0 (-r) b)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem cepsScaledZeroDriftLiftDenominator_sqrt_eq_surrogate (N : ℕ) (b z : ℂ) :
    cepsScaledZeroDriftLiftDenominator dom ρW b (sqrt z) =
      cepsScaledSurrogateDenominator dom ρW N 0 z b := by
  unfold cepsScaledZeroDriftLiftDenominator cepsScaledSurrogateDenominator
  rw [cepsScaledZeroDriftLiftG_eq_surrogate dom (ρW := ρW) N, sqrt_sq_eq]
  simp only [cepsScaledSignedRoot_zeroDrift_eq_chart, neg_one_mul, one_mul]

theorem cepsScaledZeroDriftLiftBridge_sqrt_eq_surrogate (N : ℕ) (b z : ℂ) :
    cepsScaledZeroDriftLiftBridgeNumerator dom ρW b (sqrt z) /
      cepsScaledZeroDriftLiftDenominator dom ρW b (sqrt z) =
        cepsScaledSurrogateBridge dom ρW N 0 z b := by
  unfold cepsScaledZeroDriftLiftBridgeNumerator cepsScaledSurrogateBridge
  rw [cepsScaledZeroDriftLiftG_eq_surrogate dom (ρW := ρW) N, sqrt_sq_eq,
    cepsScaledZeroDriftLiftDenominator_sqrt_eq_surrogate dom (ρW := ρW) N]
  simp only [cepsScaledSignedRoot_zeroDrift_eq_chart, neg_one_mul, one_mul]

include hW hθ hD in
theorem cepsScaledZeroDriftLiftBridgeNumerator_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledZeroDriftLiftBridgeNumerator dom ρW x.1 x.2)
      (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) := by
  have hG := cepsScaledZeroDriftLiftG_differentiableOn dom hW hθ hD hR
    (zeroDriftLiftSpatialRadius_pos dom hD hR)
  obtain ⟨hp, ha⟩ := cepsScaledZeroDriftLift_roots_differentiableOn dom hW hθ hD hR
  have hGp : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsScaledZeroDriftLiftG dom ρW x.1 x.2 (cepsScaledMorseChart D θ ρW 0 x.2 x.1))
        (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) :=
    hG.comp (f := fun x : ℂ × ℂ => (x, cepsScaledMorseChart D θ ρW 0 x.2 x.1))
      (differentiableOn_id.prodMk hp) (fun x hx => ⟨hx, mem_ball_zero_iff.mpr
        (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hx.1 hx.2)⟩)
  have hGa : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsScaledZeroDriftLiftG dom ρW x.1 x.2 (cepsScaledMorseChart D θ ρW 0 (-x.2) x.1))
        (ball 0 (dom.zeroDriftKernelScaleRadius R) ×ˢ ball 0 R) :=
    hG.comp (f := fun x : ℂ × ℂ => (x, cepsScaledMorseChart D θ ρW 0 (-x.2) x.1))
      (differentiableOn_id.prodMk ha) (fun x hx => ⟨hx, mem_ball_zero_iff.mpr
        (cepsScaledZeroDriftLift_chart_budget dom hW hθ hD hR hx.1
          (mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2)))⟩)
  exact hGp.neg.mul hGa

theorem cepsScaledZeroDriftLiftBridgeNumerator_even (b r : ℂ) :
    cepsScaledZeroDriftLiftBridgeNumerator dom ρW b (-r) =
      cepsScaledZeroDriftLiftBridgeNumerator dom ρW b r := by
  unfold cepsScaledZeroDriftLiftBridgeNumerator
  rw [cepsScaledZeroDriftLiftG_even, neg_neg]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateBridge_zeroDrift_holomorphic_near_joint_origin
    {m : ℕ} {η M : ℝ} (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 1 ≤ m) (N : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.zeroDriftKernelScaleRadius 1)
      (dom.surrogateRegularScaleRadius 0 M 0 0))) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateBridge dom ρW N 0 x.2 x.1)
        (ball b ε ×ˢ ball 0 (ε ^ 2)) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => deriv (fun z => cepsScaledSurrogateBridge dom ρW N 0 z x.1) x.2)
        (ball b ε ×ˢ ball 0 (ε ^ 2)) := by
  have hbL := ball_subset_ball (min_le_left _ _) hb
  have hbS := ball_subset_ball (min_le_right _ _) hb
  have hD0 : cepsScaledZeroDriftLiftDenominator dom ρW b 0 ≠ 0 := by
    have he := cepsScaledZeroDriftLiftDenominator_sqrt_eq_surrogate dom (ρW := ρW) 0 b 0
    rw [sqrt_zero] at he
    rw [he]
    exact cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM 0 (by simpa using hm)
      0 (by simp) hbS
  obtain ⟨ε, hε, hq⟩ := cepsNormal_joint_even_quotient_near_origin
    (F := cepsScaledZeroDriftLiftBridgeNumerator dom ρW)
    (S := cepsScaledZeroDriftLiftDenominator dom ρW) isOpen_ball (by norm_num : (0 : ℝ) < 1)
    (cepsScaledZeroDriftLiftBridgeNumerator_differentiableOn dom hW hθ hD (by norm_num))
    (cepsScaledZeroDriftLiftDenominator_differentiableOn dom hW hθ hD (by norm_num))
    (fun b _ r _ => cepsScaledZeroDriftLiftBridgeNumerator_even dom b r)
    (fun b _ r _ => cepsScaledZeroDriftLiftDenominator_even dom b r) hbL hD0
  have hB : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateBridge dom ρW N 0 x.2 x.1)
      (ball b ε ×ˢ ball 0 (ε ^ 2)) := by
    apply hq.congr
    intro x _
    exact (cepsScaledZeroDriftLiftBridge_sqrt_eq_surrogate dom (ρW := ρW) N x.1 x.2).symm
  exact ⟨ε, hε, hB, cepsNormal_differentiableOn_spatial_deriv
    (G := fun b z => cepsScaledSurrogateBridge dom ρW N 0 z b) isOpen_ball hB⟩

end PGM
