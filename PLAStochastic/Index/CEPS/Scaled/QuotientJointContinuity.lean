import PLAStochastic.Index.CEPS.Scaled.QuotientBranchIdentification
import PLAStochastic.Index.CEPS.Normal.MovingSlopeContinuity
import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope

/-! # Joint continuity and holomorphic slices of the actual scaled quotient

The hypotheses describe a joint open chart for the two physical roots.
The following neighborhood module supplies that chart from the actual law.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotient_raw_analyticOnNhd (lam : ℝ) (U : Set (ℂ × ℂ)) :
    AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ =>
      -cepsD ρW (x.1.1 * lam) (cepsComplexScaledDiscount lam x.1.2 x.1.1) x.2)
      (U ×ˢ ball 0 dom.ρA) := by
  have hM : AnalyticOnNhd ℂ (stepTransform ρW) (ball 0 (θ / 2)) :=
    (differentiableOn_stepTransform_ball hW hθ hD.le).analyticOnNhd isOpen_ball
  have hM' : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => stepTransform ρW x.2)
      (U ×ˢ ball 0 dom.ρA) := hM.comp analyticOnNhd_snd (fun x hx => by
    apply mem_ball_zero_iff.mpr
    have hn := mem_ball_zero_iff.mp hx.2
    have := CepsC6.ρA_lt_cgfRadius dom hθ hD
    have := cepsCgfRadius_le (D := D) (θ := θ)
    linarith)
  have hb : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.1) (U ×ˢ ball 0 dom.ρA) :=
    analyticOnNhd_fst.comp analyticOnNhd_fst (fun _ _ => mem_univ _)
  have hz : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.2) (U ×ˢ ball 0 dom.ρA) :=
    analyticOnNhd_snd.comp analyticOnNhd_fst (fun _ _ => mem_univ _)
  have hq : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ =>
      cepsComplexScaledDiscount lam x.1.2 x.1.1) (U ×ˢ ball 0 dom.ρA) := by
    unfold cepsComplexScaledDiscount
    exact ((hb.pow 2).mul hz).mul
      ((analyticOnNhd_const (v := (1 : ℂ))).add (hb.mul (analyticOnNhd_const (v := (lam : ℂ)))))
  have hE : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => exp ((x.1.1 * lam) * x.2))
      (U ×ˢ ball 0 dom.ρA) :=
    ((hb.mul (analyticOnNhd_const (v := (lam : ℂ)))).mul analyticOnNhd_snd).cexp
  unfold cepsD
  exact ((analyticOnNhd_const (v := (1 : ℂ))).sub ((hq.neg.cexp.mul hE).mul hM')).neg

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsScaledQuotient_continuousOn_joint_on_root_chart
    (lam : ℝ) {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hp : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1) U)
    (hm : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1) U)
    (hpmap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      U (ball 0 dom.ρA))
    (hmmap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      U (ball 0 dom.ρA)) :
    ContinuousOn (fun x : (ℂ × ℂ) × ℂ => cepsScaledQuotient D θ ρW lam x.1.2 x.1.1 x.2)
      (U ×ˢ ball 0 dom.ρA) := by
  have hG := cepsScaledQuotient_raw_analyticOnNhd dom hW hθ hD lam U
  have hd : ∀ x ∈ U, DifferentiableOn ℂ
      (fun w => -cepsD ρW (x.1 * lam) (cepsComplexScaledDiscount lam x.2 x.1) w)
      (ball 0 dom.ρA) := fun x hx w hw =>
    (hG (x, w) ⟨hx, hw⟩).curry_right.differentiableAt.differentiableWithinAt
  exact cepsNormal_continuousOn_joint_moving_second_dslope_general
    (G := fun x w => -cepsD ρW (x.1 * lam) (cepsComplexScaledDiscount lam x.2 x.1) w)
    (a := fun x => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
    (b := fun x => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
    hU hG.continuousOn hd
    hp.continuousOn hm.continuousOn hpmap hmmap

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsScaledQuotient_holomorphic_slices_on_root_chart
    (lam : ℝ) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hp : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1) (U ×ˢ V))
    (hm : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1) (U ×ˢ V))
    (hpmap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      (U ×ˢ V) (ball 0 dom.ρA))
    (hmmap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (U ×ˢ V) (ball 0 dom.ρA)) :
    (∀ z ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledQuotient D θ ρW lam z x.1 x.2)
      (U ×ˢ ball 0 dom.ρA)) ∧
    (∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledQuotient D θ ρW lam x.1 b x.2)
      (V ×ˢ ball 0 dom.ρA)) := by
  have hG := (cepsScaledQuotient_raw_analyticOnNhd dom hW hθ hD lam (U ×ˢ V)).differentiableOn
  constructor
  · intro z hz
    have hraw : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        -cepsD ρW (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) x.2)
        (U ×ˢ ball 0 dom.ρA) := hG.comp
      (f := fun x : ℂ × ℂ => ((x.1, z), x.2)) (by fun_prop) (fun x hx => ⟨⟨hx.1, hz⟩, hx.2⟩)
    exact cepsNormal_joint_moving_second_dslope_of_differentiable
      (G := fun b w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w)
      (a := fun b => b * cepsScaledSignedRoot D θ ρW lam z 1 b)
      (b := fun b => b * cepsScaledSignedRoot D θ ρW lam z (-1) b) hU hraw
      (hp.comp (f := fun b : ℂ => (b, z)) (by fun_prop) (fun _ hb => ⟨hb, hz⟩))
      (hm.comp (f := fun b : ℂ => (b, z)) (by fun_prop) (fun _ hb => ⟨hb, hz⟩))
      (fun b hb => hpmap (show (b, z) ∈ U ×ˢ V from ⟨hb, hz⟩))
      (fun b hb => hmmap (show (b, z) ∈ U ×ˢ V from ⟨hb, hz⟩))
  · intro b hb
    have hraw : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam x.1 b) x.2)
        (V ×ˢ ball 0 dom.ρA) := hG.comp
      (f := fun x : ℂ × ℂ => ((b, x.1), x.2)) (by fun_prop) (fun x hx => ⟨⟨hb, hx.1⟩, hx.2⟩)
    exact cepsNormal_joint_moving_second_dslope_of_differentiable
      (G := fun z w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w)
      (a := fun z => b * cepsScaledSignedRoot D θ ρW lam z 1 b)
      (b := fun z => b * cepsScaledSignedRoot D θ ρW lam z (-1) b) hV hraw
      (hp.comp (f := fun z : ℂ => (b, z)) (by fun_prop) (fun _ hz => ⟨hb, hz⟩))
      (hm.comp (f := fun z : ℂ => (b, z)) (by fun_prop) (fun _ hz => ⟨hb, hz⟩))
      (fun z hz => hpmap (show (b, z) ∈ U ×ˢ V from ⟨hb, hz⟩))
      (fun z hz => hmmap (show (b, z) ∈ U ×ˢ V from ⟨hb, hz⟩))

end PGM
