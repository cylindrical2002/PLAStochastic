import PLAStochastic.Index.CEPS.Scaled.RootCurvePair
import PLAStochastic.Index.CEPS.Normal.ActualPiBounds

/-! # Actual quadratic quotients along the complex-scale roots -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledQuotient (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z b ζ : ℂ) : ℂ :=
  dslope (dslope (fun w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w)
    (b * cepsScaledSignedRoot D θ ρW lam z 1 b))
    (b * cepsScaledSignedRoot D θ ρW lam z (-1) b) ζ

def cepsScaledQuotientAtRoot (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z sign b : ℂ) : ℂ :=
  cepsScaledQuotient D θ ρW lam z b (b * cepsScaledSignedRoot D θ ρW lam z sign b)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotient_eq_actual (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) (ζ : ℂ) :
    cepsScaledQuotient D θ ρW lam z b ζ =
      cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) ζ := by
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb
  have hm : ‖b * (lam : ℂ)‖ ≤ dom.μ₀ := hμ.le.trans (by linarith [dom.μ₀_pos])
  have hq' : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ := hq.le.trans (half_le_self dom.q₀_pos.le)
  rcases cepsScaledRootCurve_pair dom hW hθ hD lam hz hb with hp | hp
  · have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    dsimp only at h1 h2
    rw [cepsScaledQuotient, h1, h2]
    rfl
  · have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    dsimp only at h1 h2
    have hM := (differentiableOn_stepTransform_ball hW hθ hD.le).mono
      (ball_subset_ball (show dom.ρA ≤ θ / 2 by
        have := CepsC6.ρA_lt_cgfRadius dom hθ hD
        have := cepsCgfRadius_le (D := D) (θ := θ); linarith))
    have hG : DifferentiableOn ℂ
        (fun w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w) (ball 0 dom.ρA) := by
      unfold cepsD
      fun_prop
    have hpr := CepsC6.ball_c₀_subset dom (CepsC6.rootPlus_mem_ball dom hW hθ hD hm hq')
    have hmr := CepsC6.ball_c₀_subset dom (CepsC6.rootMinus_mem_ball dom hW hθ hD hm hq')
    rw [cepsScaledQuotient, h1, h2]
    exact cepsNormal_second_dslope_swap
      ((hG _ hpr).differentiableAt (isOpen_ball.mem_nhds hpr))
      ((hG _ hmr).differentiableAt (isOpen_ball.mem_nhds hmr)) ζ

include hW hθ hD in
theorem cepsScaledQuotient_differentiableOn (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledQuotient D θ ρW lam z x.1 x.2)
      (ball 0 (dom.canonScaleRadius lam z) ×ˢ ball 0 dom.ρA) := by
  let U : Set ℂ := ball 0 (dom.canonScaleRadius lam z)
  have hM : AnalyticOnNhd ℂ (stepTransform ρW) (ball 0 (θ / 2)) :=
    (differentiableOn_stepTransform_ball hW hθ hD.le).analyticOnNhd isOpen_ball
  have hM' : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => stepTransform ρW x.2)
      (U ×ˢ ball 0 dom.ρA) := hM.comp analyticOnNhd_snd (fun x hx => by
    apply mem_ball_zero_iff.mpr
    have hn := mem_ball_zero_iff.mp hx.2
    have := CepsC6.ρA_lt_cgfRadius dom hθ hD
    have := cepsCgfRadius_le (D := D) (θ := θ)
    linarith)
  have hq : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => cepsComplexScaledDiscount lam z x.1)
      (U ×ˢ ball 0 dom.ρA) := by
    unfold cepsComplexScaledDiscount
    exact ((analyticOnNhd_fst.pow 2).mul (analyticOnNhd_const (v := z))).mul
      ((analyticOnNhd_const (v := (1 : ℂ))).add
        (analyticOnNhd_fst.mul (analyticOnNhd_const (v := (lam : ℂ)))))
  have hE : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => exp ((x.1 * lam) * x.2))
      (U ×ˢ ball 0 dom.ρA) := ((analyticOnNhd_fst.mul (analyticOnNhd_const (v := (lam : ℂ)))).mul analyticOnNhd_snd).cexp
  have hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ =>
      -cepsD ρW (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) x.2)
      (U ×ˢ ball 0 dom.ρA) := by
    unfold cepsD
    exact ((analyticOnNhd_const (v := (1 : ℂ))).sub ((hq.neg.cexp.mul hE).mul hM')).neg
  have hp : DifferentiableOn ℂ (fun b => b * cepsScaledSignedRoot D θ ρW lam z 1 b) U :=
    differentiableOn_id.mul ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1.mono
      (ball_subset_ball (min_le_left _ _)))
  have hm : DifferentiableOn ℂ (fun b => b * cepsScaledSignedRoot D θ ρW lam z (-1) b) U :=
    differentiableOn_id.mul ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1.mono
      (ball_subset_ball (min_le_left _ _)))
  have hmap : ∀ sign : ℂ, ‖sign‖ ≤ 1 → MapsTo
      (fun b => b * cepsScaledSignedRoot D θ ρW lam z sign b) U (ball 0 dom.ρA) := by
    intro sign hsign b hb
    have hn := (canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb).2.2
    apply mem_ball_zero_iff.mpr
    have := dom.c₀_le; have := dom.ρA_pos
    linarith
  simpa only [cepsScaledQuotient] using!
    cepsNormal_differentiableOn_joint_moving_second_dslope
      (G := fun b w => -cepsD ρW (b * lam) (cepsComplexScaledDiscount lam z b) w)
      isOpen_ball hG hp hm (hmap 1 (by norm_num)) (hmap (-1) (by norm_num))

include hW hθ hD in
theorem cepsScaledQuotientAtRoot_budget (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    DifferentiableOn ℂ (cepsScaledQuotientAtRoot D θ ρW lam z sign)
      (ball 0 (dom.canonScaleRadius lam z)) ∧
    (∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      ‖cepsScaledQuotientAtRoot D θ ρW lam z sign b‖ ≤ v) ∧
    DifferentiableOn ℂ (fun b => (cepsScaledQuotientAtRoot D θ ρW lam z sign b)⁻¹)
      (ball 0 (dom.canonScaleRadius lam z)) ∧
    (∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      cepsVarLo D / 4 ≤ ‖cepsScaledQuotientAtRoot D θ ρW lam z sign b‖ ∧
      ‖(cepsScaledQuotientAtRoot D θ ρW lam z sign b)⁻¹‖ ≤ 4 / cepsVarLo D) := by
  have hs : DifferentiableOn ℂ (cepsScaledSignedRoot D θ ρW lam z sign)
      (ball 0 (dom.canonScaleRadius lam z)) :=
    (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).1.mono (ball_subset_ball (min_le_left _ _))
  have hmap : MapsTo (fun b => (b, b * cepsScaledSignedRoot D θ ρW lam z sign b))
      (ball 0 (dom.canonScaleRadius lam z))
      (ball 0 (dom.canonScaleRadius lam z) ×ˢ ball 0 dom.ρA) := by
    intro b hb
    refine ⟨hb, mem_ball_zero_iff.mpr ?_⟩
    have hn := (canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb).2.2
    have := dom.c₀_le; have := dom.ρA_pos
    linarith
  have hd : DifferentiableOn ℂ (cepsScaledQuotientAtRoot D θ ρW lam z sign)
      (ball 0 (dom.canonScaleRadius lam z)) := by
    simpa only [cepsScaledQuotientAtRoot, Function.comp_apply] using!
      (cepsScaledQuotient_differentiableOn dom hW hθ hD lam hz).comp
        (differentiableOn_id.prodMk (differentiableOn_id.mul hs)) hmap
  have hbounds : ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      cepsVarLo D / 4 ≤ ‖cepsScaledQuotientAtRoot D θ ρW lam z sign b‖ ∧
      ‖cepsScaledQuotientAtRoot D θ ρW lam z sign b‖ ≤ v := by
    intro b hb
    obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
    have hm : ‖b * (lam : ℂ)‖ ≤ dom.μ₀ := hμ.le.trans (by linarith [dom.μ₀_pos])
    have hq' : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ := hq.le.trans (half_le_self dom.q₀_pos.le)
    have hζ := mem_ball_zero_iff.mp (hmap hb).2
    rw [cepsScaledQuotientAtRoot, cepsScaledQuotient_eq_actual dom hW hθ hD lam hz hb]
    exact ⟨cepsQ_norm_ge_on_rootZone dom hW hθ hD hm hq' hζ,
      cepsQ_norm_le_on_rootZone dom hW hθ hD hm hq' hζ⟩
  have hne : ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      cepsScaledQuotientAtRoot D θ ρW lam z sign b ≠ 0 := by
    intro b hb
    exact norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num)).trans_le (hbounds b hb).1)
  refine ⟨hd, fun b hb => (hbounds b hb).2, hd.inv hne, fun b hb => ⟨(hbounds b hb).1, ?_⟩⟩
  rw [norm_inv]
  have hlo : 0 < ‖cepsScaledQuotientAtRoot D θ ρW lam z sign b‖ := norm_pos_iff.mpr (hne b hb)
  calc
    _ ≤ (cepsVarLo D / 4)⁻¹ :=
      (inv_le_inv₀ hlo (div_pos (cepsVarLo_pos hD) (by norm_num))).mpr (hbounds b hb).1
    _ = 4 / cepsVarLo D := by ring

include hW hθ hD in
theorem cepsScaledQuotientAtRoot_inverse_taylor_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    ‖(cepsScaledQuotientAtRoot D θ ρW lam z sign b)⁻¹ -
      complexTaylorSum (fun b => (cepsScaledQuotientAtRoot D θ ρW lam z sign b)⁻¹) n 0 b‖ ≤
      ((n.factorial : ℝ) * (4 / cepsVarLo D) / (dom.canonScaleRadius lam z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨_, _, hi, hm⟩ := cepsScaledQuotientAtRoot_budget dom hW hθ hD lam hz hsign
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (canonScaleRadius_pos dom hW hθ hD lam z) hi (fun b hb => (hm b hb).2) hb

end PGM
