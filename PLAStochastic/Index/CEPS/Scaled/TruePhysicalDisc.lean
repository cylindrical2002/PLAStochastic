import PLAStochastic.Index.CEPS.Scaled.TruePhysicalScaling

/-! # True physical scaling on a full discount disc

The scaling identities are algebraic on the full canonical discount disc,
including its negative-real part. This pays a genuine open neighborhood
for subsequent discount differentiation at imaginary-axis points.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrue_physical_slopes_of_discount_disc {b lam : ℝ} (hb : 0 < b)
    (hμD : |b * lam| ≤ dom.μ₀) {z : ℂ}
    (hqD : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀) :
    let a := cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
    let F := a.normalG (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
      ((1 + (b : ℂ) * lam) / b)
    cepsScaledTrueDenominator dom ρW lam z b = (b : ℂ) * dslope F a.βm a.βp ∧
      cepsScaledTrueEntranceNumerator dom ρW lam z b =
        (b : ℂ) ^ 2 * dslope (dslope F a.βm) a.βp ((b : ℂ) ^ 2 * z) ∧
      cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) = F a.βp ∧
      cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b) = F a.βm := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let a := cepsWHNormalData D θ ρW μ q
  let F := a.normalG (dom.canonL ρW) μ q l
  let rp := cepsScaledSignedRoot D θ ρW lam z 1 b
  let rm := cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hμnorm : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμprod : ‖(b : ℂ) * lam‖ ≤ dom.μ₀ := by simpa only [ofReal_mul] using hμnorm
  have hμchart : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ := dom.μ_lt_chart hμnorm
  have hqeq : q = cepsScaledDiscount b lam z := by
    simp only [q, cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_mul]
  have hp : (b : ℂ) * rp = a.βp := by
    dsimp only [rp, a, μ, cepsWHNormalData]
    rw [hqeq, cepsScaledSignedRoot_plus_actual hW hθ hD hb hμchart, ofReal_mul]
    exact mul_div_cancel₀ _ hb0
  have hm : (b : ℂ) * rm = a.βm := by
    dsimp only [rm, a, μ, cepsWHNormalData]
    rw [hqeq, cepsScaledSignedRoot_minus_actual hW hθ hD hb hμchart, ofReal_mul]
    exact mul_div_cancel₀ _ hb0
  have hcurve : cepsScaledTrueG dom ρW lam z b = fun ξ : ℂ => F ((b : ℂ) * ξ) := by
    funext ξ
    exact cepsScaledTrueG_eq_normalG dom ρW lam z hb.ne' ξ
  have hF : DifferentiableOn ℂ F (ball 0 (dom.c₀ / 2)) := by
    have hbase := cepsCanonTrueWeight_spatial_differentiableOn dom hW hθ hD hμD
      hqD
    have hraw := ((differentiableOn_id.neg.mul_const l).cexp).mul hbase
    apply hraw.congr
    intro ζ _
    dsimp only [F, a, μ, q, cepsWHNormalData, CepsNormalData.normalG, Pi.mul_apply, Pi.neg_apply,
      id_eq, cepsCanonTrueWeight]
    rw [ofReal_mul]
    ring
  have hmMem : a.βm ∈ ball (0 : ℂ) (dom.c₀ / 2) := by
    exact mem_ball_zero_iff.mpr ((dom.norm_rootMinus_le hW hθ hD hμprod hqD).trans_lt
      (by linarith [dom.c₀_pos]))
  have hpMem : a.βp ∈ ball (0 : ℂ) (dom.c₀ / 2) := by
    exact mem_ball_zero_iff.mpr ((dom.norm_rootPlus_le hW hθ hD hμprod hqD).trans_lt
      (by linarith [dom.c₀_pos]))
  have hFd := (hF _ hmMem).differentiableAt (isOpen_ball.mem_nhds hmMem)
  have hSF := (differentiableOn_dslope (isOpen_ball.mem_nhds hmMem)).mpr hF
  have hds := dslope_comp_const_mul hb0 rm rp (by simpa only [hm] using hFd)
  have hds2 := second_dslope_comp_const_mul hb0 rm rp ((b : ℂ) * z)
    (by simpa only [hm] using hFd)
    (by simpa only [hp, hm] using (hSF _ hpMem).differentiableAt (isOpen_ball.mem_nhds hpMem))
  rw [← hcurve, hp, hm] at hds
  rw [← hcurve, hp, hm, show (b : ℂ) * ((b : ℂ) * z) = (b : ℂ) ^ 2 * z by ring] at hds2
  exact ⟨hds, hds2, by simpa only [hp] using congrFun hcurve rp,
    by simpa only [hm] using congrFun hcurve rm⟩

include hW hθ hD in
theorem cepsScaledTrueBridge_eq_actual_on_discount_disc {b lam : ℝ} (hb : 0 < b)
    (hμD : |b * lam| ≤ dom.μ₀) {z : ℂ} (hqD : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀) :
    (b : ℂ) * cepsScaledTrueBridge dom ρW lam z b =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularBridge
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) := by
  obtain ⟨hds, _, hp, hn⟩ := cepsScaledTrue_physical_slopes_of_discount_disc dom hW hθ hD hb hμD hqD
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold cepsScaledTrueBridge CepsNormalData.regularBridge
  rw [hp, hn, hds]
  by_cases hS : dslope
      ((cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).normalG
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b))
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).βm
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).βp = 0
  · simp only [hS, mul_zero, div_zero]
  · field_simp

include hW hθ hD in
theorem cepsScaledTrueEntrance_eq_actual_on_discount_disc {b lam : ℝ} (hb : 0 < b)
    (hμD : |b * lam| ≤ dom.μ₀) {z : ℂ} (hqD : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀) :
    cepsScaledTrueEntrance dom ρW lam z b =
      (b : ℂ) * (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularEntrance
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) ((b : ℂ) ^ 2 * z) := by
  obtain ⟨hds, hds2, _, _⟩ := cepsScaledTrue_physical_slopes_of_discount_disc dom hW hθ hD hb hμD hqD
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold cepsScaledTrueEntrance cepsScaledTrueMarkPrefactor CepsNormalData.regularEntrance
  rw [hds2, hds]
  dsimp only [cepsWHNormalData]
  simp only [div_eq_mul_inv, mul_inv]
  field_simp [hb0]

end PGM
