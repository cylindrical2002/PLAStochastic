import PLAStochastic.Index.CEPS.Scaled.TrueZero
import PLAStochastic.ForMathlib.Analysis.Calculus.SecondDSlopeScale

/-! # Exact physical scaling of the true removable entrance and bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsScaledTrueG_eq_normalG {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) {b : ℝ} (hb : b ≠ 0) (ξ : ℂ) :
    cepsScaledTrueG dom ρW lam z b ξ =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).normalG
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) ((b : ℂ) * ξ) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  unfold cepsScaledTrueG cepsCanonTrueWeight CepsNormalData.normalG cepsWHNormalData
  rw [ofReal_mul]
  have he : -ξ * (1 + (b : ℂ) * lam) = -((b : ℂ) * ξ) * ((1 + (b : ℂ) * lam) / b) := by field_simp
  rw [he]
  ring

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrue_physical_slopes (M : ℝ) {b lam : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
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
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hbs
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
  have hμchart : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ := by
    rw [ofReal_mul]
    exact dom.μ_lt_chart (hμ.le.trans (by linarith [dom.μ₀_pos]))
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
  have hμD : |b * lam| ≤ dom.μ₀ := by
    have ht : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμ
    rw [norm_real, Real.norm_eq_abs] at ht
    linarith [dom.μ₀_pos]
  have hF : DifferentiableOn ℂ F (ball 0 (dom.c₀ / 2)) := by
    have hbase := cepsCanonTrueWeight_spatial_differentiableOn dom hW hθ hD hμD
      (hq.le.trans (half_le_self dom.q₀_pos.le))
    have hraw := ((differentiableOn_id.neg.mul_const l).cexp).mul hbase
    apply hraw.congr
    intro ζ _
    dsimp only [F, a, μ, q, cepsWHNormalData, CepsNormalData.normalG, Pi.mul_apply, Pi.neg_apply,
      id_eq, cepsCanonTrueWeight]
    rw [ofReal_mul]
    ring
  have hmMem : a.βm ∈ ball (0 : ℂ) (dom.c₀ / 2) := by
    rw [← hm]
    exact mem_ball_zero_iff.mpr ((cepsScaledRootCurve_norm_le dom hW hθ hD lam hz hbC).2.trans_lt
      (by linarith [dom.c₀_pos]))
  have hpMem : a.βp ∈ ball (0 : ℂ) (dom.c₀ / 2) := by
    rw [← hp]
    exact mem_ball_zero_iff.mpr ((cepsScaledRootCurve_norm_le dom hW hθ hD lam hz hbC).1.trans_lt
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
theorem cepsScaledTrueBridge_eq_actual_regular {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    {b lam : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    (b : ℂ) * cepsScaledTrueBridge dom ρW lam z b =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularBridge
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) := by
  obtain ⟨hds, _, hp, hn⟩ := cepsScaledTrue_physical_slopes dom hW hθ hD M hb hz hbs
  have hS := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM hm lam hz hbs
  rw [hds] at hS
  have hSF := (mul_ne_zero_iff.mp hS).2
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold cepsScaledTrueBridge CepsNormalData.regularBridge
  rw [hp, hn, hds]
  field_simp

include hW hθ hD in
theorem cepsScaledTrueEntrance_eq_actual_regular {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    {b lam : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    cepsScaledTrueEntrance dom ρW lam z b =
      (b : ℂ) * (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularEntrance
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) ((b : ℂ) ^ 2 * z) := by
  obtain ⟨hds, hds2, _, _⟩ := cepsScaledTrue_physical_slopes dom hW hθ hD M hb hz hbs
  have hS := cepsScaledTrueDenominator_ne_zero dom hW hθ hD hf hη hM hm lam hz hbs
  rw [hds] at hS
  have hSF := (mul_ne_zero_iff.mp hS).2
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hbs
  have hQb := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD 0 M lam hz).2 b hbE
  have hQ0 := norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num)).trans_le hQb)
  unfold cepsScaledTrueEntrance cepsScaledTrueMarkPrefactor CepsNormalData.regularEntrance
  rw [hds2, hds]
  dsimp only [cepsWHNormalData]
  field_simp

end PGM
