import PLAStochastic.Index.CEPS.Scaled.SurrogateEntrance
import PLAStochastic.ForMathlib.Analysis.Calculus.SecondDSlopeScale

/-! # Exact physical scaling of the removable surrogate entrance -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsScaledSurrogateG_eq_normalG {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℂ} (hb : b ≠ 0) (ξ : ℂ) :
    cepsScaledSurrogateG dom ρW N lam z b ξ =
      (cepsWHNormalData D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b)).normalG
        (cepsCanonDriftTaylor dom ρW N) (b * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + b * lam) / b) (b * ξ) := by
  unfold cepsScaledSurrogateG CepsNormalData.normalG cepsWHNormalData cepsCanonSurrogateWeight
  have he : -ξ * (1 + b * lam) = -(b * ξ) * ((1 + b * lam) / b) := by field_simp
  rw [he]
  ring

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_eq_actual_regular {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {b lam : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    cepsScaledSurrogateEntrance dom ρW N lam z b =
      (b : ℂ) * (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularEntrance
        (cepsCanonDriftTaylor dom ρW N) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) ((b : ℂ) ^ 2 * z) := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let a := cepsWHNormalData D θ ρW μ q
  let L := cepsCanonDriftTaylor dom ρW N
  let F := a.normalG L μ q l
  let rp := cepsScaledSignedRoot D θ ρW lam z 1 b
  let rm := cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hrad : dom.entranceScaleRadius N M lam z ≤ dom.canonScaleRadius lam z :=
    (min_le_right _ _).trans (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))
  have hbC := ball_subset_ball hrad hbs
  have hbReg := ball_subset_ball (min_le_left _ _) hbs
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
  have hcurve : cepsScaledSurrogateG dom ρW N lam z b = fun ξ : ℂ => F ((b : ℂ) * ξ) := by
    funext ξ
    exact cepsScaledSurrogateG_eq_normalG dom ρW N lam z hb0 ξ
  have hF : DifferentiableOn ℂ F (ball 0 (dom.c₀ / 2)) := by
    have hbase := cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ.le hq
    have hraw := ((differentiableOn_id.neg.mul_const l).cexp).mul hbase
    apply hraw.congr
    intro ζ _
    dsimp only [F, a, L, μ, q, cepsWHNormalData, CepsNormalData.normalG, Pi.mul_apply, Pi.neg_apply,
      id_eq, cepsCanonSurrogateWeight]
    ring
  have hnorm := (cepsScaledRootCurve_norm_le dom hW hθ hD lam hz hbC).2
  have hmMem : a.βm ∈ ball (0 : ℂ) (dom.c₀ / 2) := by
    rw [← hm]
    exact mem_ball_zero_iff.mpr (hnorm.trans_lt (by linarith [dom.c₀_pos]))
  have hpMem : a.βp ∈ ball (0 : ℂ) (dom.c₀ / 2) := by
    have hn := (cepsScaledRootCurve_norm_le dom hW hθ hD lam hz hbC).1
    rw [← hp]
    exact mem_ball_zero_iff.mpr (hn.trans_lt (by linarith [dom.c₀_pos]))
  have hFd := (hF _ hmMem).differentiableAt (isOpen_ball.mem_nhds hmMem)
  have hSF : DifferentiableOn ℂ (dslope F a.βm) (ball 0 (dom.c₀ / 2)) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds hmMem)).mpr hF
  have hds := dslope_comp_const_mul hb0 rm rp (by simpa only [hm] using hFd)
  have hds2 := second_dslope_comp_const_mul hb0 rm rp ((b : ℂ) * z)
    (by simpa only [hm] using hFd)
    (by simpa only [hp, hm] using (hSF _ hpMem).differentiableAt (isOpen_ball.mem_nhds hpMem))
  rw [← hcurve, hp, hm] at hds
  rw [← hcurve, hp, hm, show (b : ℂ) * ((b : ℂ) * z) = (b : ℂ) ^ 2 * z by ring] at hds2
  change cepsScaledSurrogateDenominator dom ρW N lam z b = (b : ℂ) * dslope F a.βm a.βp at hds
  have hS := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbReg
  have hSphys : dslope F a.βm a.βp ≠ 0 := by
    intro he
    exact hS (by rw [hds, he, mul_zero])
  have hQlo := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).2 b hbs
  have hQ0 : a.Q ((b : ℂ) ^ 2 * z) ≠ 0 := norm_pos_iff.mp
    ((div_pos (cepsVarLo_pos hD) (by norm_num)).trans_le hQlo)
  change (-exp (L μ q ((b : ℂ) ^ 2 * z)) *
      dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b) rm) rp ((b : ℂ) * z) /
        (a.Q ((b : ℂ) ^ 2 * z) * cepsScaledSurrogateDenominator dom ρW N lam z b)) =
      (b : ℂ) * (-exp (L μ q ((b : ℂ) ^ 2 * z)) * dslope (dslope F a.βm) a.βp ((b : ℂ) ^ 2 * z) /
        (a.Q ((b : ℂ) ^ 2 * z) * dslope F a.βm a.βp))
  rw [hds2, hds]
  field_simp

end PGM
