import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeBudget
import PLAStochastic.ForMathlib.Analysis.Calculus.DSlopeScale

/-! # Exact identification with the actual normal bridge after scaling -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_eq_actual_regular {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {b lam : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    (b : ℂ) * cepsScaledSurrogateBridge dom ρW N lam z b =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularBridge
        (cepsCanonDriftTaylor dom ρW N) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let a := cepsWHNormalData D θ ρW μ q
  let L := cepsCanonDriftTaylor dom ρW N
  let F := a.normalG L μ q l
  let rp := cepsScaledSignedRoot D θ ρW lam z 1 b
  let rm := cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsub : dom.surrogateRegularScaleRadius N M lam z ≤ dom.canonScaleRadius lam z :=
    (min_le_left _ _).trans ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le))
  have hbC := ball_subset_ball hsub hbs
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
  have hμchart : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ := by
    rw [ofReal_mul]
    exact dom.μ_lt_chart (hμ.le.trans (by linarith [dom.μ₀_pos]))
  have hqeq : cepsComplexScaledDiscount lam z b = cepsScaledDiscount b lam z := by
    simp only [cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_mul]
  have hp : (b : ℂ) * rp = a.βp := by
    dsimp only [rp, a, μ, q, cepsWHNormalData]
    rw [hqeq, cepsScaledSignedRoot_plus_actual hW hθ hD hb hμchart, ofReal_mul]
    exact mul_div_cancel₀ _ hb0
  have hm : (b : ℂ) * rm = a.βm := by
    dsimp only [rm, a, μ, q, cepsWHNormalData]
    rw [hqeq, cepsScaledSignedRoot_minus_actual hW hθ hD hb hμchart, ofReal_mul]
    exact mul_div_cancel₀ _ hb0
  have hcurve : cepsScaledSurrogateG dom ρW N lam z b = fun ξ : ℂ => F ((b : ℂ) * ξ) := by
    funext ξ
    dsimp only [cepsScaledSurrogateG, F, CepsNormalData.normalG, a, cepsWHNormalData, L, μ, q,
      cepsCanonSurrogateWeight]
    have he : -ξ * (1 + (b : ℂ) * lam) = -((b : ℂ) * ξ) * l := by
      dsimp only [l]
      field_simp
    rw [he]
    ring
  have hF : DifferentiableOn ℂ F (ball 0 (dom.c₀ / 2)) := by
    have hbase := cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ.le hq
    have hraw := ((differentiableOn_id.neg.mul_const l).cexp).mul hbase
    apply hraw.congr
    intro ζ _
    dsimp only [F, a, L, μ, q, cepsWHNormalData, CepsNormalData.normalG, Pi.mul_apply, Pi.neg_apply,
      id_eq, cepsCanonSurrogateWeight]
    ring
  have hnorm := (cepsScaledRootCurve_norm_le dom hW hθ hD lam hz hbC).2
  have hmem : (b : ℂ) * rm ∈ ball (0 : ℂ) (dom.c₀ / 2) := mem_ball_zero_iff.mpr
    (hnorm.trans_lt (by linarith [dom.c₀_pos]))
  have hds := dslope_comp_const_mul hb0 rm rp
    ((hF _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem))
  rw [← hcurve, hp, hm] at hds
  change cepsScaledSurrogateDenominator dom ρW N lam z b = b * dslope F a.βm a.βp at hds
  have hS := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbs
  have hSphys : dslope F a.βm a.βp ≠ 0 := by
    intro he
    exact hS (by rw [hds, he, mul_zero])
  have hgp : cepsScaledSurrogateG dom ρW N lam z b rp = F a.βp := by
    simpa only [hp] using congrFun hcurve rp
  have hgm : cepsScaledSurrogateG dom ρW N lam z b rm = F a.βm := by
    simpa only [hm] using congrFun hcurve rm
  change (b : ℂ) * (-cepsScaledSurrogateG dom ρW N lam z b rp *
    cepsScaledSurrogateG dom ρW N lam z b rm / cepsScaledSurrogateDenominator dom ρW N lam z b) =
      -F a.βp * F a.βm / dslope F a.βm a.βp
  rw [hgp, hgm, hds]
  field_simp

end PGM
