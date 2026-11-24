import PLAStochastic.Index.CEPS.Scaled.ActualSurrogateBridge
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeCorrection
import PLAStochastic.Index.CEPS.Normal.RootCompatibility

/-! # Exact physical scaling of the surrogate half-line bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_eq_actual (N : ℕ)
    {b lam : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    (b : ℂ) * cepsScaledSurrogateHalfBridge dom ρW N lam z b =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).halfBridge
        (cepsCanonDriftTaylor dom ρW N) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let a := cepsWHNormalData D θ ρW μ q
  let L := cepsCanonDriftTaylor dom ρW N
  let rp := cepsScaledSignedRoot D θ ρW lam z 1 b
  let rm := cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbs
  have hμdom : ‖μ‖ ≤ dom.μ₀ := hμ.le.trans (by linarith [dom.μ₀_pos])
  have hqdom : ‖q‖ ≤ dom.q₀ := hq.le.trans (by linarith [dom.q₀_pos])
  have hμchart : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ := by
    rw [ofReal_mul]
    exact dom.μ_lt_chart hμdom
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
  have hψ : a.ψp = (a.βp - a.βm) * a.Q a.βp := by
    have hcompat := (cepsNormalData_root_compatibility hW hθ hD (dom.μ_lt_chart hμdom)
      (dom.norm_cepsRootR_lt hW hθ hD hμdom hqdom)).1
    have hqp := CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμdom hqdom
      (CepsC6.ball_c₀_subset dom (CepsC6.rootPlus_mem_ball dom hW hθ hD hμdom hqdom))
    change deriv (cepsCgfShift ρW μ) (cepsRootPlus D θ ρW μ q) =
      (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q) *
        cepsQuotA D θ ρW μ q (cepsRootPlus D θ ρW μ q) at hcompat
    change deriv (cepsCgfShift ρW μ) (cepsRootPlus D θ ρW μ q) =
      (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q) *
        cepsQ D θ ρW μ q (cepsRootPlus D θ ρW μ q)
    rw [hqp]
    exact hcompat
  have hgp : cepsScaledSurrogateG dom ρW N lam z b rp = a.normalG L μ q l a.βp := by
    rw [← hp]
    dsimp only [cepsScaledSurrogateG, CepsNormalData.normalG, a, cepsWHNormalData, L, μ, q,
      cepsCanonSurrogateWeight]
    have he : -rp * (1 + (b : ℂ) * lam) = -((b : ℂ) * rp) * l := by
      dsimp only [l]
      field_simp
    rw [he]
    ring
  change (b : ℂ) * ((rp - rm) * cepsScaledSurrogateG dom ρW N lam z b rp) = a.halfBridge L μ q l
  rw [hgp, CepsNormalData.halfBridge, hψ,
    show -a.βp * l - 2 * L μ q a.βp = -a.βp * l + -2 * L μ q a.βp by ring,
    exp_add]
  unfold CepsNormalData.normalG
  rw [← hp, ← hm]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_eq_actual {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {b lam : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 ≤ z.re)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    (b : ℂ) * cepsScaledSurrogateBridgeCorrection dom ρW N lam z b =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularBridge
        (cepsCanonDriftTaylor dom ρW N) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) -
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).halfBridge
        (cepsCanonDriftTaylor dom ρW N) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) := by
  have hsub : dom.surrogateRegularScaleRadius N M lam z ≤ dom.canonScaleRadius lam z :=
    (min_le_left _ _).trans ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le))
  rw [cepsScaledSurrogateBridgeCorrection, mul_sub,
    cepsScaledSurrogateBridge_eq_actual_regular dom hW hθ hD hf hη hM N hN hb hz hbs,
    cepsScaledSurrogateHalfBridge_eq_actual dom hW hθ hD N hb hz (ball_subset_ball hsub hbs)]

end PGM
