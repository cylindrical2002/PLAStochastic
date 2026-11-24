import PLAStochastic.Index.CEPS.Scaled.TruePositivePair
import PLAStochastic.Index.CEPS.Scaled.TruePhysicalDisc
import PLAStochastic.Index.CEPS.Normal.HalfLineRegular
import PLAStochastic.Index.CEPS.Normal.RootCompatibility

/-! # Exact physical scaling of the actual half-line components on the full discount disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_eq_actual_on_discount_disc
    {b lam : ℝ} (hb : 0 < b) (hμD : |b * lam| ≤ dom.μ₀) {z : ℂ}
    (hqD : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀) :
    (b : ℂ) * cepsScaledTrueHalfBridge dom ρW lam z b =
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).halfBridge
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)
          ((1 + (b : ℂ) * lam) / b) := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let a := cepsWHNormalData D θ ρW μ q
  let L := dom.canonL ρW
  let rp := cepsScaledSignedRoot D θ ρW lam z 1 b
  let rm := cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hμdom : ‖μ‖ ≤ dom.μ₀ := by
    simpa only [μ, ← ofReal_mul, norm_real, Real.norm_eq_abs] using hμD
  have hqdom : ‖q‖ ≤ dom.q₀ := hqD
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
  have hgp : cepsScaledTrueG dom ρW lam z b rp = a.normalG L μ q l a.βp := by
    rw [← hp]
    exact cepsScaledTrueG_eq_normalG dom ρW lam z hb.ne' rp
  change (b : ℂ) * ((rp - rm) * cepsScaledTrueG dom ρW lam z b rp) = a.halfBridge L μ q l
  rw [hgp, CepsNormalData.halfBridge, hψ,
    show -a.βp * l - 2 * L μ q a.βp = -a.βp * l + -2 * L μ q a.βp by ring,
    exp_add]
  unfold CepsNormalData.normalG
  rw [← hp, ← hm]
  ring

include hW hθ hD in
theorem cepsScaledTrueHalfEntrance_eq_actual_on_discount_disc
    {b lam : ℝ} (hb : 0 < b) (hμD : |b * lam| ≤ dom.μ₀) {z : ℂ}
    (_hqD : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀) :
    cepsScaledTrueHalfEntrance dom ρW lam z b = (b : ℂ) *
      (cepsWHNormalData D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b)).regularHalfEntrance
        (dom.canonL ρW) ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμchart := dom.μ_lt_chart hμn
  have hm : (b : ℂ) * cepsScaledSignedRoot D θ ρW lam z (-1) b =
      cepsRootMinus D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) := by
    rw [cepsScaledSignedRoot_minus_actual hW hθ hD hb hμchart, mul_div_cancel₀ _ hb0]
    simp only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  have hg : (b : ℂ) ^ 2 * z -
      cepsRootMinus D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) =
        (b : ℂ) * ((b : ℂ) * z - cepsScaledSignedRoot D θ ρW lam z (-1) b) := by
    rw [← hm]; ring
  unfold cepsScaledTrueHalfEntrance cepsScaledTrueMarkPrefactor CepsNormalData.regularHalfEntrance
  dsimp only [cepsWHNormalData, CepsCanonDomain.canonL]
  rw [hg]
  simp only [div_eq_mul_inv, mul_inv]
  field_simp

end PGM
