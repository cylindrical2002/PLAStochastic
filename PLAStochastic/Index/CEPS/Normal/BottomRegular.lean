import PLAStochastic.Index.CEPS.Normal.DividedDifference
import PLAStochastic.ForMathlib.Analysis.Complex.InverseDSlope

/-! # The lower-end unmarked normal entrance in genuine divided differences -/

noncomputable section
open Complex Set Metric
namespace PGM.CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ)

def normalK (ζ : ℂ) : ℂ := (a.normalG L μ q l ζ)⁻¹

def regularBottomEntrance : ℂ :=
  exp (-L μ q 0) * dslope (dslope (a.normalK L μ q l) a.βm) a.βp 0 /
    dslope (a.normalK L μ q l) a.βm a.βp

theorem normalK_dslope (hf : DifferentiableAt ℂ (a.normalG L μ q l) a.βm)
    (hm : a.Q a.βm ≠ 0) (hp : a.Q a.βp ≠ 0) :
    dslope (a.normalK L μ q l) a.βm a.βp =
      -dslope (a.normalG L μ q l) a.βm a.βp /
        (a.normalG L μ q l a.βm * a.normalG L μ q l a.βp) :=
  dslope_inv_eq hf (a.normalG_ne L μ q l hm) (a.normalG_ne L μ q l hp)

theorem normalG_zero_ratio (hQ0 : a.Q 0 ≠ 0) :
    a.normalG L μ q l a.βp / a.normalG L μ q l 0 =
      exp (-a.βp * l) * a.reflectedN L μ q := by
  unfold normalG reflectedN
  simp only [neg_zero, zero_mul, exp_zero, one_mul]
  rw [exp_sub]
  simp only [neg_mul, exp_neg]
  field_simp

theorem bottomEntrance_eq_regular
    (hm : a.Q a.βm ≠ 0) (hp : a.Q a.βp ≠ 0) (h0 : a.Q 0 ≠ 0)
    (hab : a.βp ≠ a.βm) (ha : a.βp ≠ 0) (hb : a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) (hd : a.d 0 = -a.βp * a.βm * a.Q 0) :
    a.bottomEntrance L μ q l = a.regularBottomEntrance L μ q l := by
  let G := a.normalG L μ q l
  let K := a.normalK L μ q l
  have hgm : G a.βm ≠ 0 := a.normalG_ne L μ q l hm
  have hgp : G a.βp ≠ 0 := a.normalG_ne L μ q l hp
  have hg0 : G 0 ≠ 0 := a.normalG_ne L μ q l h0
  have hδ : a.delta L μ q l = 1 - G a.βp / G a.βm := by
    rw [delta, ← a.normalG_root_ratio L μ q l hm]
  have hdiff : G a.βm - G a.βp ≠ 0 := by
    intro h
    have he : G a.βp = G a.βm := (sub_eq_zero.mp h).symm
    rw [hδ, he, div_self hgm, sub_self] at hΔ
    exact hΔ rfl
  have hS : dslope K a.βm a.βp = (G a.βm - G a.βp) /
      ((a.βp - a.βm) * G a.βm * G a.βp) := by
    rw [dslope_of_ne _ hab]
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    change (a.βp - a.βm)⁻¹ * ((G a.βp)⁻¹ - (G a.βm)⁻¹) = _
    field_simp
  have hS0 : dslope K a.βm a.βp ≠ 0 := by
    rw [hS]
    exact div_ne_zero hdiff (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab) hgm) hgp)
  have hR : exp (-a.βp * l) * a.reflectedN L μ q = G a.βp / G 0 :=
    (a.normalG_zero_ratio L μ q l h0).symm
  have hN : a.bottomNumerator L μ q l = -a.βm +
      a.βp * (G a.βp / G a.βm) - a.eta * (G a.βp / G 0) := by
    unfold bottomNumerator
    rw [mul_assoc a.βp _ _, ← a.normalG_root_ratio L μ q l hm,
      mul_assoc a.eta _ _, hR]
  unfold bottomEntrance regularBottomEntrance
  rw [a.exp_factorMinus L μ q h0, hd, hN, hδ]
  change _ = exp (-L μ q 0) * dslope (dslope K a.βm) a.βp 0 / dslope K a.βm a.βp
  rw [dslope_of_ne _ (Ne.symm ha)]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  rw [dslope_of_ne _ (Ne.symm hb), hS]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  change _ = exp (-L μ q 0) * ((0 - a.βp)⁻¹ *
    ((0 - a.βm)⁻¹ * ((G 0)⁻¹ - (G a.βm)⁻¹) -
      (G a.βm - G a.βp) / ((a.βp - a.βm) * G a.βm * G a.βp))) /
    ((G a.βm - G a.βp) / ((a.βp - a.βm) * G a.βm * G a.βp))
  rw [exp_neg]
  unfold eta
  field_simp
  ring

end PGM.CepsNormalData
