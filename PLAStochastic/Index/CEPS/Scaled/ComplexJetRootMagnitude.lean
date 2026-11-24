import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootDomain
import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootStability

/-! # Quadratic root and gap magnitudes uniform on bounded complex variance regions -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteRadicandCoercivity (vlo vhi : ℝ) : ℝ :=
  2 * vhi ^ 2 / vlo + 1 + vhi ^ 2 / vlo ^ 2

def cepsFiniteQuadraticRootBound (vlo : ℝ) : ℝ :=
  1 / vlo + Real.sqrt (2 / vlo + 1 / vlo ^ 2)

def cepsFiniteQuadraticGapLower (vlo vhi : ℝ) : ℝ :=
  Real.sqrt (vlo / cepsFiniteRadicandCoercivity vlo vhi)

theorem cepsComplexQuadraticRadicand_re (v : ℂ) (hv : v ≠ 0) (lam : ℝ) :
    (((lam : ℂ) ^ 2 / (2 * v)).re) = (lam ^ 2 / 2) * (v.re / ‖v‖ ^ 2) := by
  have he : (lam : ℂ) ^ 2 / (2 * v) = ((lam ^ 2 / 2 : ℝ) : ℂ) * v⁻¹ := by
    push_cast
    field_simp [hv]
  rw [he, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, inv_re, normSq_eq_norm_sq]

/-- A bounded complex variance with real part bounded away from zero gives a uniform
radicand coercivity estimate on the whole right frequency half-plane. -/
theorem cepsComplexQuadraticRadicand_coercive {v : ℂ} {vlo vhi : ℝ}
    (hlo : 0 < vlo) (hvre : vlo ≤ v.re) (hvhi : ‖v‖ ≤ vhi) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) :
    lam ^ 2 + ‖z‖ ≤ cepsFiniteRadicandCoercivity vlo vhi *
      ‖z + (lam : ℂ) ^ 2 / (2 * v)‖ := by
  let a := (lam : ℂ) ^ 2 / (2 * v)
  let w := z + a
  have hnv : vlo ≤ ‖v‖ := hvre.trans (re_le_norm _)
  have hvpos : 0 < ‖v‖ := hlo.trans_le hnv
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  have hhi : 0 < vhi := hvpos.trans_le hvhi
  have hinv : vlo / vhi ^ 2 ≤ v.re / ‖v‖ ^ 2 := by
    calc
      _ ≤ vlo / ‖v‖ ^ 2 := div_le_div_of_nonneg_left hlo.le (pow_pos hvpos 2)
        (pow_le_pow_left₀ (norm_nonneg _) hvhi 2)
      _ ≤ _ := div_le_div_of_nonneg_right hvre (by positivity)
  have hlower : (lam ^ 2 / 2) * (vlo / vhi ^ 2) ≤ ‖w‖ := by
    calc
      _ ≤ (lam ^ 2 / 2) * (v.re / ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = a.re := (cepsComplexQuadraticRadicand_re v hv0 lam).symm
      _ ≤ w.re := by dsimp only [w]; rw [add_re]; exact le_add_of_nonneg_left hz
      _ ≤ _ := re_le_norm _
  have hlam : lam ^ 2 ≤ (2 * vhi ^ 2 / vlo) * ‖w‖ := by
    have hh : (lam ^ 2 * vlo / 2) / vhi ^ 2 ≤ ‖w‖ := by
      convert hlower using 1; ring
    have hh' := (div_le_iff₀ (pow_pos hhi 2)).mp hh
    rw [div_mul_eq_mul_div, le_div_iff₀ hlo]
    nlinarith
  have hanorm : ‖a‖ ≤ lam ^ 2 / (2 * vlo) := by
    dsimp [a]
    rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, norm_mul, norm_ofNat]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have ha : ‖a‖ ≤ (vhi ^ 2 / vlo ^ 2) * ‖w‖ := by
    calc
      _ ≤ lam ^ 2 / (2 * vlo) := hanorm
      _ ≤ ((2 * vhi ^ 2 / vlo) * ‖w‖) / (2 * vlo) :=
        div_le_div_of_nonneg_right hlam (by positivity)
      _ = _ := by field_simp
  have hzNorm : ‖z‖ ≤ (1 + vhi ^ 2 / vlo ^ 2) * ‖w‖ := by
    have ht := norm_sub_le w a
    rw [show w - a = z by dsimp [w]; ring] at ht
    calc
      ‖z‖ ≤ ‖w‖ + ‖a‖ := ht
      _ ≤ ‖w‖ + (vhi ^ 2 / vlo ^ 2) * ‖w‖ := add_le_add le_rfl ha
      _ = _ := by ring
  exact (add_le_add hlam hzNorm).trans_eq (by dsimp [cepsFiniteRadicandCoercivity, w, a]; ring)

end PGM
