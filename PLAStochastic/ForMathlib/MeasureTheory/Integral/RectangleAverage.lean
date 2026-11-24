import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Exact positive rectangle averages under signed affine changes of variables -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Lebesgue integration under a nonzero signed affine scale, without finiteness assumptions. -/
theorem lintegral_affine_eq_div (f : ℝ → ℝ≥0∞) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (∫⁻ u : ℝ, f (a+b*u)) = (∫⁻ x : ℝ, f x) / ENNReal.ofReal |b| := by
  have h := (Homeomorph.mulLeft₀ b hb).toMeasurableEquiv.measurableEmbedding.lintegral_map
    (μ := (volume : Measure ℝ)) (fun x => f (a+x))
  change (∫⁻ x : ℝ, f (a+x) ∂Measure.map (fun u : ℝ => b*u) volume) =
    (∫⁻ u : ℝ, f (a+b*u)) at h
  rw [Real.map_volume_mul_left hb, lintegral_smul_measure,
    lintegral_add_left_eq_self] at h
  simpa only [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hb),
    ENNReal.div_eq_inv_mul, smul_eq_mul] using h.symm

/-- The affine change of variables respects an arbitrary measurable target restriction. -/
theorem setLIntegral_affine_preimage_eq_div (f : ℝ → ℝ≥0∞) {S : Set ℝ}
    (hS : MeasurableSet S) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (∫⁻ u in (fun u => a+b*u) ⁻¹' S, f (a+b*u)) =
      (∫⁻ x in S, f x) / ENNReal.ofReal |b| := by
  rw [← lintegral_indicator (hS.preimage (by fun_prop)), ← lintegral_indicator hS]
  have h := lintegral_affine_eq_div (S.indicator f) a hb
  rw [← h]
  apply lintegral_congr
  intro u
  rfl

/-- A positive one-sided level interval is exactly a unit-interval average after normalization. -/
theorem setLIntegral_Ioo_add_mul_average (f : ℝ → ℝ≥0∞) (m : ℝ) {e : ℝ} (he : 0 < e) :
    (∫⁻ l in Ioo m (m+e), f l) / ENNReal.ofReal e =
      ∫⁻ a in Ioo (0 : ℝ) 1, f (m+e*a) := by
  have hpre : (fun a : ℝ => m+e*a) ⁻¹' Ioo m (m+e) = Ioo 0 1 := by
    ext a
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1,h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1,h2⟩
      constructor <;> nlinarith
  simpa only [hpre, abs_of_pos he] using
    (setLIntegral_affine_preimage_eq_div f (S := Ioo m (m+e)) measurableSet_Ioo m he.ne').symm

/-- Reflection gives the corresponding normalized interval below the upper level. -/
theorem setLIntegral_Ioo_sub_mul_average (f : ℝ → ℝ≥0∞) (M : ℝ) {d : ℝ} (hd : 0 < d) :
    (∫⁻ h in Ioo (M-d) M, f h) / ENNReal.ofReal d =
      ∫⁻ b in Ioo (0 : ℝ) 1, f (M-d*b) := by
  have hpre : (fun b : ℝ => M+(-d)*b) ⁻¹' Ioo (M-d) M = Ioo 0 1 := by
    ext b
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1,h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1,h2⟩
      constructor <;> nlinarith
  have h := setLIntegral_affine_preimage_eq_div f (S := Ioo (M-d) M) measurableSet_Ioo M (neg_ne_zero.mpr hd.ne')
  rw [hpre] at h
  simpa only [abs_neg, abs_of_pos hd, neg_mul, ← sub_eq_add_neg] using h.symm

/-- Every nonnegative two-dimensional thin-rectangle average is exactly a unit-square average. -/
theorem setLIntegral_rectangle_average (F : ℝ → ℝ → ℝ≥0∞) (m M : ℝ)
    {e d : ℝ} (he : 0 < e) (hd : 0 < d) :
    (∫⁻ l in Ioo m (m+e), ∫⁻ h in Ioo (M-d) M, F l h) /
      (ENNReal.ofReal e * ENNReal.ofReal d) =
      ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1, F (m+e*a) (M-d*b) := by
  have he0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.mpr he).ne'
  have hd0 : ENNReal.ofReal d ≠ 0 := (ENNReal.ofReal_pos.mpr hd).ne'
  have hdtop : (ENNReal.ofReal d)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hd0
  rw [← setLIntegral_Ioo_add_mul_average (fun l => ∫⁻ b in Ioo (0 : ℝ) 1, F l (M-d*b)) m he]
  have hin (l : ℝ) : (∫⁻ b in Ioo (0 : ℝ) 1, F l (M-d*b)) =
      (∫⁻ h in Ioo (M-d) M, F l h) / ENNReal.ofReal d :=
    (setLIntegral_Ioo_sub_mul_average (F l) M hd).symm
  simp_rw [hin]
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ hdtop,
    ENNReal.mul_inv (Or.inl he0) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm ((ENNReal.ofReal e)⁻¹) ((ENNReal.ofReal d)⁻¹), mul_assoc]

end BrownianAffine
