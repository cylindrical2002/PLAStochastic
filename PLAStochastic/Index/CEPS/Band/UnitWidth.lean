import PLAStochastic.Index.KEP.ReferenceScale.FixedBridge
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Finite bridges in a fixed unit band

Rescaling only the intermediate positions removes moving interval indicators.
Differentiation needs a differentiable step density and a bounded first derivative;
the derivative need not be continuous.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

/-- The `n + 1` step bridge with all intermediate positions in a fixed unit band. -/
def cepsBandUnitBridge (p : ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, l, x, y => p (l * (y - x))
  | n + 1, l, x, y => l * ∫ z in Ioc 0 1,
      cepsBandUnitBridge p n l x z * p (l * (y - z))

/-- Its actual width derivative. -/
def cepsBandUnitBridgeWidth (p p' : ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, l, x, y => p' (l * (y - x)) * (y - x)
  | n + 1, l, x, y =>
      (∫ z in Ioc 0 1, cepsBandUnitBridge p n l x z * p (l * (y - z))) +
      l * ∫ z in Ioc 0 1,
        cepsBandUnitBridgeWidth p p' n l x z * p (l * (y - z)) +
        cepsBandUnitBridge p n l x z * (p' (l * (y - z)) * (y - z))

def cepsBandUnitBound (P R : ℝ) : ℕ → ℝ
  | 0 => P
  | n + 1 => R * cepsBandUnitBound P R n * P

def cepsBandUnitWidthBound (P Q R : ℝ) : ℕ → ℝ
  | 0 => Q
  | n + 1 => cepsBandUnitBound P R n * P +
      R * (cepsBandUnitWidthBound P Q R n * P + cepsBandUnitBound P R n * Q)

theorem cepsBandUnitBound_nonneg {P R : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ cepsBandUnitBound P R n := by
  induction n with
  | zero => exact hP
  | succ n ih => simp only [cepsBandUnitBound]; positivity

theorem cepsBandUnitWidthBound_nonneg {P Q R : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hR : 0 ≤ R) (n : ℕ) : 0 ≤ cepsBandUnitWidthBound P Q R n := by
  induction n with
  | zero => exact hQ
  | succ n ih =>
    have := cepsBandUnitBound_nonneg hP hR n
    simp only [cepsBandUnitWidthBound]; positivity

theorem continuous_cepsBandUnitBridge {p : ℝ → ℝ} (hp : Continuous p) (n : ℕ) :
    Continuous (fun t : ℝ × ℝ × ℝ => cepsBandUnitBridge p n t.1 t.2.1 t.2.2) := by
  induction n with
  | zero => exact hp.comp (continuous_fst.mul (continuous_snd.snd.sub continuous_snd.fst))
  | succ n ih =>
    exact continuous_fst.mul (continuous_integral_Ioc_of_continuous
      ((ih.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk continuous_snd))).mul
        (hp.comp (continuous_fst.fst.mul (continuous_fst.snd.snd.sub continuous_snd)))) 0 1)

theorem measurable_cepsBandUnitBridgeWidth {p p' : ℝ → ℝ}
    (hp : Continuous p) (hp' : Measurable p') (n : ℕ) :
    Measurable (fun t : ℝ × ℝ × ℝ => cepsBandUnitBridgeWidth p p' n t.1 t.2.1 t.2.2) := by
  induction n with
  | zero =>
    exact (hp'.comp (measurable_fst.mul (measurable_snd.snd.sub measurable_snd.fst))).mul
      (measurable_snd.snd.sub measurable_snd.fst)
  | succ n ih =>
    have hb := (continuous_cepsBandUnitBridge hp n).measurable
    have hF := (hb.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.fst.prodMk measurable_snd))).mul
      (hp.measurable.comp (measurable_fst.fst.mul (measurable_fst.snd.snd.sub measurable_snd)))
    have hF' := ((ih.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.fst.prodMk measurable_snd))).mul
      (hp.measurable.comp (measurable_fst.fst.mul (measurable_fst.snd.snd.sub measurable_snd)))).add
      ((hb.comp (measurable_fst.fst.prodMk
        (measurable_fst.snd.fst.prodMk measurable_snd))).mul
        ((hp'.comp (measurable_fst.fst.mul (measurable_fst.snd.snd.sub measurable_snd))).mul
          (measurable_fst.snd.snd.sub measurable_snd)))
    exact hF.stronglyMeasurable.integral_prod_right'.measurable.add
      (measurable_fst.mul hF'.stronglyMeasurable.integral_prod_right'.measurable)

private theorem cepsBand_unit_difference {x y : ℝ} (hx : x ∈ Icc 0 1)
    (hy : y ∈ Icc 0 1) : |y - x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩

theorem cepsBandUnitBridge_bound {p : ℝ → ℝ} {P R : ℝ} (hP : 0 ≤ P)
    (hR : 0 ≤ R) (hp : ∀ t, |p t| ≤ P) (n : ℕ) {l x y : ℝ}
    (hl : |l| ≤ R) (_hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    |cepsBandUnitBridge p n l x y| ≤ cepsBandUnitBound P R n := by
  induction n generalizing y with
  | zero => exact hp _
  | succ n ih =>
    have hb : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        ‖cepsBandUnitBridge p n l x z * p (l * (y - z))‖ ≤ cepsBandUnitBound P R n * P := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (ih ⟨hz.1.le, hz.2⟩) (hp _) (abs_nonneg _) (cepsBandUnitBound_nonneg hP hR n)
    have hi := norm_integral_le_of_norm_le_const hb
    have hi' : |∫ z in Ioc 0 1, cepsBandUnitBridge p n l x z * p (l * (y - z))| ≤
        cepsBandUnitBound P R n * P := by simpa [Measure.real] using hi
    simp only [cepsBandUnitBridge, cepsBandUnitBound, abs_mul]
    exact (mul_le_mul hl hi' (abs_nonneg _) hR).trans_eq (by ring)

theorem cepsBandUnitBridgeWidth_bound {p p' : ℝ → ℝ} {P Q R : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hp : ∀ t, |p t| ≤ P)
    (hp' : ∀ t, |p' t| ≤ Q) (n : ℕ) {l x y : ℝ}
    (hl : |l| ≤ R) (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    |cepsBandUnitBridgeWidth p p' n l x y| ≤ cepsBandUnitWidthBound P Q R n := by
  induction n generalizing y with
  | zero =>
    exact (abs_mul _ _).trans_le ((mul_le_mul (hp' _) (cepsBand_unit_difference hx hy)
      (abs_nonneg _) hQ).trans_eq (mul_one _))
  | succ n ih =>
    have hb : ∀ {z : ℝ}, z ∈ Icc 0 1 → |cepsBandUnitBridge p n l x z| ≤
        cepsBandUnitBound P R n := fun hz => cepsBandUnitBridge_bound hP hR hp n hl hx hz
    have hI : |∫ z in Ioc 0 1, cepsBandUnitBridge p n l x z * p (l * (y - z))| ≤
        cepsBandUnitBound P R n * P := by
      have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (C := cepsBandUnitBound P R n * P) (f := fun z => cepsBandUnitBridge p n l x z * p (l * (y - z))) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hb ⟨hz.1.le, hz.2⟩) (hp _) (abs_nonneg _) (cepsBandUnitBound_nonneg hP hR n))
      simpa [Measure.real, Real.norm_eq_abs] using h
    have hI' : |∫ z in Ioc 0 1,
        cepsBandUnitBridgeWidth p p' n l x z * p (l * (y - z)) +
        cepsBandUnitBridge p n l x z * (p' (l * (y - z)) * (y - z))| ≤
        cepsBandUnitWidthBound P Q R n * P + cepsBandUnitBound P R n * Q := by
      have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
        (C := cepsBandUnitWidthBound P Q R n * P + cepsBandUnitBound P R n * Q)
        (f := fun z => cepsBandUnitBridgeWidth p p' n l x z * p (l * (y - z)) +
          cepsBandUnitBridge p n l x z * (p' (l * (y - z)) * (y - z))) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
          rw [Real.norm_eq_abs]
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]
            exact mul_le_mul (ih ⟨hz.1.le, hz.2⟩) (hp _) (abs_nonneg _)
              (cepsBandUnitWidthBound_nonneg hP hQ hR n)
          · rw [abs_mul, abs_mul]
            exact mul_le_mul (hb ⟨hz.1.le, hz.2⟩)
              ((mul_le_mul (hp' _) (cepsBand_unit_difference ⟨hz.1.le, hz.2⟩ hy)
                (abs_nonneg _) hQ).trans_eq (mul_one _))
              (by positivity) (cepsBandUnitBound_nonneg hP hR n))
      simpa [Measure.real, Real.norm_eq_abs] using h
    simp only [cepsBandUnitBridgeWidth, cepsBandUnitWidthBound]
    exact (abs_add_le _ _).trans (add_le_add hI (by
      rw [abs_mul]; exact mul_le_mul hl hI' (abs_nonneg _) hR))

end
end PGM
