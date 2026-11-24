import PLAStochastic.Swing.Gaussian.Bridge.DensityAlgebra

/-! The exact finite Gaussian bridge density, obtained by two translations and Tonelli. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def gaussianBridgeProductDensity (m : ℕ) (r : ℝ≥0) (z : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianPDFReal 0 r (-(∑ i, z i))/gaussianPDFReal 0 ((m : ℝ≥0)+r) 0)

theorem gaussianBridgeProductDensity_measurable (m : ℕ) (r : ℝ≥0) :
    Measurable (gaussianBridgeProductDensity m r) := by
  unfold gaussianBridgeProductDensity
  fun_prop

theorem gaussianBridge_density_factor_enn (m : ℕ) {r : ℝ≥0} (hr : 0 < r)
    (z : Fin m → ℝ) (y : ℝ) :
    ENNReal.ofReal (Real.exp ((-y/((m : ℝ)+r))*(∑ i, z i)-(m : ℝ)*(-y/((m : ℝ)+r))^2/2))*
      gaussianPDF 0 r (y-((∑ i, z i)+(m : ℝ)*y/((m : ℝ)+r))) =
    gaussianPDF 0 ((m : ℝ≥0)+r) y * gaussianBridgeProductDensity m r z := by
  unfold gaussianPDF gaussianBridgeProductDensity
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianBridge_density_factor m hr]

/-- The joint bridge-increment and endpoint transform of independent Gaussian coordinates. -/
def gaussianBridgeProductTransform (m : ℕ) (r : ℝ≥0) (p : (Fin m → ℝ) × ℝ) :
    (Fin m → ℝ) × ℝ :=
  ((fun i => p.1 i-((∑ j, p.1 j)+p.2)/((m : ℝ)+r)), (∑ j, p.1 j)+p.2)

theorem gaussianBridgeProductTransform_measurable (m : ℕ) (r : ℝ≥0) :
    Measurable (gaussianBridgeProductTransform m r) := by
  unfold gaussianBridgeProductTransform
  fun_prop

/-- The integral identity is valid for every nonnegative measurable joint test. -/
theorem gaussianBridgeProductTransform_lintegral (m : ℕ) {r : ℝ≥0} (hr : 0 < r)
    {F : (Fin m → ℝ) × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F (gaussianBridgeProductTransform m r p)
      ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (gaussianReal 0 r)) =
    ∫⁻ p, F p ∂((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).withDensity
      (gaussianBridgeProductDensity m r)).prod (gaussianReal 0 ((m : ℝ≥0)+r)) := by
  let P := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let t : ℝ := (m : ℝ)+r
  have ht : ((m : ℝ≥0)+r) ≠ 0 := by positivity
  have hraw : Measurable (fun p : (Fin m → ℝ) × ℝ =>
      gaussianPDF 0 r (p.2-∑ i, p.1 i)*F ((fun i => p.1 i-p.2/t), p.2)) := by
    apply Measurable.mul
    · fun_prop
    · apply hF.comp
      fun_prop
  rw [lintegral_prod (fun p : (Fin m → ℝ) × ℝ => F (gaussianBridgeProductTransform m r p))
    ((hF.comp (gaussianBridgeProductTransform_measurable m r)).aemeasurable)]
  change (∫⁻ z, ∫⁻ v, F ((fun i => z i-((∑ j, z j)+v)/t), (∑ j, z j)+v)
    ∂gaussianReal 0 r ∂P) = _
  have hinner (z : Fin m → ℝ) :
      (∫⁻ v, F ((fun i => z i-((∑ j, z j)+v)/t), (∑ j, z j)+v) ∂gaussianReal 0 r) =
      ∫⁻ y, gaussianPDF 0 r (y-∑ j, z j)*F ((fun i => z i-y/t), y) := by
    exact gaussianReal_lintegral_translate hr.ne' (∑ j, z j)
      (hF.comp (show Measurable (fun y : ℝ => ((fun i => z i-y/t), y)) by fun_prop))
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hraw.aemeasurable]
  have hshift (y : ℝ) :
      (∫⁻ z, gaussianPDF 0 r (y-∑ j, z j)*F ((fun i => z i-y/t), y) ∂P) =
      ∫⁻ z, gaussianPDF 0 ((m : ℝ≥0)+r) y * gaussianBridgeProductDensity m r z * F (z, y) ∂P := by
    let f : (Fin m → ℝ) → ℝ≥0∞ := fun z =>
      gaussianPDF 0 r (y-∑ i, (z i+y/t))*F (z, y)
    have hf : Measurable f := by
      apply Measurable.mul
      · fun_prop
      · exact hF.comp (by fun_prop)
    have he := gaussianPi_lintegral_translate (-y/t) hf
    change (∫⁻ z, f (fun i => z i+(-y/t)) ∂P) = _ at he
    have hleft : (fun z : Fin m → ℝ => gaussianPDF 0 r (y-∑ j, z j)*F ((fun i => z i-y/t), y)) =
        (fun z => f (fun i => z i+(-y/t))) := by
      funext z
      have hc (i : Fin m) : z i+(-(y/t))+y/t = z i := by ring
      simp only [f, neg_div, hc, sub_eq_add_neg]

    rw [hleft, he]
    apply lintegral_congr
    intro z
    dsimp only [f]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hn : (m : ℝ)*(y/t) = (m : ℝ)*y/t := by ring
    rw [hn, ← mul_assoc]
    exact congrArg (fun u => u*F (z, y)) (gaussianBridge_density_factor_enn m hr z y)
  simp_rw [hshift]
  rw [lintegral_prod_symm _ hF.aemeasurable, gaussianReal_of_var_ne_zero 0 ht,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)
      (by fun_prop)]
  apply lintegral_congr
  intro y
  dsimp only [Pi.mul_apply]
  rw [lintegral_withDensity_eq_lintegral_mul _ (gaussianBridgeProductDensity_measurable m r)
    (g := fun z => F (z, y)) (hF.comp (by fun_prop))]
  simp only [Pi.mul_apply]
  rw [← lintegral_const_mul (f := fun z : Fin m → ℝ => gaussianBridgeProductDensity m r z * F (z, y))
    _ ((gaussianBridgeProductDensity_measurable m r).mul
    (hF.comp (show Measurable (fun z : Fin m → ℝ => (z, y)) by fun_prop)))]
  apply lintegral_congr
  intro z
  exact mul_assoc _ _ _


/-- The integral calculation identifies the actual transformed product measure. -/
theorem gaussianBridgeProductTransform_map (m : ℕ) {r : ℝ≥0} (hr : 0 < r) :
    ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (gaussianReal 0 r)).map
      (gaussianBridgeProductTransform m r) =
    ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).withDensity
      (gaussianBridgeProductDensity m r)).prod (gaussianReal 0 ((m : ℝ≥0)+r)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (gaussianBridgeProductTransform_measurable m r)]
  exact gaussianBridgeProductTransform_lintegral m hr hF

/-- The first half of a bridge has density at most sqrt(2) relative to an ordinary walk. -/
theorem gaussianBridgeProductDensity_le_sqrt_two (m : ℕ) {r : ℝ≥0}
    (hr : 0 < r) (hm : (m : ℝ) ≤ r) (z : Fin m → ℝ) :
    gaussianBridgeProductDensity m r z ≤ ENNReal.ofReal (Real.sqrt 2) := by
  have hrR : (0 : ℝ) < r := hr
  have ht : ((m : ℝ≥0)+r) ≠ 0 := by positivity
  have hp := gaussianPDFReal_pos 0 ((m : ℝ≥0)+r) 0 ht
  apply ENNReal.ofReal_le_ofReal
  have hpdf : gaussianPDFReal 0 r (-(∑ i, z i)) ≤ gaussianPDFReal 0 r 0 := by
    rw [gaussianPDFReal_zero_mean_factor]
    exact mul_le_of_le_one_right (gaussianPDFReal_nonneg _ _ _)
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))
  calc
    _ ≤ gaussianPDFReal 0 r 0 / gaussianPDFReal 0 ((m : ℝ≥0)+r) 0 :=
      div_le_div_of_nonneg_right hpdf hp.le
    _ ≤ Real.sqrt 2 := by
      simp only [gaussianPDFReal, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
        neg_zero, zero_div, Real.exp_zero, mul_one, NNReal.coe_add, NNReal.coe_natCast,
        div_inv_eq_mul]
      rw [mul_comm, ← div_eq_mul_inv]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply Real.sqrt_le_sqrt
      nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*Real.pi by positivity)]

end SwingRepair
