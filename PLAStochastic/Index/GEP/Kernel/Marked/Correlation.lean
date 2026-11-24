import PLAStochastic.Index.GEP.Kernel.BV.Translation

/-!
# Whole-line BV regularity of displacement correlations

The variation is that of the entire representative on the real line, including
all boundary jumps of a zero extension. No derivative of a density is used.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter

def kernelCorrelation (f g : ℝ → ℂ) (d : ℝ) : ℂ := ∫ u, f u * g (u+d)

theorem measurable_kernelCorrelation {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (kernelCorrelation f g) := by
  have hm : Measurable (fun p : ℝ × ℝ => f p.2 * g (p.2+p.1)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem kernelCorrelation_flip (f g : ℝ → ℂ) (d : ℝ) :
    kernelCorrelation f g d = kernelCorrelation g f (-d) := by
  unfold kernelCorrelation
  rw [← integral_add_right_eq_self (fun u => g u * f (u + -d)) d]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show u+d + -d = u by ring, mul_comm]

theorem kernelCorrelation_integrable_left {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Measurable g) {B : ℝ} (hB : ∀ u, ‖g u‖ ≤ B) (d : ℝ) :
    Integrable (fun u => f u * g (u+d)) := by
  exact hf.mul_bdd ((hg.comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => hB (u+d))

theorem kernelCorrelation_integrable_right {f g : ℝ → ℂ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B) (hg : Integrable g) (d : ℝ) :
    Integrable (fun u => f u * g (u+d)) :=
  (hg.comp_add_right d).bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hB)

theorem kernelCorrelation_norm_le_left {f g : ℝ → ℂ} (hf : Integrable f)
    {B : ℝ} (hB : ∀ u, ‖g u‖ ≤ B) (d : ℝ) :
    ‖kernelCorrelation f g d‖ ≤ B * ∫ u, ‖f u‖ := by
  unfold kernelCorrelation
  calc
    _ ≤ ∫ u, ‖f u * g (u+d)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, B * ‖f u‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hf.norm.const_mul B)
      filter_upwards [] with u
      rw [norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hB (u+d)) (norm_nonneg (f u))]
    _ = _ := integral_const_mul _ _

theorem kernelCorrelation_norm_le_right {f g : ℝ → ℂ} (hg : Integrable g)
    {B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B) (d : ℝ) :
    ‖kernelCorrelation f g d‖ ≤ B * ∫ u, ‖g u‖ := by
  rw [kernelCorrelation_flip]
  exact kernelCorrelation_norm_le_left hg hB (-d)

/-- BV of the shifted factor gives a global Lipschitz displacement modulus. -/
theorem kernelCorrelation_lip_right {f g : ℝ → ℂ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B)
    (hgv : BoundedVariationOn g univ) (hgi : Integrable g) (d e : ℝ) :
    ‖kernelCorrelation f g d - kernelCorrelation f g e‖ ≤
      B * (eVariationOn g univ).toReal * |d-e| := by
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have heq : (∫ u, ‖g (u+d) - g (u+e)‖) =
      ∫ u, ‖g (u+(d-e)) - g u‖ := by
    rw [← integral_add_right_eq_self (fun u => ‖g (u+(d-e))-g u‖) e]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [show u+e+(d-e) = u+d by ring]
  unfold kernelCorrelation
  rw [← integral_sub (kernelCorrelation_integrable_right hf hB hgi d)
    (kernelCorrelation_integrable_right hf hB hgi e)]
  calc
    _ ≤ ∫ u, ‖f u * g (u+d) - f u * g (u+e)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, B * ‖g (u+d) - g (u+e)‖ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (((hgi.comp_add_right d).sub (hgi.comp_add_right e)).norm.const_mul B)
      filter_upwards [] with u
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB u) (norm_nonneg _)
    _ = B * ∫ u, ‖g (u+(d-e)) - g u‖ := by rw [integral_const_mul, heq]
    _ ≤ B * (|d-e| * (eVariationOn g univ).toReal) :=
      mul_le_mul_of_nonneg_left (kernelTranslation_le hgv hgi (d-e)) hB0
    _ = _ := by ring

theorem kernelCorrelation_lip_left {f g : ℝ → ℂ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ u, ‖g u‖ ≤ B)
    (hfv : BoundedVariationOn f univ) (hfi : Integrable f) (d e : ℝ) :
    ‖kernelCorrelation f g d - kernelCorrelation f g e‖ ≤
      B * (eVariationOn f univ).toReal * |d-e| := by
  rw [kernelCorrelation_flip f g d, kernelCorrelation_flip f g e]
  have h := kernelCorrelation_lip_right hg hB hfv hfi (-d) (-e)
  rwa [show -d - -e = -(d-e) by ring, abs_neg] at h

theorem kernelCorrelation_affine_lip_right {f g : ℝ → ℂ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B)
    (hgv : BoundedVariationOn g univ) (hgi : Integrable g) (β a x y : ℝ) :
    ‖kernelCorrelation f g (β-a*x) - kernelCorrelation f g (β-a*y)‖ ≤
      (|a| * (eVariationOn g univ).toReal * B) * |x-y| := by
  have h := kernelCorrelation_lip_right hf hB hgv hgi (β-a*x) (β-a*y)
  rw [show (β-a*x)-(β-a*y) = -a*(x-y) by ring, abs_mul, abs_neg] at h
  exact h.trans_eq (by ring)

theorem kernelCorrelation_affine_lip_left {f g : ℝ → ℂ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ u, ‖g u‖ ≤ B)
    (hfv : BoundedVariationOn f univ) (hfi : Integrable f) (β a x y : ℝ) :
    ‖kernelCorrelation f g (β-a*x) - kernelCorrelation f g (β-a*y)‖ ≤
      (|a| * (eVariationOn f univ).toReal * B) * |x-y| := by
  have h := kernelCorrelation_lip_left hg hB hfv hfi (β-a*x) (β-a*y)
  rw [show (β-a*x)-(β-a*y) = -a*(x-y) by ring, abs_mul, abs_neg] at h
  exact h.trans_eq (by ring)

theorem kernelCorrelation_split_right {f g r h : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B)
    (hgi : Integrable g) (hr : Measurable r) {R : ℝ} (hR : ∀ u, ‖r u‖ ≤ R)
    (hsplit : ∀ u, h u = g u + r u) (d : ℝ) :
    kernelCorrelation f h d = kernelCorrelation f g d + kernelCorrelation f r d := by
  unfold kernelCorrelation
  simp_rw [hsplit, mul_add]
  exact integral_add (kernelCorrelation_integrable_right hf hB hgi d)
    (kernelCorrelation_integrable_left hfi hr hR d)

theorem kernelCorrelation_split_left {f g r h : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) {B : ℝ} (hB : ∀ u, ‖f u‖ ≤ B)
    (hgi : Integrable g) (hr : Measurable r) {R : ℝ} (hR : ∀ u, ‖r u‖ ≤ R)
    (hsplit : ∀ u, h u = g u + r u) (d : ℝ) :
    kernelCorrelation h f d = kernelCorrelation g f d + kernelCorrelation r f d := by
  rw [kernelCorrelation_flip h f d, kernelCorrelation_flip g f d,
    kernelCorrelation_flip r f d]
  exact kernelCorrelation_split_right hf hfi hB hgi hr hR hsplit (-d)

end
end PGM
