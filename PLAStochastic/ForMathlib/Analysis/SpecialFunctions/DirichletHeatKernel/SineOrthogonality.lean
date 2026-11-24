import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.DirichletHeatKernel.SineSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Orthogonality and analytic-kernel sine moments on the killed interval -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem integral_cos_int_frequency {r : ℝ} (hr : 0 < r) (k : ℤ) :
    (∫ x in (0 : ℝ)..r, Real.cos ((k : ℝ) * (Real.pi / r) * x)) =
      if k = 0 then r else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hf : (k : ℝ) * (Real.pi / r) ≠ 0 := by positivity
    have hd (x : ℝ) : HasDerivAt
        (fun x : ℝ => Real.sin ((k : ℝ) * (Real.pi / r) * x) / ((k : ℝ) * (Real.pi / r)))
        (Real.cos ((k : ℝ) * (Real.pi / r) * x)) x := by
      convert! (((hasDerivAt_id x).const_mul ((k : ℝ) * (Real.pi / r))).sin).div_const
        ((k : ℝ) * (Real.pi / r)) using 1
      simp only [mul_one, id_eq]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * (Real.pi / r) * x))).intervalIntegrable 0 r)]
    have he : (k : ℝ) * (Real.pi / r) * r = (k : ℝ) * Real.pi := by field_simp
    rw [he, Real.sin_int_mul_pi]
    simp [hk]

/-- Exact interval sine orthogonality, with index zero denoting the first Dirichlet mode. -/
theorem integral_heatSine_mul_heatSine {r : ℝ} (hr : 0 < r) (n m : ℕ) :
    (∫ z in (0 : ℝ)..r, Real.sin (heatFrequency r n * z) * Real.sin (heatFrequency r m * z)) =
      if n = m then r / 2 else 0 := by
  have he (z : ℝ) : Real.sin (heatFrequency r n * z) * Real.sin (heatFrequency r m * z) =
      (1 / 2 : ℝ) * (Real.cos ((heatFrequency r n - heatFrequency r m) * z) -
        Real.cos ((heatFrequency r n + heatFrequency r m) * z)) := by
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun z : ℝ => Real.cos ((heatFrequency r n - heatFrequency r m) * z))).intervalIntegrable 0 r)
    ((by fun_prop : Continuous (fun z : ℝ => Real.cos ((heatFrequency r n + heatFrequency r m) * z))).intervalIntegrable 0 r)]
  have hd : heatFrequency r n - heatFrequency r m = ((n : ℤ) - m : ℤ) * (Real.pi / r) := by
    unfold heatFrequency
    push_cast
    ring
  have hs : heatFrequency r n + heatFrequency r m = ((n : ℤ) + m + 2 : ℤ) * (Real.pi / r) := by
    unfold heatFrequency
    push_cast
    ring
  rw [hd, hs, integral_cos_int_frequency hr, integral_cos_int_frequency hr]
  have hdiff : ((n : ℤ) - m = 0) ↔ n = m := by omega
  have hsum : (n : ℤ) + m + 2 ≠ 0 := by omega
  simp only [hdiff, if_neg hsum, sub_zero]
  split_ifs <;> ring

theorem integral_Icc_heatSine_mul_heatSine {r : ℝ} (hr : 0 < r) (n m : ℕ) :
    (∫ z in Icc (0 : ℝ) r, Real.sin (heatFrequency r n * z) * Real.sin (heatFrequency r m * z)) =
      if n = m then r / 2 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
  exact integral_heatSine_mul_heatSine hr n m

/-- The analytic kernel has exactly the Dirichlet sine moments; the sum-integral interchange
uses the proved uniform summable bound. -/
theorem integral_dirichletHeatKernel_mul_sine {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (x : ℝ) (m : ℕ) :
    (∫ z in Icc (0 : ℝ) r, dirichletHeatKernel r t x z * Real.sin (heatFrequency r m * z)) =
      Real.sin (heatFrequency r m * x) * Real.exp (-(heatFrequency r m ^ 2) * t / 2) := by
  let F : ℕ → ℝ → ℝ := fun n z => heatSpatialMode r 0 0 n t x z * Real.sin (heatFrequency r m * z)
  have hi (n : ℕ) : IntegrableOn (F n) (Icc 0 r) := by
    apply Continuous.integrableOn_Icc
    dsimp only [F, heatSpatialMode]
    fun_prop
  have hb (n : ℕ) (z : ℝ) : ‖F n z‖ ≤ heatSpatialBound r t 0 0 n := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ ‖heatSpatialMode r 0 0 n t x z‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact heatSpatialMode_bound hr ht.le le_rfl 0 0 n x z
  have hbn (n : ℕ) : (∫ z in Icc (0 : ℝ) r, ‖F n z‖) ≤ r * heatSpatialBound r t 0 0 n := by
    calc
      _ ≤ ∫ _z in Icc (0 : ℝ) r, heatSpatialBound r t 0 0 n :=
        integral_mono_ae (hi n).norm (integrable_const _) (Eventually.of_forall (hb n))
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_restrict_apply_univ, smul_eq_mul, Real.volume_real_Icc_of_le hr.le, sub_zero]
  have hs : Summable (fun n => ∫ z in Icc (0 : ℝ) r, ‖F n z‖) :=
    ((summable_heatSpatialBound hr ht 0 0).mul_left r).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbn
  have heq (z : ℝ) : dirichletHeatKernel r t x z * Real.sin (heatFrequency r m * z) =
      ∑' n, F n z := by
    unfold dirichletHeatKernel heatSpatialSeries
    exact (tsum_mul_right).symm
  simp only [heq]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  have hint (n : ℕ) : (∫ z in Icc (0 : ℝ) r, F n z) =
      (2 / r * Real.sin (heatFrequency r n * x) * Real.exp (-(heatFrequency r n ^ 2) * t / 2)) *
        (if n = m then r / 2 else 0) := by
    have hf (z : ℝ) : F n z =
        (2 / r * Real.sin (heatFrequency r n * x) * Real.exp (-(heatFrequency r n ^ 2) * t / 2)) *
          (Real.sin (heatFrequency r n * z) * Real.sin (heatFrequency r m * z)) := by
      dsimp only [F, heatSpatialMode]
      norm_num
      ring
    simp only [hf]
    rw [integral_const_mul, integral_Icc_heatSine_mul_heatSine hr n m]
  simp only [hint]
  rw [tsum_eq_single m (fun n hnm => by rw [if_neg hnm, mul_zero]), if_pos rfl]
  field_simp

end BrownianAffine
