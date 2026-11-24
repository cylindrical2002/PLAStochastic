import PLAStochastic.Index.CEPS.Scaled.RootJetModel
import Mathlib.Analysis.Complex.SqrtDeriv

/-! # Genuine joint scale-frequency analyticity of finite cumulant root models -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsCumulantRootBase_radicand_mem_slitPlane (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) :
    z + (lam : ℂ) ^ 2 / (2 * (p (cepsJetCode (.inl 0)) : ℂ)) ∈ slitPlane := by
  have he : (lam : ℂ) ^ 2 / (2 * (p (cepsJetCode (.inl 0)) : ℂ)) =
      ((lam ^ 2 / (2 * p (cepsJetCode (.inl 0))) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, mem_slitPlane_iff]
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  by_cases hlam : lam = 0
  · have hz0 : z ≠ 0 := hne.resolve_left (not_not.mpr hlam)
    simp only [hlam, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, add_zero]
    by_cases hi : z.im = 0
    · left
      have hr : z.re ≠ 0 := fun h => hz0 (Complex.ext h hi)
      exact lt_of_le_of_ne hz hr.symm
    · exact Or.inr hi
  · exact Or.inl (add_pos_of_nonneg_of_pos hz (div_pos (sq_pos_of_ne_zero hlam) (by positivity)))

theorem cepsCumulantRootBase_frequency_analyticAt (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) :
    AnalyticAt ℂ (fun z => cepsCumulantRootBase p lam z sign) z := by
  have hrad := cepsCumulantRootBase_radicand_mem_slitPlane p hp lam hz hne
  have hsqrt : AnalyticAt ℂ sqrt (z + (lam : ℂ) ^ 2 /
      (2 * (p (cepsJetCode (.inl 0)) : ℂ))) :=
    differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hrad)
  have hcurve : AnalyticAt ℂ (fun z : ℂ => z + (lam : ℂ) ^ 2 /
      (2 * (p (cepsJetCode (.inl 0)) : ℂ))) z := by fun_prop
  have hs := hsqrt.comp (f := fun ζ : ℂ => ζ + (lam : ℂ) ^ 2 /
    (2 * (p (cepsJetCode (.inl 0)) : ℂ))) hcurve
  exact analyticAt_const.add (analyticAt_const.mul hs)

theorem cepsCumulantRootGap_ne_zero (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) (hsign : sign ≠ 0) : cepsCumulantRootGap p lam z sign ≠ 0 := by
  have hv : (p (cepsJetCode (.inl 0)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hrad := cepsCumulantRootBase_radicand_mem_slitPlane p hp lam hz hne
  have hrad0 : z + (lam : ℂ) ^ 2 / (2 * (p (cepsJetCode (.inl 0)) : ℂ)) ≠ 0 := by
    intro he; rw [he] at hrad; exact zero_notMem_slitPlane hrad
  have he : cepsCumulantRootGap p lam z sign = (p (cepsJetCode (.inl 0)) : ℂ) * sign *
      sqrt (2 / (p (cepsJetCode (.inl 0)) : ℂ)) *
        sqrt (z + (lam : ℂ) ^ 2 / (2 * (p (cepsJetCode (.inl 0)) : ℂ))) := by
    unfold cepsCumulantRootGap cepsCumulantRootBase
    field_simp [hv]
    ring
  rw [he]
  have hS0 (a : ℂ) (ha : a ≠ 0) : sqrt a ≠ 0 := by
    intro hh
    have he := sqrt_sq_eq a
    rw [hh, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact ha he.symm
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hv hsign)
    (hS0 _ (div_ne_zero (by norm_num) hv))) (hS0 _ hrad0)

theorem cepsCumulantRootModel_joint_frequency_analyticAt (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z sign : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) (hsign : sign ≠ 0) (b : ℂ) (k : ℕ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCumulantRootModel p N lam x.2 sign k x.1) (b, z) := by
  have hBase := cepsCumulantRootBase_frequency_analyticAt p hp lam hz hne (sign := sign)
  have hBaseJoint : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCumulantRootBase p lam x.2 sign) (b, z) :=
    hBase.comp (x := (b, z)) (f := fun x : ℂ × ℂ => x.2) analyticAt_snd
  have hGap : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCumulantRootGap p lam x.2 sign) (b, z) :=
    analyticAt_const.add (analyticAt_const.mul hBaseJoint)
  have hGap0 := cepsCumulantRootGap_ne_zero p hp lam hz hne hsign
  induction k with
  | zero => exact hBaseJoint
  | succ k ih =>
    have hProd : AnalyticAt ℂ (fun x : ℂ × ℂ =>
        x.1 * cepsCumulantRootModel p N lam x.2 sign k x.1) (b, z) := analyticAt_fst.mul ih
    have hP := (cepsCgfJetPolynomial_differentiable p N).analyticAt
      (b * cepsCumulantRootModel p N lam z sign k b)
    have hPc := hP.comp (x := (b, z)) (f := fun x : ℂ × ℂ =>
      x.1 * cepsCumulantRootModel p N lam x.2 sign k x.1) hProd
    have hFst : AnalyticAt ℂ (fun x : ℂ × ℂ => x.1) (b, z) := analyticAt_fst
    have hSnd : AnalyticAt ℂ (fun x : ℂ × ℂ => x.2) (b, z) := analyticAt_snd
    exact ih.sub (((((ih.pow 2).mul hPc).add (analyticAt_const.mul ih)).sub
      (hSnd.mul (analyticAt_const.add (hFst.mul analyticAt_const)))).div hGap hGap0)

end PGM
