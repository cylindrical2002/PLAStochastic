import PLAStochastic.Index.CEPS.Total.LevelClass
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# WP10: pointwise bounds from the weighted Sobolev size

A `C¹` function with integrable value and derivative is bounded by `∫ |g'|`
(`abs_le_integral_abs_deriv`). Hence every derivative of order `k < m` of a function in the
weighted Sobolev class of order `m` and weight `η ≥ 0` is bounded by its Sobolev size
(`CepsSobolevClass.abs_iteratedDeriv_le`); this pays pointwise density-derivative hypotheses
(such as `|f'| ≤ K_f`) from the level data.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace PGM

theorem abs_le_integral_abs_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hgi : Integrable g)
    (hg'i : Integrable (deriv g)) (x : ℝ) : |g x| ≤ ∫ y, |deriv g y| := by
  have hd : ∀ y, HasDerivAt g (deriv g y) y := fun y =>
    (hg.differentiable (by norm_num) y).hasDerivAt
  have hlim : Tendsto g atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := x) (fun y _ => hd y)
      hg'i.integrableOn hgi.integrableOn
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' (a := x) (fun y _ => hd y)
    hg'i.integrableOn hlim
  have h1 : |g x| = |∫ y in Ioi x, deriv g y| := by rw [hI, zero_sub, abs_neg]
  rw [h1]
  calc |∫ y in Ioi x, deriv g y| ≤ ∫ y in Ioi x, |deriv g y| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (deriv g)
    _ ≤ ∫ y, |deriv g y| :=
        setIntegral_le_integral hg'i.abs (ae_of_all _ fun y => abs_nonneg _)

/-- **Pointwise bound** of the derivatives of order `< m` by the weighted Sobolev size. -/
theorem CepsSobolevClass.abs_iteratedDeriv_le {m : ℕ} {η : ℝ} {f : ℝ → ℝ}
    (hf : CepsSobolevClass m η f) (hη : 0 ≤ η) {k : ℕ} (hk : k + 1 ≤ m) (x : ℝ) :
    |iteratedDeriv k f x| ≤ cepsSobolev m η f := by
  have hC : ContDiff ℝ 1 (iteratedDeriv k f) := by
    have h2 : ContDiff ℝ ((1 + k : ℕ) : WithTop ℕ∞) f :=
      hf.contDiff.of_le (by exact_mod_cast (show 1 + k ≤ m by omega))
    rw [iteratedDeriv_eq_iterate]
    exact_mod_cast h2.iterate_deriv' 1 k
  have hder : deriv (iteratedDeriv k f) = iteratedDeriv (k + 1) f := by
    rw [iteratedDeriv_succ]
  have h1 := abs_le_integral_abs_deriv hC (hf.integrable_iteratedDeriv hη (by omega))
    (by rw [hder]; exact hf.integrable_iteratedDeriv hη hk) x
  rw [hder] at h1
  refine h1.trans ?_
  calc ∫ y, |iteratedDeriv (k + 1) f y| ≤ ∫ y, Real.exp (η * |y|) * |iteratedDeriv (k + 1) f y| :=
        integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (hf.integrable_abs hk)
          (ae_of_all _ fun y => le_mul_of_one_le_left (abs_nonneg _)
            (Real.one_le_exp (by positivity)))
    _ ≤ cepsSobolev m η f := by
        unfold cepsSobolev
        exact Finset.single_le_sum (f := fun r => ∫ x, Real.exp (η * |x|) * |iteratedDeriv r f x|)
          (fun r _ => integral_nonneg fun _ => by positivity)
          (Finset.mem_range.mpr (by omega))

/-- A level-`n` density is `C¹` with derivative bounded by `2^n`; in particular it is
`2^n`-Lipschitz. -/
theorem CepsLevelDensity.lipschitz {n : ℕ} {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    (h : CepsLevelDensity n ν f) :
    Differentiable ℝ f ∧ (∀ x, |deriv f x| ≤ cepsLevelScale n) ∧
      LipschitzWith (Real.toNNReal (cepsLevelScale n)) f := by
  obtain ⟨-, -, -, -, -, -, -, -, hS, hSM⟩ := h
  set fW := fun x => f (1 - x) with hfW
  have hf : f = fun x => fW (1 - x) := by funext x; simp [fW]
  have hC : ContDiff ℝ 1 fW := hS.contDiff.of_le (by norm_num [cepsLevelOrder])
  have hd : Differentiable ℝ f := by
    rw [hf]; exact (hC.differentiable (by norm_num)).comp (by fun_prop)
  have hderiv : ∀ x, deriv f x = -deriv fW (1 - x) := by
    intro x
    rw [hf]
    have h1 : HasDerivAt (fun y => fW (1 - y)) (deriv fW (1 - x) * (-1)) x :=
      ((hC.differentiable (by norm_num) (1 - x)).hasDerivAt).comp x
        (by simpa using (hasDerivAt_id x).const_sub 1)
    rw [h1.deriv]; ring
  have hbound : ∀ x, |deriv f x| ≤ cepsLevelScale n := by
    intro x
    rw [hderiv, abs_neg]
    have := hS.abs_iteratedDeriv_le (cepsLevelRate_pos n).le (k := 1)
      (by norm_num [cepsLevelOrder]) (1 - x)
    rw [iteratedDeriv_one] at this
    exact this.trans hSM
  refine ⟨hd, hbound, lipschitzWith_of_nnnorm_deriv_le hd fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _
    (cepsLevelScale_pos n).le]
  exact hbound x

end PGM
