import PLAStochastic.Index.CEPS.Scaled.KernelZeroModel

/-! # The finite-kernel zero-scale denominator is nonzero without a law realization -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

/-- Exponential divided differences cannot vanish between nodes with different real parts. -/
theorem dslope_exp_neg_ne_zero {a b : ℂ} (hab : a = b ∨ a.re ≠ b.re) :
    dslope (fun x : ℂ => exp (-x)) a b ≠ 0 := by
  rcases hab with rfl | hab
  · rw [dslope_same]
    have hd : HasDerivAt (fun x : ℂ => exp (-x)) (-exp (-a)) a := by
      simpa only [mul_neg, mul_one, Pi.neg_apply, id_eq] using! (hasDerivAt_id a).neg.cexp
    rw [hd.deriv]
    exact neg_ne_zero.mpr (exp_ne_zero _)
  · have hba : b ≠ a := fun h => hab (congrArg Complex.re h.symm)
    rw [dslope_of_ne _ hba, slope_def_field]
    apply div_ne_zero _ (sub_ne_zero.mpr hba)
    apply sub_ne_zero.mpr
    intro he
    have hn := congrArg norm he
    rw [norm_exp, norm_exp, neg_re, neg_re] at hn
    exact hab (neg_injective (Real.exp_injective hn).symm)

/-- The two quadratic roots have strictly separated real parts throughout the right half-plane,
except at their single common zero. -/
theorem cepsCumulantRootBase_re_separated (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    (cepsCumulantRootBase p lam z (-1)).re ≠ (cepsCumulantRootBase p lam z 1).re := by
  let v : ℝ := p (cepsJetCode (.inl 0))
  let w : ℂ := z + (lam : ℂ) ^ 2 / (2 * (v : ℂ))
  have hw : w ∈ slitPlane := cepsCumulantRootBase_radicand_mem_slitPlane p hp lam hz hne
  have hw0 : w ≠ 0 := fun h => zero_notMem_slitPlane (h ▸ hw)
  have hwre : 0 ≤ w.re := by
    have he : (lam : ℂ) ^ 2 / (2 * (v : ℂ)) = ((lam ^ 2 / (2 * v) : ℝ) : ℂ) := by
      push_cast; rfl
    dsimp [w]
    rw [he, ofReal_re]
    exact add_nonneg hz (div_nonneg (sq_nonneg _) (by dsimp [v]; positivity))
  have hs : 0 < (sqrt w).re := by
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_pos.mpr (by linarith [norm_pos_iff.mpr hw0])
  have hv : 0 < v := hp
  have hcast : 2 / (v : ℂ) = ((2 / v : ℝ) : ℂ) := by push_cast; rfl
  have hsreal : sqrt (2 / (v : ℂ)) = ((Real.sqrt (2 / v) : ℝ) : ℂ) := by
    rw [hcast]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast (div_pos (by norm_num : (0 : ℝ) < 2) hv).le)
  have hprod : 0 < (sqrt (2 / (v : ℂ)) * sqrt w).re := by
    rw [hsreal, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Real.sqrt_pos.mpr (div_pos (by norm_num) hv)) hs
  unfold cepsCumulantRootBase
  change (-(lam : ℂ) / (v : ℂ) + (-1) * sqrt (2 / (v : ℂ)) * sqrt w).re ≠
    (-(lam : ℂ) / (v : ℂ) + 1 * sqrt (2 / (v : ℂ)) * sqrt w).re
  simp only [neg_mul, one_mul, add_re, neg_re]
  linarith

/-- Arbitrary positive-variance finite jet vectors already pay the genuine zero-scale
bridge and entrance denominator, including the joint origin. -/
theorem cepsKernelDenominatorJetModel_zero_ne (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    cepsKernelDenominatorJetModel p N lam z 0 ≠ 0 := by
  let c : ℂ := (p (cepsJetCode (.inl 0)) : ℂ) / 2 *
    exp (-2 * (p (cepsJetCode (.inr (0, 0, 0))) : ℂ))
  have hc : c ≠ 0 := mul_ne_zero (div_ne_zero (by exact_mod_cast hp.ne') (by norm_num))
    (exp_ne_zero _)
  have hG : cepsKernelGJetModel p N lam z 0 = fun ξ : ℂ => c * exp (-ξ) := by
    funext ξ
    exact cepsKernelGJetModel_zero p N lam z ξ
  have hdiff : Differentiable ℂ (fun ξ : ℂ => exp (-ξ)) := by fun_prop
  rw [cepsKernelDenominatorJetModel, hG,
    dslope_const_mul_of_differentiable c _ _ (hdiff _),
    cepsCumulantRootModel_zero p hp.ne' N lam z (-1) (by norm_num) N,
    cepsCumulantRootModel_zero p hp.ne' N lam z 1 (by norm_num) N]
  apply mul_ne_zero hc
  apply dslope_exp_neg_ne_zero
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · exact Or.inr (cepsCumulantRootBase_re_separated p hp lam hz hne)
  · push Not at hne
    exact Or.inl (by simp [cepsCumulantRootBase, hne.1, hne.2])

/-- The negative zero-scale root is nonzero on the positive-drift half-line for any frequency. -/
theorem cepsCumulantRootBase_minus_ne_zero (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    cepsCumulantRootBase p lam z (-1) ≠ 0 := by
  let v : ℝ := p (cepsJetCode (.inl 0))
  let w : ℂ := z + (lam : ℂ) ^ 2 / (2 * (v : ℂ))
  have hv : 0 < v := hp
  have hcast : 2 / (v : ℂ) = ((2 / v : ℝ) : ℂ) := by push_cast; rfl
  have hsreal : sqrt (2 / (v : ℂ)) = ((Real.sqrt (2 / v) : ℝ) : ℂ) := by
    rw [hcast]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast (div_pos (by norm_num : (0 : ℝ) < 2) hv).le)
  have hs : 0 ≤ (sqrt w).re := by
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hprod : 0 ≤ (sqrt (2 / (v : ℂ)) * sqrt w).re := by
    rw [hsreal, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hs
  have hneg : (cepsCumulantRootBase p lam z (-1)).re < 0 := by
    unfold cepsCumulantRootBase
    change (-(lam : ℂ) / (v : ℂ) + (-1) * sqrt (2 / (v : ℂ)) * sqrt w).re < 0
    have hdiv : -(lam : ℂ) / (v : ℂ) = ((-lam / v : ℝ) : ℂ) := by push_cast; rfl
    rw [hdiv]
    simp only [neg_mul, one_mul, add_re, neg_re, ofReal_re, neg_div]
    linarith [div_pos hlam hv]
  exact fun h => by rw [h, zero_re] at hneg; exact lt_irrefl _ hneg

end PGM
