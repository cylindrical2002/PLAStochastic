import PLAStochastic.Index.CEPS.Scaled.ComplexJetKernelLift

/-! # Root charts for all complex positive-real-part variance inputs -/

noncomputable section
open Complex Set
namespace PGM

theorem cepsComplexCumulantRootGap_eq (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ)
    (hv : p (cepsJetCode (.inl 0)) ≠ 0) :
    cepsComplexCumulantRootGap p lam z sign = p (cepsJetCode (.inl 0)) * sign *
      sqrt (2 / p (cepsJetCode (.inl 0))) *
        sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))) := by
  unfold cepsComplexCumulantRootGap cepsComplexCumulantRootBase
  field_simp [hv]
  ring

/-- The right frequency half-plane is inside the actual root chart for every complex
variance with positive real part, away from the single joint origin. -/
theorem cepsComplexJetRootChart_right (p : ℕ → ℂ)
    (hp : 0 < (p (cepsJetCode (.inl 0))).re) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) : CepsComplexJetRootChart p lam z := by
  let v := p (cepsJetCode (.inl 0))
  have hv : v ≠ 0 := by
    intro h
    have hzero : (p (cepsJetCode (.inl 0))).re = 0 := congrArg Complex.re h
    exact hp.ne' hzero
  have hi : 0 < v⁻¹.re := by
    rw [inv_re]
    exact div_pos hp (normSq_pos.mpr hv)
  have hr : 2 / v ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    rw [div_eq_mul_inv, mul_re]
    norm_num
    simpa only [inv_re] using hi
  have hrad : z + (lam : ℂ) ^ 2 / (2 * v) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_cases hl : lam = 0
    · have hz0 : z ≠ 0 := hne.resolve_left (not_not.mpr hl)
      simp only [hl, ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, add_zero]
      by_cases hzi : z.im = 0
      · left
        have hzr : z.re ≠ 0 := fun h => hz0 (Complex.ext h hzi)
        exact lt_of_le_of_ne hz hzr.symm
      · exact Or.inr hzi
    · left
      have he : (lam : ℂ) ^ 2 / (2 * v) = ((lam ^ 2 / 2 : ℝ) : ℂ) * v⁻¹ := by
        push_cast
        field_simp [hv]
      rw [add_re, he, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      exact add_pos_of_nonneg_of_pos hz (mul_pos (div_pos (sq_pos_of_ne_zero hl) (by norm_num)) hi)
  have hs (w : ℂ) (hw : w ≠ 0) : sqrt w ≠ 0 := by
    intro h
    have he := sqrt_sq_eq w
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact hw he.symm
  have hrad0 : z + (lam : ℂ) ^ 2 / (2 * v) ≠ 0 :=
    fun h => zero_notMem_slitPlane (h ▸ hrad)
  have hg (sign : ℂ) (hsg : sign ≠ 0) : cepsComplexCumulantRootGap p lam z sign ≠ 0 := by
    rw [cepsComplexCumulantRootGap_eq p lam z sign hv]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hv hsg)
      (hs _ (div_ne_zero (by norm_num) hv))) (hs _ hrad0)
  exact ⟨hv, hr, hrad, hg 1 (by norm_num), hg (-1) (by norm_num)⟩

end PGM
