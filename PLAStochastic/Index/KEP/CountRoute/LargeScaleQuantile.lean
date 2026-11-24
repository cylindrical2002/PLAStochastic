import PLAStochastic.Index.KEP.CountRoute.WindowChoice

/-!
# The Poisson span-quantile bridge at a proved lower reference scale

The optimized Poisson lower-tail bound is evaluated at the actual minimum
reference scale. This permits a fixed small physical span quantile while
large epsilon makes the count error arbitrarily small.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval NNReal Nat

theorem kepPoissonQuantile_of_spanQuantile_large_scale
    {Q : ℝ → ℝ} {eps0 a c p0 p Bc gamma N : ℝ}
    (heps0 : kepReferenceClassicalThreshold ≤ eps0) (ha : 0 < a) (hac : a < c)
    (hgamma : 0 ≤ gamma) (hBc : 2 * c ≤ Bc)
    (hscale : ∀ eps, eps0 ≤ eps → ∀ ell, 1 ≤ ell → N ≤ kepReferenceSpan eps ell)
    (hpar : (Real.sqrt p + c / Bc) ^ 2 + Real.exp (-(poissonRateGap a c * N)) ≤ p0)
    (hS : KepPoissonSpanQuantile Q eps0 c p0 Bc gamma) :
    KepPoissonQuantile Q eps0 a p Bc gamma := by
  intro eps heps ell hell m hm u hu0 hu1
  have hthr : kepReferenceClassicalThreshold ≤ eps := heps0.trans heps
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans hthr
  have heps' : 1 / 2 ≤ eps := by linarith
  have hm4 : 4 ≤ kepReferenceSpan eps ell := kepReferenceSpan_ge_four hthr hell
  set mL := kepReferenceSpan eps ell with hmL
  have hmL0 : 0 < mL := by linarith
  have hc : 0 < c := ha.trans hac
  have hBc0 : 0 < Bc := by linarith
  have hpow : 1 ≤ eps ^ gamma := Real.one_le_rpow (by linarith) hgamma
  have hmR : Bc * eps ^ gamma * mL ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hm_ge : Bc * mL ≤ m := by
    have : Bc * mL ≤ Bc * eps ^ gamma * mL := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hmL0.le hpow) hBc0.le
    linarith
  have hmpos : (0 : ℝ) < m := by nlinarith
  set q : ℝ := c * mL / m with hq
  have hq0 : 0 < q := by positivity
  have hq_le : q ≤ c / Bc := by
    rw [hq, div_le_div_iff₀ hmpos hBc0]
    nlinarith
  have hq_half : q ≤ 1 / 2 := hq_le.trans (by rw [div_le_iff₀ hBc0]; linarith)
  have hq1 : q ≤ 1 := hq_half.trans (by norm_num)
  refine ⟨⟨q, hq0.le, hq1⟩, hq0, hq_half, ?_⟩
  set g := ⌊a * mL⌋₊ with hg
  have hS' := hS eps heps ell hell m hm u hu0 hu1 ⟨q, hq0.le, hq1⟩ rfl
  have hlow := poissonWindow_real_tailEvent_le (Q := Q) (u := u) heps' hell m ⟨q, hq0.le, hq1⟩ g
  have hrate : ((binomialPoissonRate m ⟨q, hq0.le, hq1⟩ : ℝ≥0) : ℝ) = c * mL := by
    change (m : ℝ) * q = c * mL
    rw [hq]
    field_simp
  have hcher := poissonMeasure_real_lt_le_exp_neg ha hac hrate
    (Nat.floor_le (by positivity) : (g : ℝ) ≤ a * mL)
  have hgap := poissonRateGap_pos ha hac
  have hN := hscale eps heps ell hell
  have hexp : Real.exp (-(poissonRateGap a c * mL)) ≤ Real.exp (-(poissonRateGap a c * N)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hfinal : (Real.sqrt p + q) ^ 2 ≤
      (poissonWindow m ⟨q, hq0.le, hq1⟩).real (quantEvent eps Q u ell g) := by
    calc
      (Real.sqrt p + q) ^ 2 ≤ (Real.sqrt p + c / Bc) ^ 2 := by gcongr
      _ ≤ _ := by linarith
  exact (Real.le_sqrt (by positivity) measureReal_nonneg).mpr hfinal

end

end PGM
