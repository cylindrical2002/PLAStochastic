import PLAStochastic.Index.KEP.CountRoute.WindowChoice

/-!
# Fixed constants for the original Poisson span-quantile bridge

Any fixed positive span mass admits a smaller positive rank quantile, a
polynomial cutoff constant and a minimum reference scale that pay both the
window Hellinger loss and the optimized Poisson count tail.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

theorem kepPoisson_quantile_parameters {c p0 : ℝ} (hc : 0 < c) (hp0 : 0 < p0) (R : ℝ) :
    ∃ a p Bc N : ℝ, 0 < a ∧ a < c ∧ 0 < p ∧ R ≤ Bc ∧ 2 * c ≤ Bc ∧ 0 < N ∧
      (Real.sqrt p + c / Bc) ^ 2 + Real.exp (-(poissonRateGap a c * N)) ≤ p0 := by
  let a := c / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hac : a < c := by dsimp [a]; linarith
  let p := p0 / 16
  have hp : 0 < p := by dsimp [p]; positivity
  let root := Real.sqrt p0
  have hroot : 0 < root := Real.sqrt_pos.mpr hp0
  have hrootSq : root ^ 2 = p0 := Real.sq_sqrt hp0.le
  let Bc := max R (max (2 * c + 1) (4 * c / root))
  have hBcR : R ≤ Bc := le_max_left _ _
  have hBc21 : 2 * c + 1 ≤ Bc := (le_max_left _ _).trans (le_max_right _ _)
  have hBc2 : 2 * c ≤ Bc := by linarith
  have hBc : 0 < Bc := by linarith
  have hBcRoot : 4 * c / root ≤ Bc := (le_max_right _ _).trans (le_max_right _ _)
  have hwindow : c / Bc ≤ root / 4 := by
    rw [div_le_iff₀ hroot] at hBcRoot
    rw [div_le_iff₀ hBc]
    nlinarith
  have hsqrt : Real.sqrt p = root / 4 := by
    dsimp [p, root]
    rw [Real.sqrt_div hp0.le]
    norm_num
  have hsq : (Real.sqrt p + c / Bc) ^ 2 ≤ p0 / 4 := by
    rw [hsqrt]
    have hcn : 0 ≤ c / Bc := by positivity
    nlinarith
  have hgap : 0 < poissonRateGap a c := poissonRateGap_pos ha hac
  let N := 4 / (poissonRateGap a c * p0)
  have hN : 0 < N := by dsimp [N]; positivity
  have hcost : poissonRateGap a c * N = 4 / p0 := by dsimp [N]; field_simp
  have hexp : Real.exp (-(poissonRateGap a c * N)) ≤ p0 / 4 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity : 0 < p0 / 4), inv_div,
      hcost]
    linarith [Real.add_one_le_exp (4 / p0)]
  refine ⟨a, p, Bc, N, ha, hac, hp, hBcR, hBc2, hN, ?_⟩
  linarith

end

end PGM
