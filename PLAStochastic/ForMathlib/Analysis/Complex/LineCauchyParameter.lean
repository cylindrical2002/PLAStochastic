import PLAStochastic.ForMathlib.Analysis.Complex.LineCauchy

/-! # Real parameter differentiation of the spatial Cauchy derivative -/

noncomputable section
open Complex MeasureTheory Filter Topology Metric Set
namespace PGM

/-- One additional Cauchy denominator preserves a dominated real parameter derivative. -/
theorem hasDerivAt_deriv_lineCauchy_parameter
    {φ φ' : ℝ → ℝ → ℂ} {x c δ : ℝ} {ζ : ℂ} (hδ : 0 < δ) (hζ : ζ.re < c)
    (hI : ∀ t ∈ ball x δ, Integrable (fun y => φ t y / ((c : ℂ) + y * I - ζ)))
    (hD : ∀ t ∈ ball x δ, ∀ y, HasDerivAt (fun t => φ t y) (φ' t y) t)
    (hM : AEStronglyMeasurable (fun y => φ' x y / ((c : ℂ) + y * I - ζ)) volume)
    {bound : ℝ → ℝ} (hbound : Integrable bound)
    (hB : ∀ y t, t ∈ ball x δ → ‖φ' t y / ((c : ℂ) + y * I - ζ)‖ ≤ bound y) :
    HasDerivAt (fun t => deriv (lineCauchy (φ t) c) ζ)
      (∫ y, φ' x y / ((c : ℂ) + y * I - ζ) ^ 2) x := by
  let A := c - ζ.re
  have hA : 0 < A := by dsimp [A]; linarith
  have hne : ∀ y : ℝ, (c : ℂ) + y * I - ζ ≠ 0 := vline_sub_ne_zero hζ.ne
  have hden : ∀ y : ℝ, A ≤ ‖(c : ℂ) + y * I - ζ‖ := by
    intro y
    simpa only [A, abs_of_pos hA] using abs_sub_re_le_norm_vline c y ζ
  have hinv : ∀ y : ℝ, ‖((c : ℂ) + y * I - ζ)⁻¹‖ ≤ A⁻¹ := by
    intro y
    rw [norm_inv]
    exact inv_anti₀ hA (hden y)
  have hInvM : AEStronglyMeasurable (fun y : ℝ => ((c : ℂ) + y * I - ζ)⁻¹) volume := by
    fun_prop
  have hEq : ∀ (ψ : ℝ → ℂ) y, ψ y / ((c : ℂ) + y * I - ζ) ^ 2 =
      (ψ y / ((c : ℂ) + y * I - ζ)) * ((c : ℂ) + y * I - ζ)⁻¹ := by
    intro ψ y
    simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
    ring
  have hI2 : ∀ t ∈ ball x δ, Integrable (fun y => φ t y / ((c : ℂ) + y * I - ζ) ^ 2) := by
    intro t ht
    exact ((hI t ht).mul_bdd hInvM (Eventually.of_forall hinv)).congr
      (Eventually.of_forall fun y => (hEq (φ t) y).symm)
  have hM2 : AEStronglyMeasurable (fun y => φ' x y / ((c : ℂ) + y * I - ζ) ^ 2) volume :=
    (hM.mul hInvM).congr (Eventually.of_forall fun y => (hEq (φ' x) y).symm)
  have hB2 : ∀ y t, t ∈ ball x δ →
      ‖φ' t y / ((c : ℂ) + y * I - ζ) ^ 2‖ ≤ bound y * A⁻¹ := by
    intro y t ht
    rw [hEq, norm_mul]
    exact mul_le_mul (hB y t ht) (hinv y) (norm_nonneg _)
      ((norm_nonneg _).trans (hB y t ht))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t y => φ t y / ((c : ℂ) + y * I - ζ) ^ 2)
    (F' := fun t y => φ' t y / ((c : ℂ) + y * I - ζ) ^ 2)
    (bound := fun y => bound y * A⁻¹) (x₀ := x) (s := ball x δ) (ball_mem_nhds x hδ)
    (eventually_of_mem (ball_mem_nhds x hδ) fun t ht => (hI2 t ht).aestronglyMeasurable)
    (hI2 x (mem_ball_self hδ)) hM2
    (Eventually.of_forall hB2) (hbound.mul_const _)
    (Eventually.of_forall fun y t ht => (hD t ht y).div_const _)
  have he : (fun t => deriv (lineCauchy (φ t) c) ζ) =ᶠ[𝓝 x]
      (fun t => ∫ y, φ t y / ((c : ℂ) + y * I - ζ) ^ 2) := by
    filter_upwards [ball_mem_nhds x hδ] with t ht
    exact (hasDerivAt_lineCauchy hζ.ne (hI t ht) hζ.ne).deriv
  exact hmain.2.congr_of_eventuallyEq he

end PGM
