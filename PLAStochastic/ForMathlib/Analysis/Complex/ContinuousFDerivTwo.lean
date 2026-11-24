import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Continuous Frechet derivatives for holomorphic scalar functions on C squared -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem fderiv_eq_complex_partials {F : ℂ × ℂ → ℂ} {x : ℂ × ℂ}
    (hF : DifferentiableAt ℂ F x) :
    fderiv ℂ F x =
      deriv (fun z => F (z, x.2)) x.1 • ContinuousLinearMap.fst ℂ ℂ ℂ +
        deriv (fun z => F (x.1, z)) x.2 • ContinuousLinearMap.snd ℂ ℂ ℂ := by
  have h₁ := (hF.hasFDerivAt.comp x.1
    ((hasFDerivAt_id (𝕜 := ℂ) x.1).prodMk (hasFDerivAt_const (𝕜 := ℂ) x.2 x.1))).hasDerivAt.deriv
  have h₂ := (hF.hasFDerivAt.comp x.2
    ((hasFDerivAt_const (𝕜 := ℂ) x.1 x.2).prodMk (hasFDerivAt_id (𝕜 := ℂ) x.2))).hasDerivAt.deriv
  have hp : deriv (fun z => F (z, x.2)) x.1 = fderiv ℂ F x (1, 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
      id_eq, ContinuousLinearMap.smulRight_apply, one_smul] using h₁
  have hq : deriv (fun z => F (x.1, z)) x.2 = fderiv ℂ F x (0, 1) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
      id_eq, ContinuousLinearMap.smulRight_apply, one_smul] using h₂
  apply ContinuousLinearMap.ext
  intro y
  have hy : y = y.1 • ((1, 0) : ℂ × ℂ) + y.2 • ((0, 1) : ℂ × ℂ) := by ext <;> simp
  rw [hp, hq]
  change (fderiv ℂ F x) y = (fderiv ℂ F x) (1, 0) * y.1 + (fderiv ℂ F x) (0, 1) * y.2
  conv_lhs => rw [hy, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

theorem continuousOn_fderiv_of_complex_differentiableOn {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) :
    ContinuousOn (fderiv ℂ F) U := by
  have hp := (differentiableOn_deriv_fst hU hF).continuousOn
  have hswap : DifferentiableOn ℂ (fun x : ℂ × ℂ => F (x.2, x.1))
      ((fun x : ℂ × ℂ => (x.2, x.1)) ⁻¹' U) :=
    hF.comp (by fun_prop) (fun _ hx => hx)
  have hq' := (differentiableOn_deriv_fst (hU.preimage (by fun_prop)) hswap).continuousOn
  have hq : ContinuousOn (fun x : ℂ × ℂ => deriv (fun z => F (x.1, z)) x.2) U :=
    hq'.comp (f := fun x : ℂ × ℂ => (x.2, x.1)) (by fun_prop) (fun _ hx => hx)
  apply ((hp.smul continuousOn_const).add (hq.smul continuousOn_const)).congr
  intro x hx
  exact fderiv_eq_complex_partials ((hF x hx).differentiableAt (hU.mem_nhds hx))

end PGM
