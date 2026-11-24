import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic

/-! # The joint complex differential in terms of the two slice derivatives -/

noncomputable section
open Complex

theorem DifferentiableAt.hasFDerivAt_complex_prod {F : ℂ × ℂ → ℂ} {q z : ℂ}
    (hF : DifferentiableAt ℂ F (q, z)) :
    HasFDerivAt F
      (deriv (fun q' => F (q', z)) q • ContinuousLinearMap.fst ℂ ℂ ℂ +
        deriv (fun z' => F (q, z')) z • ContinuousLinearMap.snd ℂ ℂ ℂ) (q, z) := by
  let A := fderiv ℂ F (q, z)
  have hq := hF.hasFDerivAt.comp_hasDerivAt q
    ((hasDerivAt_id q).prodMk (hasDerivAt_const q z))
  have hz := hF.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z q).prodMk (hasDerivAt_id z))
  have he : A = deriv (fun q' => F (q', z)) q • ContinuousLinearMap.fst ℂ ℂ ℂ +
      deriv (fun z' => F (q, z')) z • ContinuousLinearMap.snd ℂ ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : x = x.1 • ((1, 0) : ℂ × ℂ) + x.2 • ((0, 1) : ℂ × ℂ) := by
      ext <;> simp
    calc
      A x = x.1 * A (1, 0) + x.2 * A (0, 1) := by
        conv_lhs => rw [hx]
        rw [map_add, map_smul, map_smul]
        rfl
      _ = _ := by simp [A, ← hq.deriv, ← hz.deriv, mul_comm, Function.comp_def]
  exact he ▸ hF.hasFDerivAt
