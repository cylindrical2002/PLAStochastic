import PLAStochastic.ForMathlib.Analysis.Complex.MixedPartialDeriv

/-! # Joint holomorphy of the complete entrance-square time-operator pair -/

noncomputable section
open Complex Set
namespace PGM

/-- The actual frequency derivative in the complete pair remains jointly holomorphic.
The factors and the width are evaluated on the same open parameter domain. -/
theorem differentiableOn_complete_time_pair {A U : ℂ → ℂ → ℂ} {S : Set (ℂ × ℂ)}
    (hS : IsOpen S) (lam : ℂ)
    (hA : DifferentiableOn ℂ (fun x : ℂ × ℂ => A x.1 x.2) S)
    (hU : DifferentiableOn ℂ (fun x : ℂ × ℂ => U x.1 x.2) S)
    (hwidth : ∀ x ∈ S, 1 + x.1 * lam ≠ 0) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      exp ((x.1 * x.2) * (1 + x.1 * lam)) * (A x.1 x.2) ^ 2 *
        (-(1 / (1 + x.1 * lam)) * deriv (U x.1) x.2 - x.1 * U x.1 x.2)) S := by
  have hV := differentiableOn_deriv_snd hS hU
  have hw : DifferentiableOn ℂ (fun x : ℂ × ℂ => 1 + x.1 * lam) S := by fun_prop
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      exp ((x.1 * x.2) * (1 + x.1 * lam))) S := by fun_prop
  have h := (hE.mul (hA.pow 2)).mul
    (((hw.inv hwidth).neg.mul hV).sub (differentiableOn_fst.mul hU))
  simpa only [one_div, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.inv_apply] using! h

end PGM
