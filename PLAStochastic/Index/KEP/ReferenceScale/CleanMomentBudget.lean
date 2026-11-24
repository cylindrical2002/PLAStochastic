import PLAStochastic.Index.KEP.ReferenceScale.LawOrbit
import PLAStochastic.Index.GEP.Kernel.Tilt.Rate

/-!
# Uniform two-sided moment bounds for the unchanged clean marginal

The actual regular reference class already has the proved small-tilt centered
cumulant bound. Exponentiation gives a common quadratic moment bound for both
signs of the Chernoff parameter, including the exponential base layer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepReference_uniform_two_sided_mgf :
    ∃ C t0 eps0 : ℝ, 0 < C ∧ 0 < t0 ∧ ∀ eps, eps0 ≤ eps → ∀ j : ℕ,
      ∀ t : ℝ, |t| ≤ t0 →
        Integrable (fun x => Real.exp (t * x)) (kepReferenceLaw eps j : Measure ℝ) ∧
          (∫ x, Real.exp (t * x) ∂(kepReferenceLaw eps j : Measure ℝ)) ≤
            Real.exp (t + C * t ^ 2) := by
  obtain ⟨D, theta, vlo, vhi, e0, _, ht, hvlo, hv, hreg⟩ := kepReferenceLaw_regular
  let t0 := saTiltRadius vlo (2 * D / theta) (theta / 2)
  have htHalf : 0 < theta / 2 := by positivity
  refine ⟨vhi, t0, e0, hvlo.trans_le hv, saTiltRadius_pos hvlo htHalf, ?_⟩
  intro eps he j t htime
  let nu := kepReferenceLaw eps j
  have H := (hreg eps he j).univClass ht hvlo
  have hsmall : |t| ≤ theta / 2 := by
    have hh := htime.trans (saTiltRadius_le_half vlo (2 * D / theta) htHalf)
    linarith
  have hi := H.kernel_integrable_exp_raw hsmall
  have hpos : 0 < mgf id (nu : Measure ℝ) t :=
    mgf_pos' (NeZero.ne (nu : Measure ℝ)) hi
  have heq : Real.exp (cgf id (nu : Measure ℝ) t) = mgf id (nu : Measure ℝ) t :=
    Real.exp_log hpos
  have hc : cgf id (nu : Measure ℝ) t ≤ t + vhi * t ^ 2 := by
    rw [H.kernel_raw_cgf_eq hsmall]
    have hh := H.kernel_centered_cgf_upper hvlo htHalf htime
    linarith only [hh]
  refine ⟨hi, ?_⟩
  change mgf id (nu : Measure ℝ) t ≤ _
  rw [← heq]
  exact Real.exp_le_exp.mpr hc

end

end PGM
