import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments

/-!
# A conditional cumulant budget with an arbitrary mean bound

The original nonhomogeneous gaps are compared in the physical units of the
parent anchor. Their mean need not be one. The quadratic exponential estimate
therefore retains the actual uniform mean budget before the stopping argument.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory

theorem integral_exp_mul_le_of_mean_expMom {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {a B m t : ℝ}
    (ha : 0 < a) (hpos : ∀ᵐ w ∂P, 0 ≤ X w) (hX : Integrable X P)
    (hmean : ∫ w, X w ∂P ≤ m)
    (he : Integrable (fun w => Real.exp (a * X w)) P)
    (hB : ∫ w, Real.exp (a * X w) ∂P ≤ B) (ht : 0 ≤ t) (hta : t ≤ a / 2) :
    Integrable (fun w => Real.exp (t * X w)) P ∧
      ∫ w, Real.exp (t * X w) ∂P ≤ Real.exp (m * t + 8 * B / a ^ 2 * t ^ 2) := by
  have hint : Integrable (fun w => Real.exp (t * X w)) P := by
    refine he.mono' ?_ (hpos.mono fun w hw => ?_)
    · exact (Real.measurable_exp.comp_aemeasurable
        (hX.aemeasurable.const_mul t)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hw)
  have hbd : Integrable (fun w => 1 + t * X w +
      t ^ 2 * (8 / a ^ 2 * Real.exp (a * X w))) P :=
    ((integrable_const 1).add (hX.const_mul t)).add ((he.const_mul _).const_mul _)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ w, (1 + t * X w + t ^ 2 * (8 / a ^ 2 * Real.exp (a * X w))) ∂P :=
      integral_mono_ae hint hbd (hpos.mono fun w hw => exp_mul_le_quadratic ha ht hta hw)
    _ = 1 + t * ∫ w, X w ∂P + t ^ 2 * (8 / a ^ 2 * ∫ w, Real.exp (a * X w) ∂P) := by
      rw [integral_add (f := fun w => 1 + t * X w)
        (g := fun w => t ^ 2 * (8 / a ^ 2 * Real.exp (a * X w)))
        ((integrable_const 1).add (hX.const_mul t)) ((he.const_mul _).const_mul _),
        integral_add (f := fun _ => (1 : ℝ)) (g := fun w => t * X w)
        (integrable_const 1) (hX.const_mul t), integral_const_mul,
        integral_const_mul, integral_const_mul]
      simp
    _ ≤ 1 + t * m + t ^ 2 * (8 / a ^ 2 * B) := by gcongr
    _ = 1 + (m * t + 8 * B / a ^ 2 * t ^ 2) := by ring
    _ ≤ Real.exp (m * t + 8 * B / a ^ 2 * t ^ 2) := by
      linarith [Real.add_one_le_exp (m * t + 8 * B / a ^ 2 * t ^ 2)]

end

end PGM
