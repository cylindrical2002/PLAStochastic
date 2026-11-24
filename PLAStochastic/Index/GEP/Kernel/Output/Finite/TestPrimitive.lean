import PLAStochastic.Index.GEP.Response.Score.UniformBounds

/-!
# The actual output test as a first primitive in one inserted gap

`OutTest` only assumes a measurable exponentially bounded first derivative.
Affine substitution in its defining integral supplies the pathwise primitive
identity needed by the weighted-section construction, without differentiating
the test derivative.
-/

namespace PGM

noncomputable section

open MeasureTheory Set

theorem flux_testFn_shift_primitive {η M C s a b : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hC : 0 < C) (hs : 0 ≤ s) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, ψ ((s + t) / C) / C) =
      testFn ψ ((s + b) / C) - testFn ψ ((s + a) / C) := by
  have he : (∫ t in a..b, ψ ((s + t) / C) / C) =
      ∫ t in a..b, psiPos ψ ((s + t) / C) / C := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 < (s + t) / C := div_pos (by linarith [ht.1]) hC
    change ψ ((s + t) / C) / C = psiPos ψ ((s + t) / C) / C
    rw [psiPos, indicator_of_mem (show (s + t) / C ∈ Ioi (0 : ℝ) from ht0)]
  rw [he]
  calc
    _ = ∫ t in (s + a) / C..(s + b) / C, psiPos ψ t := by
      simp_rw [add_div]
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_comp_add_div (psiPos ψ) hC.ne' (s / C), smul_eq_mul]
      field_simp
    _ = _ := by
      rw [testFn_eq_primitive, testFn_eq_primitive,
        intervalIntegral.integral_interval_sub_left
          (hψ.intervalIntegrable 0 ((s + b) / C))
          (hψ.intervalIntegrable 0 ((s + a) / C))]

end

end PGM
