import PLAStochastic.Index.GEP.Kernel.Flux.Sections.IntervalPrimitive

/-!
# The interior and endpoint terms of a weighted section

This is the pathwise integration-by-parts identity before expectation. Its
endpoint rewards are evaluated at the actual section endpoints, so those
rewards are independent of the evaluation variable when the endpoint laws
are pushed forward. Only a first primitive is used.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter

theorem flux_interval_indicator_before {f : ℝ → ℝ} {L U x : ℝ}
    (hx : 0 ≤ x) (hxl : x ≤ L) :
    (∫ t in (0 : ℝ)..x, (Ioc L U).indicator f t) = 0 := by
  rw [intervalIntegral.integral_of_le hx]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  exact indicator_of_notMem (by intro hm; exact (not_lt_of_ge (ht.2.trans hxl)) hm.1) f

theorem flux_interval_indicator_inside {f : ℝ → ℝ} {L U x : ℝ}
    (hL : 0 ≤ L) (hlx : L ≤ x) (hxu : x ≤ U) :
    (∫ t in (0 : ℝ)..x, (Ioc L U).indicator f t) = ∫ t in L..x, f t := by
  rw [intervalIntegral.integral_of_le (hL.trans hlx), integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, intervalIntegral.integral_of_le hlx]
  have he : Ioc L U ∩ Ioc 0 x = Ioc L x := by
    ext t
    constructor
    · rintro ⟨ht, ht'⟩
      exact ⟨ht.1, ht'.2⟩
    · intro ht
      exact ⟨⟨ht.1, ht.2.trans hxu⟩, lt_of_le_of_lt hL ht.1, ht.2⟩
  rw [he]

theorem flux_interval_indicator_after {f : ℝ → ℝ} {L U x : ℝ}
    (hL : 0 ≤ L) (hlu : L ≤ U) (hux : U ≤ x) :
    (∫ t in (0 : ℝ)..x, (Ioc L U).indicator f t) = ∫ t in L..U, f t := by
  rw [intervalIntegral.integral_of_le (hL.trans (hlu.trans hux)),
    integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    intervalIntegral.integral_of_le hlu]
  have he : Ioc L U ∩ Ioc 0 x = Ioc L U := by
    ext t
    constructor
    · exact fun ht => ht.1
    · intro ht
      exact ⟨ht, lt_of_le_of_lt hL ht.1, ht.2.trans hux⟩
  rw [he]

/-- Exact endpoint-plus-interior formula on one actual interval. The endpoint
terms are fixed path rewards `F L` and `F U`, not rewards evaluated at `x`. -/
theorem flux_weighted_interval_identity {F f : ℝ → ℝ} {L U x : ℝ}
    (hL : 0 ≤ L) (hlu : L ≤ U) (hx : 0 ≤ x)
    (hF : ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∫ t in a..b, f t) = F b - F a) :
    (Ioc L U).indicator F x =
      (if L < x then F L else 0) - (if U < x then F U else 0) +
        ∫ t in (0 : ℝ)..x, (Ioc L U).indicator f t := by
  classical
  by_cases hlx : L < x
  · by_cases hux : U < x
    · rw [indicator_of_notMem (by intro hm; exact (not_le.mpr hux) hm.2),
        if_pos hlx, if_pos hux, flux_interval_indicator_after hL hlu hux.le,
        hF L U hL hlu]
      ring
    · have hxu : x ≤ U := le_of_not_gt hux
      rw [indicator_of_mem (show x ∈ Ioc L U from ⟨hlx, hxu⟩), if_pos hlx, if_neg hux,
        flux_interval_indicator_inside hL hlx.le hxu, hF L x hL hlx.le]
      ring
  · have hxl : x ≤ L := le_of_not_gt hlx
    have hux : ¬ U < x := not_lt_of_ge (hxl.trans hlu)
    rw [indicator_of_notMem (by intro hm; exact hlx hm.1), if_neg hlx, if_neg hux,
      flux_interval_indicator_before hx hxl]
    ring

end

end PGM
