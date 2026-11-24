import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.MovingReward

/-!
# Unbounded weighted sections

The half-line case has one actual finite endpoint and an interior derivative.
It is treated directly, without replacing infinity by an artificial root.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

theorem flux_halfLine_weighted_identity {F f : ℝ → ℝ} {L x : ℝ}
    (hL : 0 ≤ L) (hx : 0 ≤ x)
    (hF : ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∫ t in a..b, f t) = F b - F a) :
    (Ioi L).indicator F x = (if L < x then F L else 0) +
      ∫ t in (0 : ℝ)..x, (Ioi L).indicator f t := by
  classical
  by_cases hlx : L < x
  · have hi : (∫ t in (0 : ℝ)..x, (Ioi L).indicator f t) = ∫ t in L..x, f t := by
      rw [intervalIntegral.integral_of_le hx, integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, intervalIntegral.integral_of_le hlx.le]
      have he : Ioi L ∩ Ioc 0 x = Ioc L x := by
        ext t
        constructor
        · exact fun ht => ⟨ht.1, ht.2.2⟩
        · exact fun ht => ⟨ht.1, lt_of_le_of_lt hL ht.1, ht.2⟩
      rw [he]
    rw [indicator_of_mem (show x ∈ Ioi L from hlx), if_pos hlx, hi, hF L x hL hlx.le]
    ring
  · have hi : (∫ t in (0 : ℝ)..x, (Ioi L).indicator f t) = 0 := by
      rw [intervalIntegral.integral_of_le hx]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      exact indicator_of_notMem (not_lt_of_ge (ht.2.trans (le_of_not_gt hlx))) f
    rw [indicator_of_notMem (show x ∉ Ioi L from hlx), if_neg hlx, hi, add_zero]

/-- The actual weighted half-line has its endpoint density plus its interior
derivative. Local integrability is sufficient throughout. -/
theorem flux_weighted_halfLine_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L : Ω → ℝ} {F f : Ω → ℝ → ℝ}
    (hL : Measurable L) (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω) (hFL : Measurable (fun ω => F ω (L ω)))
    (hiL : ∀ R : ℝ, IntegrableOn (fun ω => F ω (L ω)) {ω | L ω ≤ R} P)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a)
    (hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioi (L p.1)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R)))) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fun x => ∫ ω, (Ioi (L ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P) + B x) := by
  obtain ⟨jL, hIL, cL, hcL⟩ := flux_cdf_local_weight_aePrimitive P hL hacL hFL hiL
  let H : ℝ → ℝ := fun x => ∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P
  have hH : ∀ R : ℝ, IntervalIntegrable H volume 0 R := by
    intro R
    rw [intervalIntegrable_iff]
    exact (hprod R).integral_prod_right
  refine ⟨jL, ⟨fun R => (hH R).add (hIL R), cL, ?_⟩⟩
  filter_upwards [hcL, ae_restrict_mem measurableSet_Ioi] with x hcxL hx
  have hx0 : 0 < x := hx
  have he : ∀ᵐ ω ∂P,
      (Ioi (L ω)).indicator (F ω) x =
        {ω | L ω ≤ x}.indicator (fun ω => F ω (L ω)) ω +
        ∫ t in (0 : ℝ)..x, (Ioi (L ω)).indicator (f ω) t := by
    filter_upwards [hL0, hF, flux_endpoint_ae_ne_positive P hL hacL hx0] with ω hω hωF hnL
    have hh := flux_halfLine_weighted_identity hω hx0.le hωF
    have hleL : L ω < x ↔ L ω ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hnL⟩
    simp only [hleL] at hh
    simpa only [indicator_apply, mem_ofPred_eq] using hh
  have hSL : MeasurableSet {ω | L ω ≤ x} := hL measurableSet_Iic
  have hiLi : Integrable ({ω | L ω ≤ x}.indicator (fun ω => F ω (L ω))) P :=
    (integrable_indicator_iff hSL).2 (hiL x)
  have hiInt : Integrable (fun ω => ∫ t in (0 : ℝ)..x, (Ioi (L ω)).indicator (f ω) t) P := by
    simpa only [intervalIntegral.integral_of_le hx0.le, uIoc_of_le hx0.le] using
      (hprod x).integral_prod_left
  rw [integral_congr_ae he, integral_add hiLi hiInt, integral_indicator hSL, hcxL,
    ← intervalIntegral_integral_swap (μ := P) (a := 0) (b := x)
      (f := fun t ω => (Ioi (L ω)).indicator (f ω) t) (hprod x).swap,
    intervalIntegral.integral_add (hH x) (hIL x)]
  ring

end

end PGM
