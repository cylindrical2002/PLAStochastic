import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.LocalRewardBound
import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Dominated

/-!
# Quantitative primitives of weighted sections

The boundary term is the difference of the actual endpoint reward densities.
Its local variation is controlled by the two endpoint sublevel reward masses.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter
open scoped Interval

theorem flux_weighted_section_aePrimitive_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {L U : Ω → ℝ} {F f : Ω → ℝ → ℝ}
    (hL : Measurable L) (hU : Measurable U)
    (hacL : (P.map L).restrict (Ioi 0) ≪ volume)
    (hacU : (P.map U).restrict (Ioi 0) ≪ volume)
    (hLU : ∀ᵐ ω ∂P, 0 ≤ L ω ∧ L ω ≤ U ω)
    (hFL : Measurable (fun ω => F ω (L ω))) (hFU : Measurable (fun ω => F ω (U ω)))
    (hiL : ∀ R : ℝ, IntegrableOn (fun ω => F ω (L ω)) {ω | L ω ≤ R} P)
    (hiU : ∀ R : ℝ, IntegrableOn (fun ω => F ω (U ω)) {ω | U ω ≤ R} P)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a)
    (hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioc (L p.1) (U p.1)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R)))) :
    ∃ B : ℝ → ℝ,
      AEPrimitive (fun x => ∫ ω, (Ioc (L ω) (U ω)).indicator (F ω) x ∂P)
        (fun x => (∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P) + B x) ∧
      (∀ R : ℝ, IntervalIntegrable B volume 0 R) ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖B x‖) ≤
        (∫ ω in {ω | L ω ≤ max 0 R}, |F ω (L ω)| ∂P) +
          ∫ ω in {ω | U ω ≤ max 0 R}, |F ω (U ω)| ∂P := by
  obtain ⟨jL, ⟨hIL, cL, hcL⟩, hbL⟩ := flux_cdf_local_weight_bound P hL hacL hFL hiL
  obtain ⟨jU, ⟨hIU, cU, hcU⟩, hbU⟩ := flux_cdf_local_weight_bound P hU hacU hFU hiU
  let H : ℝ → ℝ := fun x => ∫ ω, (Ioc (L ω) (U ω)).indicator (f ω) x ∂P
  have hH : ∀ R : ℝ, IntervalIntegrable H volume 0 R := by
    intro R
    rw [intervalIntegrable_iff]
    exact (hprod R).integral_prod_right
  have hbound (R : ℝ) : (∫ x in Ι (0 : ℝ) R, ‖jL x - jU x‖) ≤
      (∫ ω in {ω | L ω ≤ max 0 R}, |F ω (L ω)| ∂P) +
        ∫ ω in {ω | U ω ≤ max 0 R}, |F ω (U ω)| ∂P := by
    calc
      _ ≤ ∫ x in Ι (0 : ℝ) R, ‖jL x‖ + ‖jU x‖ :=
        integral_mono ((hIL R).def'.sub (hIU R).def').norm
          ((hIL R).def'.norm.add (hIU R).def'.norm) (fun x => norm_sub_le _ _)
      _ = (∫ x in Ι (0 : ℝ) R, ‖jL x‖) + ∫ x in Ι (0 : ℝ) R, ‖jU x‖ :=
        integral_add (hIL R).def'.norm (hIU R).def'.norm
      _ ≤ _ := add_le_add (hbL R) (hbU R)
  refine ⟨fun x => jL x - jU x,
    ⟨fun R => (hH R).add ((hIL R).sub (hIU R)), cL - cU, ?_⟩,
    fun R => (hIL R).sub (hIU R), hbound⟩
  filter_upwards [hcL, hcU, ae_restrict_mem measurableSet_Ioi] with x hcxL hcxU hx
  have hx0 : 0 < x := hx
  have he : ∀ᵐ ω ∂P,
      (Ioc (L ω) (U ω)).indicator (F ω) x =
        {ω | L ω ≤ x}.indicator (fun ω => F ω (L ω)) ω -
        {ω | U ω ≤ x}.indicator (fun ω => F ω (U ω)) ω +
        ∫ t in (0 : ℝ)..x, (Ioc (L ω) (U ω)).indicator (f ω) t := by
    filter_upwards [hLU, hF, flux_endpoint_ae_ne_positive P hL hacL hx,
      flux_endpoint_ae_ne_positive P hU hacU hx] with ω hω hωF hnL hnU
    have hh := flux_weighted_interval_identity hω.1 hω.2 hx.le hωF
    have hleL : L ω < x ↔ L ω ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hnL⟩
    have hleU : U ω < x ↔ U ω ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h hnU⟩
    simp only [hleL, hleU] at hh
    simpa only [indicator_apply, mem_ofPred_eq] using hh
  have hSL : MeasurableSet {ω | L ω ≤ x} := hL measurableSet_Iic
  have hSU : MeasurableSet {ω | U ω ≤ x} := hU measurableSet_Iic
  have hiLi : Integrable ({ω | L ω ≤ x}.indicator (fun ω => F ω (L ω))) P :=
    (integrable_indicator_iff hSL).2 (hiL x)
  have hiUi : Integrable ({ω | U ω ≤ x}.indicator (fun ω => F ω (U ω))) P :=
    (integrable_indicator_iff hSU).2 (hiU x)
  have hiInt : Integrable
      (fun ω => ∫ t in (0 : ℝ)..x, (Ioc (L ω) (U ω)).indicator (f ω) t) P := by
    simpa only [intervalIntegral.integral_of_le hx0.le, uIoc_of_le hx0.le] using
      (hprod x).integral_prod_left
  have hiDiff : Integrable (fun ω =>
      {ω | L ω ≤ x}.indicator (fun ω => F ω (L ω)) ω -
      {ω | U ω ≤ x}.indicator (fun ω => F ω (U ω)) ω) P := hiLi.sub hiUi
  have hiJDiff : IntervalIntegrable (fun t => jL t - jU t) volume 0 x := (hIL x).sub (hIU x)
  rw [integral_congr_ae he, integral_add hiDiff hiInt, integral_sub hiLi hiUi,
    integral_indicator hSL, integral_indicator hSU,
    hcxL, hcxU, ← intervalIntegral_integral_swap (μ := P) (a := 0) (b := x)
      (f := fun t ω => (Ioc (L ω) (U ω)).indicator (f ω) t) (hprod x).swap,
    intervalIntegral.integral_add (hH x) hiJDiff,
    intervalIntegral.integral_sub (hIL x) (hIU x)]
  ring


theorem flux_weighted_halfLine_aePrimitive_bound {Ω : Type*} [MeasurableSpace Ω]
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
        (fun x => (∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P) + B x) ∧
      (∀ R : ℝ, IntervalIntegrable B volume 0 R) ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖B x‖) ≤
        ∫ ω in {ω | L ω ≤ max 0 R}, |F ω (L ω)| ∂P := by
  obtain ⟨jL, ⟨hIL, cL, hcL⟩, hbL⟩ := flux_cdf_local_weight_bound P hL hacL hFL hiL
  let H : ℝ → ℝ := fun x => ∫ ω, (Ioi (L ω)).indicator (f ω) x ∂P
  have hH : ∀ R : ℝ, IntervalIntegrable H volume 0 R := by
    intro R
    rw [intervalIntegrable_iff]
    exact (hprod R).integral_prod_right
  refine ⟨jL, ⟨fun R => (hH R).add (hIL R), cL, ?_⟩, hIL, hbL⟩
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
