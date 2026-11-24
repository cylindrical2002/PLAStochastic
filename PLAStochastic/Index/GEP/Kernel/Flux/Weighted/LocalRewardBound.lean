import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.LocalReward

/-!
# Local variation bounds for endpoint rewards

The derivative of an endpoint CDF has local mass bounded by the absolute reward
on the corresponding endpoint sublevel set. Global endpoint moments are not
needed. These quantitative bounds permit summation of the genuine output flux.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter
open scoped Interval ENNReal

theorem flux_cdf_nonneg_local_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {E W : Ω → ℝ}
    (hE : Measurable E) (hac : (P.map E).restrict (Ioi 0) ≪ volume)
    (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤ ∫ ω in {ω | E ω ≤ max 0 R}, W ω ∂P := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (W ω))
  have hQ : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hQa : (Q.map E).restrict (Ioi 0) ≪ volume :=
    ((hQ.map hE).restrict (Ioi 0)).trans hac
  have hfin : ∀ R : ℝ, (Q.map E) (Iic R) ≠ ∞ := by
    intro R
    rw [Measure.map_apply hE measurableSet_Iic]
    change (P.withDensity (fun ω => ENNReal.ofReal (W ω))) {ω | E ω ≤ R} ≠ ∞
    rw [withDensity_apply' _ _]
    have hh := (hWi R).2
    rw [hasFiniteIntegral_iff_enorm] at hh
    simpa only [Real.enorm_of_nonneg (hW0 _)] using hh.ne
  have : SigmaFinite (Q.map E) := flux_sigmaFinite_of_cdf_finite _ hfin
  have hp := flux_cdf_aePrimitive_local (Q.map E) hfin hQa
  have he (x : ℝ) : (Q.map E).real (Iic x) = ∫ ω in {ω | E ω ≤ x}, W ω ∂P := by
    rw [map_measureReal_apply hE measurableSet_Iic]
    exact flux_weighted_measure_real P hW hW0 (hE measurableSet_Iic)
  refine ⟨fluxEndpointDensity ((Q.map E).restrict (Ioi 0)), ?_, fun R => ?_⟩
  · simpa only [he] using hp
  · calc
      _ = ∫ x in Ι (0 : ℝ) R, fluxEndpointDensity ((Q.map E).restrict (Ioi 0)) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only
          rw [Real.norm_eq_abs, fluxEndpointDensity, abs_of_nonneg ENNReal.toReal_nonneg]
      _ = ((Q.map E).restrict (Ioi 0)).real (Ι (0 : ℝ) R) :=
        Measure.setIntegral_toReal_rnDeriv hQa _
      _ = (Q.map E).real ((Ι (0 : ℝ) R) ∩ Ioi 0) :=
        measureReal_restrict_apply measurableSet_uIoc
      _ ≤ (Q.map E).real (Iic (max 0 R)) :=
        measureReal_mono (fun x hx => hx.1.2) (hfin _)
      _ = _ := he _

/-- The signed endpoint derivative obeys a local total-variation bound. -/
theorem flux_cdf_local_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {E W : Ω → ℝ}
    (hE : Measurable E) (hac : (P.map E).restrict (Ioi 0) ≪ volume)
    (hW : Measurable W) (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤ ∫ ω in {ω | E ω ≤ max 0 R}, |W ω| ∂P := by
  obtain ⟨jp, ⟨hIp, cp, hcp⟩, hbp⟩ := flux_cdf_nonneg_local_weight_bound P hE hac
    (hW.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).pos_part)
  obtain ⟨jn, ⟨hIn, cn, hcn⟩, hbn⟩ := flux_cdf_nonneg_local_weight_bound P hE hac
    (hW.neg.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).neg_part)
  simp only [Pi.neg_apply] at hcn hbn
  refine ⟨fun x => jp x - jn x, ⟨fun R => (hIp R).sub (hIn R), cp - cn, ?_⟩, fun R => ?_⟩
  · filter_upwards [hcp, hcn] with x hp hn
    have he : (∫ ω in {ω | E ω ≤ x}, W ω ∂P) =
        (∫ ω in {ω | E ω ≤ x}, max (W ω) 0 ∂P) -
        (∫ ω in {ω | E ω ≤ x}, max (-W ω) 0 ∂P) := by
      rw [← integral_sub (hWi x).pos_part (hWi x).neg_part]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by grind
    rw [he, hp, hn, intervalIntegral.integral_sub (hIp x) (hIn x)]
    ring
  · calc
      _ ≤ ∫ x in Ι (0 : ℝ) R, ‖jp x‖ + ‖jn x‖ :=
        integral_mono ((hIp R).def'.sub (hIn R).def').norm
          ((hIp R).def'.norm.add (hIn R).def'.norm) (fun x => norm_sub_le _ _)
      _ = (∫ x in Ι (0 : ℝ) R, ‖jp x‖) + ∫ x in Ι (0 : ℝ) R, ‖jn x‖ :=
        integral_add (hIp R).def'.norm (hIn R).def'.norm
      _ ≤ (∫ ω in {ω | E ω ≤ max 0 R}, max (W ω) 0 ∂P) +
          ∫ ω in {ω | E ω ≤ max 0 R}, max (-W ω) 0 ∂P := add_le_add (hbp R) (hbn R)
      _ = _ := by
        rw [← integral_add (hWi _).pos_part (hWi _).neg_part]
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by grind

end

end PGM
