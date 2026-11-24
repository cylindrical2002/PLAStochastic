import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.OneGapPrimitive

/-!
# Integrable rewards on the actual one-gap sections

Multiplying the path law by a nonnegative integrable reward preserves absolute
continuity of every section endpoint law. Positive and negative parts therefore
give a signed weighted primitive with a sharp total-variation majorant. The
reward here depends on the unmarked path; dependence on the inserted coordinate
needs an additional interior derivative and is not hidden in this statement.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem flux_weighted_measure_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {W : Ω → ℝ} (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    {S : Set Ω} (hS : MeasurableSet S) :
    (P.withDensity (fun ω => ENNReal.ofReal (W ω))).real S = ∫ ω in S, W ω ∂P := by
  have he := setIntegral_withDensity_eq_setIntegral_toReal_smul (μ := P)
    hW.ennreal_ofReal (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)
    (fun _ : Ω => (1 : ℝ)) hS
  simpa only [setIntegral_const, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (hW0 _)] using he

/-- Endpoint rewards may depend on the full path, including the selected
endpoint. Their weighted endpoint law remains absolutely continuous. -/
theorem flux_cdf_nonneg_weight_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {E W : Ω → ℝ}
    (hE : Measurable E) (hac : (P.map E).restrict (Ioi 0) ≪ volume)
    (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (hWi : Integrable W P) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ ∫ ω, W ω ∂P := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (W ω))
  have : IsFiniteMeasure Q := isFiniteMeasure_withDensity_ofReal hWi.2
  have hQ : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hQa : (Q.map E).restrict (Ioi 0) ≪ volume :=
    ((hQ.map hE).restrict (Ioi 0)).trans hac
  let j := fluxEndpointDensity ((Q.map E).restrict (Ioi 0))
  have hp := flux_cdf_aePrimitive_of_ac_positive (Q.map E) hQa
  have he : (fun x => (Q.map E).real (Iic x)) =
      (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) := by
    funext x
    rw [map_measureReal_apply hE measurableSet_Iic]
    exact flux_weighted_measure_real P hW hW0 (hE measurableSet_Iic)
  rw [he] at hp
  refine ⟨j, hp, integrable_fluxEndpointDensity _, ?_⟩
  have hb := flux_endpoint_density_mass_le Q hE
  have hmass : Q.real univ = ∫ ω, W ω ∂P := by
    simpa only [setIntegral_univ] using flux_weighted_measure_real P hW hW0 MeasurableSet.univ
  simpa only [hmass] using hb

/-- Signed endpoint rewards give the actual weighted CDF primitive, with
derivative mass bounded by the absolute reward mass. -/
theorem flux_cdf_weight_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {E W : Ω → ℝ}
    (hE : Measurable E) (hac : (P.map E).restrict (Ioi 0) ≪ volume)
    (hW : Measurable W) (hWi : Integrable W P) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ ∫ ω, |W ω| ∂P := by
  obtain ⟨jp, ⟨hIp, cp, hcp⟩, hjp, hbp⟩ :=
    flux_cdf_nonneg_weight_aePrimitive P hE hac (hW.max measurable_const)
      (fun ω => le_max_right _ _) hWi.pos_part
  obtain ⟨jn, ⟨hIn, cn, hcn⟩, hjn, hbn⟩ :=
    flux_cdf_nonneg_weight_aePrimitive P hE hac (hW.neg.max measurable_const)
      (fun ω => le_max_right _ _) hWi.neg_part
  simp only [Pi.neg_apply] at hcn hbn
  refine ⟨fun x => jp x - jn x, ⟨fun R => (hIp R).sub (hIn R), cp - cn, ?_⟩,
    hjp.sub hjn, ?_⟩
  · filter_upwards [hcp, hcn] with x hp hn
    have he : (∫ ω in {ω | E ω ≤ x}, W ω ∂P) =
        (∫ ω in {ω | E ω ≤ x}, max (W ω) 0 ∂P) -
        (∫ ω in {ω | E ω ≤ x}, max (-W ω) 0 ∂P) := by
      rw [← integral_sub hWi.pos_part.integrableOn hWi.neg_part.integrableOn]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by grind
    rw [he, hp, hn, intervalIntegral.integral_sub (hIp x) (hIn x)]
    ring
  · calc
      _ ≤ ∫ x, ‖jp x‖ + ‖jn x‖ :=
        integral_mono (hjp.sub hjn).norm (hjp.norm.add hjn.norm) (fun x => norm_sub_le _ _)
      _ = (∫ x, ‖jp x‖) + ∫ x, ‖jn x‖ := integral_add hjp.norm hjn.norm
      _ ≤ (∫ ω, max (W ω) 0 ∂P) + ∫ ω, max (-W ω) 0 ∂P := add_le_add hbp hbn
      _ = ∫ ω, |W ω| ∂P := by
        rw [← integral_add hWi.pos_part hWi.neg_part]
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by grind

/-- Nonnegative integrable path rewards produce a primitive of the actual
inserted prefix event. Its derivative mass is bounded by twice the reward mass. -/
theorem flux_prefix_nonneg_weight_aePrimitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    {W : (ℕ → ℝ) → ℝ} (hW : Measurable W) (hW0 : ∀ g, 0 ≤ W g)
    (hWi : Integrable W P) (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    ∃ j : ℝ → ℝ,
      AEPrimitive
        (fun x => ∫ g in {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}, W g ∂P) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ 2 * ∫ g, W g ∂P := by
  let Q := P.withDensity (fun g => ENNReal.ofReal (W g))
  have : IsFiniteMeasure Q := isFiniteMeasure_withDensity_ofReal hWi.2
  have hQ : Q ≪ iidLaw ν := (withDensity_absolutelyContinuous _ _).trans hP
  obtain ⟨j, hj, hji, hb⟩ := flux_prefix_measure_aePrimitive hac hpos Q hQ eps hk hi
  have he : (fun x => Q.real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}) =
      (fun x => ∫ g in {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}, W g ∂P) := by
    funext x
    exact flux_weighted_measure_real P hW hW0
      ((measurableSet_lt_gapSegLen eps k).preimage
        ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id)))
  rw [he] at hj
  have hmass : Q.real univ = ∫ g, W g ∂P := by
    simpa only [setIntegral_univ] using flux_weighted_measure_real P hW hW0 MeasurableSet.univ
  rw [hmass] at hb
  exact ⟨j, hj, hji, hb⟩

/-- Signed integrable rewards require no positivity assumption and no new
endpoint regularity hypothesis. -/
theorem flux_prefix_weight_aePrimitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    {W : (ℕ → ℝ) → ℝ} (hW : Measurable W) (hWi : Integrable W P)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    ∃ j : ℝ → ℝ,
      AEPrimitive
        (fun x => ∫ g in {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}, W g ∂P) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ 2 * ∫ g, |W g| ∂P := by
  obtain ⟨jp, ⟨hIp, cp, hcp⟩, hjp, hbp⟩ :=
    flux_prefix_nonneg_weight_aePrimitive hac hpos P hP (hW.max measurable_const)
      (fun g => le_max_right _ _) hWi.pos_part eps hk hi
  obtain ⟨jn, ⟨hIn, cn, hcn⟩, hjn, hbn⟩ :=
    flux_prefix_nonneg_weight_aePrimitive hac hpos P hP (hW.neg.max measurable_const)
      (fun g => le_max_right _ _) hWi.neg_part eps hk hi
  simp only [Pi.neg_apply] at hcn hbn
  refine ⟨fun x => jp x - jn x, ⟨fun R => (hIp R).sub (hIn R), cp - cn, ?_⟩,
    hjp.sub hjn, ?_⟩
  · filter_upwards [hcp, hcn] with x hp hn
    have he : (∫ g in {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}, W g ∂P) =
        (∫ g in {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}, max (W g) 0 ∂P) -
        (∫ g in {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}, max (-W g) 0 ∂P) := by
      rw [← integral_sub hWi.pos_part.integrableOn hWi.neg_part.integrableOn]
      apply integral_congr_ae
      exact Eventually.of_forall fun g => by grind
    rw [he, hp, hn, intervalIntegral.integral_sub (hIp x) (hIn x)]
    ring
  · calc
      _ ≤ ∫ x, ‖jp x‖ + ‖jn x‖ :=
        integral_mono (hjp.sub hjn).norm (hjp.norm.add hjn.norm) (fun x => norm_sub_le _ _)
      _ = (∫ x, ‖jp x‖) + ∫ x, ‖jn x‖ := integral_add hjp.norm hjn.norm
      _ ≤ 2 * (∫ g, max (W g) 0 ∂P) + 2 * ∫ g, max (-W g) 0 ∂P := add_le_add hbp hbn
      _ = 2 * ∫ g, |W g| ∂P := by
        rw [← mul_add, ← integral_add hWi.pos_part hWi.neg_part]
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun g => by grind

end

end PGM
