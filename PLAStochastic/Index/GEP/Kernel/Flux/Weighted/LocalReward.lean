import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.IntegrableReward

/-!
# Locally integrable endpoint rewards

Output rewards evaluated at a distant facet root need not have a finite global
first moment. On bounded spatial intervals only roots in a bounded sublevel set
contribute. The original `AEPrimitive` requires precisely this local control.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter
open scoped Interval ENNReal

theorem flux_sigmaFinite_of_cdf_finite (μ : Measure ℝ)
    (hfin : ∀ R : ℝ, μ (Iic R) ≠ ∞) : SigmaFinite μ := by
  let S : μ.FiniteSpanningSetsIn univ :=
    { set := fun n => Iic (n : ℝ)
      set_mem := fun _ => mem_univ _
      finite := fun n => (hfin n).lt_top
      spanning := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨n, hn⟩ := exists_nat_gt x
        exact mem_iUnion.mpr ⟨n, hn.le⟩ }
  exact S.sigmaFinite

/-- A locally finite positive endpoint law gives the original primitive; the
whole endpoint measure need not be finite. -/
theorem flux_cdf_aePrimitive_local (μ : Measure ℝ)
    (hfin : ∀ R : ℝ, μ (Iic R) ≠ ∞) (hac : μ.restrict (Ioi 0) ≪ volume) :
    AEPrimitive (fun x => μ.real (Iic x)) (fluxEndpointDensity (μ.restrict (Ioi 0))) := by
  have : SigmaFinite μ := flux_sigmaFinite_of_cdf_finite μ hfin
  refine ⟨fun R => ?_, μ.real (Iic 0), ?_⟩
  · rw [intervalIntegrable_iff]
    apply Measure.integrableOn_toReal_rnDeriv
    have hb : (μ.restrict (Ioi 0)) (Ι (0 : ℝ) R) ≤ μ (Iic (max 0 R)) := by
      refine (Measure.restrict_le_self _).trans (measure_mono ?_)
      intro x hx
      exact hx.2
    exact (hb.trans_lt (hfin (max 0 R)).lt_top).ne
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hix : μ (Ioc 0 x) ≠ ∞ :=
      ((measure_mono Ioc_subset_Iic_self).trans_lt (hfin x).lt_top).ne
    have hs := measureReal_union (μ := μ) (Iic_disjoint_Ioc (a := (0 : ℝ)) le_rfl)
      (measurableSet_Ioc (a := (0 : ℝ)) (b := x)) (hfin 0) hix
    rw [Iic_union_Ioc_eq_Iic hx.le] at hs
    rw [intervalIntegral.integral_of_le hx.le]
    have hd := Measure.setIntegral_toReal_rnDeriv hac (Ioc 0 x)
    rw [measureReal_restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (fun t ht => ht.1)] at hd
    rw [show (∫ t in Ioc 0 x, fluxEndpointDensity (μ.restrict (Ioi 0)) t) = μ.real (Ioc 0 x)
      from hd]
    exact hs

/-- Only rewards at endpoints below each fixed `R` need to be integrable.
This avoids an unjustified global moment assumption on near-degenerate roots. -/
theorem flux_cdf_nonneg_local_weight_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {E W : Ω → ℝ}
    (hE : Measurable E) (hac : (P.map E).restrict (Ioi 0) ≪ volume)
    (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) j := by
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
  have hp := flux_cdf_aePrimitive_local (Q.map E) hfin hQa
  have he : (fun x => (Q.map E).real (Iic x)) =
      (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) := by
    funext x
    rw [map_measureReal_apply hE measurableSet_Iic]
    exact flux_weighted_measure_real P hW hW0 (hE measurableSet_Iic)
  rw [he] at hp
  exact ⟨_, hp⟩

/-- Signed rewards with local endpoint moments have a locally integrable
derivative on the whole positive half-line. -/
theorem flux_cdf_local_weight_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {E W : Ω → ℝ}
    (hE : Measurable E) (hac : (P.map E).restrict (Ioi 0) ≪ volume)
    (hW : Measurable W) (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P) :
    ∃ j : ℝ → ℝ, AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) j := by
  obtain ⟨jp, hIp, cp, hcp⟩ := flux_cdf_nonneg_local_weight_aePrimitive P hE hac
    (hW.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).pos_part)
  obtain ⟨jn, hIn, cn, hcn⟩ := flux_cdf_nonneg_local_weight_aePrimitive P hE hac
    (hW.neg.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).neg_part)
  simp only [Pi.neg_apply] at hcn
  refine ⟨fun x => jp x - jn x, fun R => (hIp R).sub (hIn R), cp - cn, ?_⟩
  filter_upwards [hcp, hcn] with x hp hn
  have he : (∫ ω in {ω | E ω ≤ x}, W ω ∂P) =
      (∫ ω in {ω | E ω ≤ x}, max (W ω) 0 ∂P) -
      (∫ ω in {ω | E ω ≤ x}, max (-W ω) 0 ∂P) := by
    rw [← integral_sub (hWi x).pos_part (hWi x).neg_part]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by grind
  rw [he, hp, hn, intervalIntegral.integral_sub (hIp x) (hIn x)]
  ring

end

end PGM
