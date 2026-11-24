import PLAStochastic.Index.GEP.Kernel.Output.Finite.OutTestBound

/-!
# Finite stopped-output pieces

The event that the original inserted stopping time equals `t` is the difference
of two actual survival events. Both events fit inside the same predetermined
unmarked window; the final marked coordinate is included without an exception.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval

def fluxOutputPiece (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) (C : ℝ)
    (t i : ℕ) (x : ℝ) : ℝ :=
  ∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator
    (fun g => testFn ψ (stopSum eps (Function.update g i x) / C)) g ∂iidLaw ν

theorem flux_survival_subset_winSet {eps x : ℝ} {k t i : ℕ} (hit : i < t) (htk : t ≤ k + 1) :
    {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} ⊆ winSet eps i t := by
  intro g hg
  change (k : ℕ∞) < gapSegLen eps (Function.update g i x) at hg
  have hiT : (i : ℕ∞) < gapSegLen eps (Function.update g i x) :=
    lt_of_le_of_lt (by exact_mod_cast (by omega : i ≤ k)) hg
  refine ⟨lt_gapSegLen_update_iff.mp hiT, fun h2 => ?_⟩
  rw [gapSegLen, lt_segLen_iff] at hg
  have hw := prefixAffineFeasible_window (r := i + 1) (w := t - (i + 2) + 1) hg (by omega)
  have hs : ((t - (i + 2) : ℕ) : ℕ∞) <
      segLen eps (fun j => gapKeys (Function.update g i x) (i + 1 + j)) :=
    (lt_segLen_iff _).mpr hw
  rwa [segLen_gapKeys_shift, update_shift_eq] at hs

theorem flux_enat_eq_iff_survival {T : ℕ∞} {t : ℕ} (ht : 0 < t) :
    T = t ↔ ((t - 1 : ℕ) : ℕ∞) < T ∧ ¬ (t : ℕ∞) < T := by
  by_cases hT : T = ⊤
  · simp [hT]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hT
    rw [← hn]
    norm_cast
    omega

theorem flux_stop_indicator_eq_sub {eps x : ℝ} {t i : ℕ} (ht : 0 < t)
    (F : (ℕ → ℝ) → ℝ) (g : ℕ → ℝ) :
    {g | gapSegLen eps (Function.update g i x) = t}.indicator F g =
      {g | ((t - 1 : ℕ) : ℕ∞) < gapSegLen eps (Function.update g i x)}.indicator F g -
      {g | (t : ℕ∞) < gapSegLen eps (Function.update g i x)}.indicator F g := by
  have hs : ((t : ℕ∞) < gapSegLen eps (Function.update g i x)) →
      ((t - 1 : ℕ) : ℕ∞) < gapSegLen eps (Function.update g i x) :=
    fun h => lt_trans (by exact_mod_cast (by omega : t - 1 < t)) h
  simp only [indicator_apply, mem_ofPred_eq, flux_enat_eq_iff_survival ht]
  by_cases h1 : (t : ℕ∞) < gapSegLen eps (Function.update g i x)
  · simp only [h1, hs h1, not_true_eq_false, and_false, if_false, if_true, sub_self]
  · by_cases h0 : ((t - 1 : ℕ) : ℕ∞) < gapSegLen eps (Function.update g i x) <;>
      simp only [h0, h1, not_false_eq_true, and_true, if_true, if_false, sub_zero]

theorem flux_stop_integral_eq_sub (P : Measure (ℕ → ℝ)) {eps x : ℝ} {t i : ℕ}
    (ht : 0 < t) {F : (ℕ → ℝ) → ℝ → ℝ} (hFi : Integrable (fun g => F g x) P) :
    (∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator (fun g => F g x) g ∂P) =
      fluxPrefixWeighted P eps (t - 1) i F x - fluxPrefixWeighted P eps t i F x := by
  have hm (k : ℕ) : MeasurableSet {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} :=
    (measurableSet_lt_gapSegLen eps k).preimage
      ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id))
  simp_rw [flux_stop_indicator_eq_sub ht]
  exact integral_sub (hFi.indicator (hm _)) (hFi.indicator (hm _))

theorem fluxOutputPiece_eq_window_partial (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (ψ : ℝ → ℝ) (C : ℝ) {t i : ℕ} (hit : i < t) (x : ℝ) :
    fluxOutputPiece eps ν ψ C t i x =
      ∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator
        (fun g => testFn ψ (gapKeys (Function.update g i x) t / C)) g
        ∂(iidLaw ν).restrict (winSet eps i t) := by
  rw [← integral_indicator (measurableSet_winSet eps i t)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro g
  by_cases hT : gapSegLen eps (Function.update g i x) = t
  · have hiT : (i : ℕ∞) < gapSegLen eps (Function.update g i x) := by
      rw [hT]
      exact_mod_cast hit
    have hW := (mem_winSet_of_eq hT (lt_gapSegLen_update_iff.mp hiT)).1
    simp only [indicator_of_mem (show g ∈ {g | gapSegLen eps (Function.update g i x) = t} from hT),
      indicator_of_mem hW, stopSum, hT, ENat.toNat_natCast]
  · simp only [indicator_of_notMem (show g ∉ {g | gapSegLen eps (Function.update g i x) = t} from hT)]
    by_cases hW : g ∈ winSet eps i t <;> simp [hT, hW]

theorem flux_partial_outTest_integrable {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (hit : i < t) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g => testFn ψ (gapKeys (Function.update g i x) t / C)) (iidLaw ν) := by
  have hκθ : 2 * η / C ≤ θ / 2 := by
    have he : 2 * η / C = 2 * (η / C) := by ring
    rw [he]
    linarith
  have hExp := flux_regLaw_unmarked_exp hν hθ (by positivity : 0 ≤ 2 * η / C) hκθ t i
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  simp_rw [flux_gapKeys_update hit]
  refine (hExp.const_mul (M / η * Real.exp ((2 * η / C) * max 0 x))).mono'
    ((hψ.measurable_testFn.comp (((measurable_fluxUnmarkedSum t i).add_const x).div_const C)).aestronglyMeasurable) ?_
  filter_upwards [hgs] with g hg
  exact (flux_testFn_shift_bounds hψ hη hC
    (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i).1 ⟨hx, le_max_right _ _⟩).1

/-- Each genuine stopped-output piece has a primitive whose derivative mass
is controlled by an exponential moment on the actual deleted-mark window. -/
theorem flux_output_piece_primitive_bound {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (ht : 3 ≤ t) (hit : i < t) :
    ∃ j : ℝ → ℝ, AEPrimitive (fluxOutputPiece eps ν ψ C t i) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        (2 * ((|R| * (M / C) + 2 * (M / η)) * Real.exp ((2 * η / C) * max 0 R))) *
          ∫ g in winSet eps i t, Real.exp ((2 * η / C) * fluxUnmarkedSum t i g) ∂iidLaw ν := by
  let P := (iidLaw ν).restrict (winSet eps i t)
  obtain ⟨jp, ⟨hIp, cp, hcp⟩, hbp⟩ := flux_prefix_output_partial_bound hν hθ P
    Measure.restrict_le_self eps (k := t - 1) (by omega) hit hψ hη hC hηθ
  obtain ⟨jn, ⟨hIn, cn, hcn⟩, hbn⟩ := flux_prefix_output_partial_bound hν hθ P
    Measure.restrict_le_self eps (k := t) (by omega) hit hψ hη hC hηθ
  refine ⟨fun x => jp x - jn x, ⟨fun R => (hIp R).sub (hIn R), cp - cn, ?_⟩, fun R => ?_⟩
  · filter_upwards [hcp, hcn, ae_restrict_mem measurableSet_Ioi] with x hpx hnx hx
    have hx0 : 0 < x := hx
    have hFi : Integrable (fun g => testFn ψ (gapKeys (Function.update g i x) t / C)) P :=
      (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ hit hx0.le).integrableOn
    rw [fluxOutputPiece_eq_window_partial eps ν ψ C hit x]
    change (∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator
      (fun g => testFn ψ (gapKeys (Function.update g i x) t / C)) g ∂P) = _
    rw [flux_stop_integral_eq_sub P (eps := eps) (x := x) (i := i)
      (F := fun g y => testFn ψ (gapKeys (Function.update g i y) t / C))
      (by omega : 0 < t) hFi, hpx, hnx, intervalIntegral.integral_sub (hIp x) (hIn x)]
    ring
  · calc
      _ ≤ ∫ x in Ι (0 : ℝ) R, ‖jp x‖ + ‖jn x‖ :=
        integral_mono ((hIp R).def'.sub (hIn R).def').norm
          ((hIp R).def'.norm.add (hIn R).def'.norm) (fun x => norm_sub_le _ _)
      _ = (∫ x in Ι (0 : ℝ) R, ‖jp x‖) + ∫ x in Ι (0 : ℝ) R, ‖jn x‖ :=
        integral_add (hIp R).def'.norm (hIn R).def'.norm
      _ ≤ _ := (add_le_add (hbp R) (hbn R)).trans_eq (by dsimp only [P]; ring)

/-- The already established window estimate is an ordinary real expectation
bound for the exact unmarked sum used in the output derivative estimate. -/
theorem flux_window_exp_le {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) {eps q κ : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m))
    (hκ0 : 0 ≤ κ) (hκ : 2 * κ ≤ θ / 4) {i t : ℕ} (hit : i < t) :
    (∫ g in winSet eps i t, Real.exp (κ * fluxUnmarkedSum t i g) ∂iidLaw ν) ≤
      winConst * q ^ (t - 2) * Real.exp (8 * D / θ ^ 2 * κ) ^ (t - 1) := by
  have hlin := lintegral_winSet_le hν hθ hq0 hq1 htail hκ0 hκ hit (x := 0)
  simp only [zero_add, mul_zero, Real.exp_zero, one_mul] at hlin
  rw [lintegral_indicator (measurableSet_winSet eps i t)] at hlin
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun g => (Real.exp_pos _).le)
    (((measurable_fluxUnmarkedSum t i).const_mul κ).exp.aestronglyMeasurable)]
  exact ENNReal.toReal_le_of_le_ofReal (by unfold winConst; positivity) hlin

end
end PGM
