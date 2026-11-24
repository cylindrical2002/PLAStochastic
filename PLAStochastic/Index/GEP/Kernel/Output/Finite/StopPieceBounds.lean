import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopPiece
import PLAStochastic.Index.Algorithm.EndpointHierarchyBounds

/-!
# Summable majorants for the actual stopped-output pieces

Both the absolute reward integral and the local derivative mass are controlled
by the same deleted-mark window exponential moment.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval

def fluxOutputIntegrand (eps : ℝ) (ψ : ℝ → ℝ) (C : ℝ) (t i : ℕ) (x : ℝ)
    (g : ℕ → ℝ) : ℝ :=
  {g | gapSegLen eps (Function.update g i x) = t}.indicator
    (fun g => testFn ψ (stopSum eps (Function.update g i x) / C)) g

theorem fluxOutputIntegrand_eq_partial (eps : ℝ) (ψ : ℝ → ℝ) (C : ℝ)
    (t i : ℕ) (x : ℝ) (g : ℕ → ℝ) :
    fluxOutputIntegrand eps ψ C t i x g =
      {g | gapSegLen eps (Function.update g i x) = t}.indicator
        (fun g => testFn ψ (gapKeys (Function.update g i x) t / C)) g := by
  by_cases hT : gapSegLen eps (Function.update g i x) = t
  · simp [fluxOutputIntegrand, hT, stopSum]
  · simp [fluxOutputIntegrand, hT]

theorem integrable_fluxOutputIntegrand {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (hit : i < t) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fluxOutputIntegrand eps ψ C t i x) (iidLaw ν) := by
  have he : fluxOutputIntegrand eps ψ C t i x =
      {g | gapSegLen eps (Function.update g i x) = t}.indicator
        (fun g => testFn ψ (gapKeys (Function.update g i x) t / C)) :=
    funext fun g => fluxOutputIntegrand_eq_partial eps ψ C t i x g
  rw [he]
  apply (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ hit hx).indicator
  exact (((isStoppingRule_gapSegLen eps).measurable).comp
    ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id))) (measurableSet_singleton (t : ℕ∞))

theorem fluxOutputIntegrand_norm_le {eps η M C x R : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) {t i : ℕ} (hit : i < t)
    (hx : x ∈ Icc (0 : ℝ) (max 0 R)) {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) :
    ‖fluxOutputIntegrand eps ψ C t i x g‖ ≤
      (M / η * Real.exp ((2 * η / C) * max 0 R)) *
        (winSet eps i t).indicator (fun g => Real.exp ((2 * η / C) * fluxUnmarkedSum t i g)) g := by
  have hM := hψ.nonneg'
  by_cases hT : gapSegLen eps (Function.update g i x) = t
  · have hiT : (i : ℕ∞) < gapSegLen eps (Function.update g i x) := by
      rw [hT]
      exact_mod_cast hit
    have hW := (mem_winSet_of_eq hT (lt_gapSegLen_update_iff.mp hiT)).1
    rw [fluxOutputIntegrand_eq_partial,
      indicator_of_mem (show g ∈ {g | gapSegLen eps (Function.update g i x) = t} from hT),
      indicator_of_mem hW, flux_gapKeys_update hit]
    exact (flux_testFn_shift_bounds hψ hη hC (fluxUnmarkedSum_nonneg_le hg t i).1 hx).1
  · rw [fluxOutputIntegrand, indicator_of_notMem
      (show g ∉ {g | gapSegLen eps (Function.update g i x) = t} from hT), norm_zero]
    by_cases hW : g ∈ winSet eps i t
    · rw [indicator_of_mem hW]
      positivity
    · rw [indicator_of_notMem hW, mul_zero]

theorem flux_output_piece_integral_norm_le {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C x R : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (hit : i < t) (hx : x ∈ Icc (0 : ℝ) (max 0 R)) :
    (∫ g, ‖fluxOutputIntegrand eps ψ C t i x g‖ ∂iidLaw ν) ≤
      (M / η * Real.exp ((2 * η / C) * max 0 R)) *
        ∫ g in winSet eps i t, Real.exp ((2 * η / C) * fluxUnmarkedSum t i g) ∂iidLaw ν := by
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
  rw [← integral_indicator (measurableSet_winSet eps i t), ← integral_const_mul]
  apply integral_mono_ae (integrable_fluxOutputIntegrand hν hθ eps hψ hη hC hηθ hit hx.1).norm
    ((hExp.indicator (measurableSet_winSet eps i t)).const_mul _)
  exact hgs.mono fun g hg => fluxOutputIntegrand_norm_le hψ hη hC hit hx (fun j => (hg j).le)

theorem flux_output_piece_norm_le {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C x R : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (hit : i < t) (hx : x ∈ Icc (0 : ℝ) (max 0 R)) :
    ‖fluxOutputPiece eps ν ψ C t i x‖ ≤
      (M / η * Real.exp ((2 * η / C) * max 0 R)) *
        ∫ g in winSet eps i t, Real.exp ((2 * η / C) * fluxUnmarkedSum t i g) ∂iidLaw ν :=
  (norm_integral_le_integral_norm (fluxOutputIntegrand eps ψ C t i x)).trans
    (flux_output_piece_integral_norm_le hν hθ eps hψ hη hC hηθ hit hx)

theorem fluxOutputPiece_zero {eps : ℝ} (heps : 1 ≤ eps) (ν : ProbabilityMeasure ℝ)
    (ψ : ℝ → ℝ) (C : ℝ) {t : ℕ} (ht : t < 3) (i : ℕ) (x : ℝ) :
    fluxOutputPiece eps ν ψ C t i x = 0 := by
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro g
  apply indicator_of_notMem
  intro hT
  have h3 := three_le_segLen heps (gapKeys (Function.update g i x))
  change (3 : ℕ∞) ≤ gapSegLen eps (Function.update g i x) at h3
  rw [hT] at h3
  have : 3 ≤ t := by exact_mod_cast h3
  omega

theorem flux_output_piece_primitive_bound_all {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) {eps : ℝ} (heps : 1 ≤ eps)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (hit : i < t) :
    ∃ j : ℝ → ℝ, AEPrimitive (fluxOutputPiece eps ν ψ C t i) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        (2 * ((|R| * (M / C) + 2 * (M / η)) * Real.exp ((2 * η / C) * max 0 R))) *
          ∫ g in winSet eps i t, Real.exp ((2 * η / C) * fluxUnmarkedSum t i g) ∂iidLaw ν := by
  by_cases ht : 3 ≤ t
  · exact flux_output_piece_primitive_bound hν hθ eps hψ hη hC hηθ ht hit
  · have ht3 : t < 3 := Nat.lt_of_not_ge ht
    have hM := hψ.nonneg'
    refine ⟨fun _ => 0, ⟨fun R => (integrable_zero _ _ _).intervalIntegrable, 0, ?_⟩, fun R => ?_⟩
    · exact Eventually.of_forall fun x => by simp [fluxOutputPiece_zero heps ν ψ C ht3]
    · simp only [norm_zero, integral_zero]
      apply mul_nonneg
      · positivity
      · exact integral_nonneg fun g => (Real.exp_pos _).le

end
end PGM
