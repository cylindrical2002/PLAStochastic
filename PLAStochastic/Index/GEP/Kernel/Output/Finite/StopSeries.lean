import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopTriangle

/-!
# The exact stopping-time series of the original insertion kernel

The expansion is proved with absolute integral summability on the actual
triangle `i < t`. The original unmodified insertion event and stopped reward
are retained throughout the Fubini and reindexing steps.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

def fluxOutputTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) (C : ℝ)
    (a : ℕ × ℕ) (x : ℝ) : ℝ :=
  if a.2 < a.1 then fluxOutputPiece eps ν ψ C a.1 a.2 x else 0

def fluxOutputTermIntegrand (eps : ℝ) (ψ : ℝ → ℝ) (C : ℝ)
    (a : ℕ × ℕ) (x : ℝ) (g : ℕ → ℝ) : ℝ :=
  if a.2 < a.1 then fluxOutputIntegrand eps ψ C a.1 a.2 x g else 0

theorem fluxOutputTerm_eq_integral (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (ψ : ℝ → ℝ) (C : ℝ) (a : ℕ × ℕ) (x : ℝ) :
    fluxOutputTerm eps ν ψ C a x = ∫ g, fluxOutputTermIntegrand eps ψ C a x g ∂iidLaw ν := by
  by_cases ha : a.2 < a.1
  · simp only [fluxOutputTerm, fluxOutputTermIntegrand, ha, if_true]
    rfl
  · simp only [fluxOutputTerm, fluxOutputTermIntegrand, ha, if_false, integral_zero]

theorem flux_output_integrand_tsum (eps : ℝ) (ψ : ℝ → ℝ) (C : ℝ) (i : ℕ) (x : ℝ)
    (g : ℕ → ℝ) (hfin : gapSegLen eps (Function.update g i x) ≠ ⊤) :
    (∑' t : ℕ, fluxOutputTermIntegrand eps ψ C (t, i) x g) =
      {g | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => testFn ψ (stopSum eps (Function.update g i x) / C)) g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hT : gapSegLen eps (Function.update g i x) = n := hn.symm
  have hi : (i : ℕ∞) < gapSegLen eps g ↔ i < n := by
    rw [← lt_gapSegLen_update_iff (x := x), hT]
    exact Nat.cast_lt
  rw [tsum_eq_single n]
  · simp only [fluxOutputTermIntegrand, fluxOutputIntegrand,
      indicator_of_mem (show g ∈ {g | gapSegLen eps (Function.update g i x) = n} from hT),
      indicator_apply, mem_ofPred_eq, hi]
  · intro t ht
    have hTt : gapSegLen eps (Function.update g i x) ≠ t := by
      rw [hT]
      exact_mod_cast Ne.symm ht
    simp [fluxOutputTermIntegrand, fluxOutputIntegrand, hTt]

theorem flux_output_terms_integral_norm_summable {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) (hWin : Summable (fluxWindowMoment eps ν (2 * η / C)))
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun a : ℕ × ℕ => ∫ g, ‖fluxOutputTermIntegrand eps ψ C a x g‖ ∂iidLaw ν) := by
  refine Summable.of_nonneg_of_le (fun a => integral_nonneg fun g => norm_nonneg _) ?_
    (hWin.mul_left (M / η * Real.exp ((2 * η / C) * max 0 x)))
  intro a
  by_cases ha : a.2 < a.1
  · simp only [fluxOutputTermIntegrand, fluxWindowMoment, ha, if_true]
    exact flux_output_piece_integral_norm_le hν hθ eps hψ hη hC hηθ ha ⟨hx, le_max_right _ _⟩
  · simp only [fluxOutputTermIntegrand, fluxWindowMoment, ha, if_false, norm_zero, integral_zero,
      mul_zero, le_refl]

set_option maxHeartbeats 800000 in
theorem flux_output_terms_eq_insKernel {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) (hWin : Summable (fluxWindowMoment eps ν (2 * η / C)))
    (hfin : ∀ᵐ g ∂iidLaw ν, gapSegLen eps g ≠ ⊤) {x : ℝ} (hx : 0 ≤ x) :
    (∑' a : ℕ × ℕ, fluxOutputTerm eps ν ψ C a x) =
      insKernel eps ν (fun g => testFn ψ (stopSum eps g / C)) x := by
  have hnorm := flux_output_terms_integral_norm_summable hν hθ eps hψ hη hC hηθ hWin hx
  have hI (a : ℕ × ℕ) : Integrable (fluxOutputTermIntegrand eps ψ C a x) (iidLaw ν) := by
    change Integrable (fun g => fluxOutputTermIntegrand eps ψ C a x g) (iidLaw ν)
    by_cases ha : a.2 < a.1
    · simpa only [fluxOutputTermIntegrand, ha, if_true] using
        integrable_fluxOutputIntegrand hν hθ eps hψ hη hC hηθ ha hx
    · simpa only [fluxOutputTermIntegrand, ha, if_false] using
        (integrable_const (0 : ℝ) (μ := iidLaw ν))
  have hs : Summable (fun a : ℕ × ℕ => fluxOutputTerm eps ν ψ C a x) :=
    hnorm.of_norm_bounded fun a => by
      rw [fluxOutputTerm_eq_integral]
      exact norm_integral_le_integral_norm _
  calc
    _ = ∑' t : ℕ, ∑' i : ℕ, fluxOutputTerm eps ν ψ C (t, i) x := hs.tsum_prod
    _ = ∑' i : ℕ, ∑' t : ℕ, fluxOutputTerm eps ν ψ C (t, i) x := hs.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro i
      simp_rw [fluxOutputTerm_eq_integral]
      rw [integral_tsum_of_summable_integral_norm (fun t => hI (t, i)) (hnorm.prod_symm.prod_factor i)]
      apply integral_congr_ae
      filter_upwards [ae_gapSegLen_update_ne_top hfin i x] with g hg
      exact flux_output_integrand_tsum eps ψ C i x g hg

end
end PGM
