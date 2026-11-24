import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Root
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Centered

/-!
# Esscher tilt for the Wiener--Hopf library

Probability laws, explicit tilted envelopes and moments, finite-prefix changes
of measure, ascending and descending ladder transform identities, recentering,
and the differentiated root identity `m₊ (1 - p₋) = ψ'(β)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM.WienerHopf

namespace IsStepLaw

variable {ρ : Measure ℝ} {f : ℝ → ℝ} {D θ v : ℝ}

/-- Recenter the tilted law and expose it through the existing `IsStepLaw` API. -/
theorem esscher_centered (h : IsStepLaw ρ f D θ v) (hD : 0 ≤ D) (hθ : 0 < θ)
    {β q : ℝ} (hβ : |β| ≤ θ / 2) (hq : 0 ≤ q)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    IsStepLaw (driftStep (esscherLaw ρ β) (-deriv (cgf id ρ) β))
      (fun y => Real.exp (β * (y + deriv (cgf id ρ) β) - q) *
        f (y + deriv (cgf id ρ) β))
      (D * Real.exp (θ / 2 * |deriv (cgf id ρ) β|)) (θ / 2)
      (2 * (256 * D / θ ^ 3) + 2 * (deriv (cgf id ρ) β) ^ 2) :=
  (h.esscher hD hθ hβ hq hroot).centered hD (by positivity)

/-- The root mean identity for the small-drift step class used by CEPS.
No separate hypotheses on the masses of the two half-lines are needed. -/
theorem esscher_drift_root_mean (h : IsStepLaw ρ f D θ v)
    (hD : 0 < D) (hθ : 0 < θ) (hv : 0 < v)
    {μ δ β q : ℝ} (hμ : |μ| ≤ δ) (hδ : δ ≤ 1 / (64 * D))
    (hβ : 0 ≤ β) (hβθ : β ≤ θ / 2) (hq : 0 < q)
    (hroot : (∫ y, Real.exp (β * y) ∂driftStep ρ μ) = Real.exp q) :
    entryMean (esscherLaw (driftStep ρ μ) β) (Ioi 0) *
      (1 - expEntryMass (esscherLaw (driftStep ρ μ) β) (Iic 0) 0) =
        deriv (cgf id (driftStep ρ μ)) β := by
  have := h.isProbabilityMeasure
  have hm := driftStep_masses h hθ.le hD hv hμ hδ
  have hb : 0 < 1 / (64 * D) := by positivity
  have hmass : 0 < 1 / (1024 * D ^ 2 * v) := by positivity
  have hl : 0 < driftStep ρ μ (Iio 0) := by
    by_contra hn
    have hz : driftStep ρ μ (Iio 0) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hz' : (driftStep ρ μ).real (Iio 0) = 0 := by simp [measureReal_def, hz]
    have hs : Iic (-(1 / (64 * D))) ⊆ Iio (0 : ℝ) := fun _ hx => by
      simp only [mem_Iic, mem_Iio] at hx ⊢
      linarith
    have he := measureReal_mono (μ := driftStep ρ μ) hs
    linarith [hm.1]
  have hr : 0 < driftStep ρ μ (Ioi 0) := by
    by_contra hn
    have hz : driftStep ρ μ (Ioi 0) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hz' : (driftStep ρ μ).real (Ioi 0) = 0 := by simp [measureReal_def, hz]
    have hs : Ici (1 / (64 * D)) ⊆ Ioi (0 : ℝ) := fun _ hx => by
      simp only [mem_Ici, mem_Ioi] at hx ⊢
      linarith
    have he := measureReal_mono (μ := driftStep ρ μ) hs
    linarith [hm.2]
  exact esscher_entryMean_mul_one_sub_descMass (a := 3 * θ / 4) (by positivity)
    (integrable_exp_driftStep ρ μ _ (h.integrable_exp_of_abs_lt hD.le
      (by rw [abs_of_pos (by positivity)]; linarith)))
    (integrable_exp_driftStep ρ μ _ (h.integrable_exp_of_abs_lt hD.le
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)))
    hl hr hβ (by linarith) hq hroot

end IsStepLaw

end PGM.WienerHopf
