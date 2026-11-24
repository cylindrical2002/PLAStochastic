import PLAStochastic.Index.KEP.Poisson.LayerSequence
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import PLAStochastic.Index.KEP.GapWindowSurvival

/-!
# The whole actual Poisson child sequence after a finite completed restart

The original future child sequence restarts at its physical anchor. Its
only change of units is the actual intensity ratio, so greedy stopping
events are exactly invariant under that ratio.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoissonLayerSequence_restart {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j i g ≠ ⊤) :
    (fun k => kepPoissonLayerSequence hf eps n x j g (i + k)) =
      fun k => (f x / f (kepPoissonPivotAnchor hf eps n x j i g)) *
        kepPoissonLayerSequence hf eps n (kepPoissonPivotAnchor hf eps n x j i g) j
          (shiftBy (kepPoissonPivot hf eps n x j i) g) k := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hr' : kepPoissonPivot hf eps n x j i g = (r : ℕ∞) := hr.symm
  have horig := kepPoissonPivot_eq_original_of_finite hf hr'
  have hshift : shiftBy (kepPoissonPivot hf eps n x j i) g = fun k => g (r + k) := by
    funext k
    change g ((kepPoissonPivot hf eps n x j i g).toNat + k) = g (r + k)
    rw [hr', ENat.toNat_natCast]
  have hD : kepPoissonPivotAnchor hf eps n x j i g = kepPoissonKeys hf n x g r := by
    simp only [kepPoissonPivotAnchor, kepPoissonStoppedAnchor, hr', ENat.toNat_natCast]
  have hl := kepPoisson_pairLayer_restart hf eps n x g j i
  dsimp only at hl
  rw [horig] at hl
  funext k
  simp only [kepPoissonLayerSequence, hD, hshift, hl]
  field_simp [(hf.f_pos (kepPoissonKeys hf n x g r)).ne']

theorem kepPoissonLayerSequence_restart_stop {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j i g ≠ ⊤) :
    gapSegLen eps (fun k => kepPoissonLayerSequence hf eps n x j g (i + k)) =
      gapSegLen eps (kepPoissonLayerSequence hf eps n
        (kepPoissonPivotAnchor hf eps n x j i g) j
        (shiftBy (kepPoissonPivot hf eps n x j i) g)) := by
  rw [kepPoissonLayerSequence_restart hf hfin]
  exact gapSegLen_const_mul eps _ (div_ne_zero (hf.f_pos x).ne' (hf.f_pos _).ne')

theorem kepPoissonLayerSequence_survival_restart {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps n x : ℝ} {j i M : ℕ} {g : ℕ → ℝ}
    (hfin : kepPoissonPivot hf eps n x j i g ≠ ⊤)
    (hsurv : ((i + M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)) :
    (M : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n
      (kepPoissonPivotAnchor hf eps n x j i g) j
      (shiftBy (kepPoissonPivot hf eps n x j i) g)) := by
  rw [← kepPoissonLayerSequence_restart_stop hf hfin]
  exact gapSegLen_window_survival hsurv

end

end PGM
