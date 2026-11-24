import PLAStochastic.Index.KEP.Poisson.LayerObjects
import PLAStochastic.Index.KEP.PivotRestart

/-!
# Exact physical coordinates after a Poisson restart

Shifting the exponential innovations restarts the same physical arrival
sequence at its actual position. At every original endpoint pivot, the
shifted layer is exactly the original future layer. These identities are
pointwise and do not assume a probability comparison.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoissonKeys_shift {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) (g : ℕ → ℝ) (r k : ℕ) :
    kepPoissonKeys hf n (kepPoissonKeys hf n x g r) (fun i => g (r + i)) k =
      kepPoissonKeys hf n x g (r + k) := by
  unfold kepPoissonKeys
  rw [kepPoissonArrival_restart, gapKeys_shift]
  congr 1
  ring

theorem kepPoissonPairs_shift {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) (g : ℕ → ℝ) (r : ℕ) :
    kepPoissonPairs hf n (kepPoissonKeys hf n x g r) (fun i => g (r + i)) =
      fun i => kepPoissonPairs hf n x g (r + i) := by
  funext i
  unfold kepPoissonPairs
  rw [kepPoissonKeys_shift, kepPoissonKeys_shift, Nat.add_assoc]

theorem kepPoisson_pairLayer_restart {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (g : ℕ → ℝ) (j i : ℕ) :
    let r := layerPivot eps (kepPoissonPairs hf n x g) j i
    pairLayer eps j
      (kepPoissonPairs hf n (kepPoissonKeys hf n x g r) (fun k => g (r + k))) =
      fun k => pairLayer eps j (kepPoissonPairs hf n x g) (i + k) := by
  dsimp only
  rw [kepPoissonPairs_shift]
  exact pairLayer_shift_layerPivot (fun _ => rfl) j i

theorem kepPoisson_layer_gap_restart {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (g : ℕ → ℝ) (j i : ℕ) :
    let r := layerPivot eps (kepPoissonPairs hf n x g) j i
    let y := kepPoissonKeys hf n x g r
    (f x / f y) * kepPoissonLayerGap hf eps n y j (fun k => g (r + k)) =
      (n * f x / kepReferenceSpan eps j) *
        (pairLayer eps j (kepPoissonPairs hf n x g) i).1 := by
  dsimp only
  unfold kepPoissonLayerGap
  rw [kepPoisson_pairLayer_restart]
  simp only [Nat.add_zero]
  have he : (f x / f (kepPoissonKeys hf n x g
      (layerPivot eps (kepPoissonPairs hf n x g) j i))) *
      (n * f (kepPoissonKeys hf n x g
        (layerPivot eps (kepPoissonPairs hf n x g) j i)) / kepReferenceSpan eps j) =
      n * f x / kepReferenceSpan eps j := by
    field_simp [(hf.f_pos _).ne']
  rw [← mul_assoc, he]

end

end PGM
