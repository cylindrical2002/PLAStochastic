import PLAStochastic.Index.KEP.Poisson.CompletedStopping
import PLAStochastic.Index.KEP.PivotRestart

/-!
# Finite height is read by the completed pivot of the actual process

A finite prefix is compared with its zero-tail truncation. The original
height/pivot equivalence then identifies the event directly with the
completed extended-natural pivot, without assuming finite future layers.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem epHeight_le_iff_completedPivot {eps : ℝ} (heps : 1 / 2 ≤ eps)
    (z : ℕ → ℝ × ℕ) (x : ℝ) (N : ℕ) {ell : ℕ} (hell : 1 ≤ ell) :
    epHeight eps (fun t => x + pairKeys z t) (N + 1) ≤ ell ↔
      (N : ℕ∞) < completedPivot eps z ell 1 := by
  have hh : epHeight eps (fun t => x + pairKeys z t) (N + 1) =
      epHeight eps (fun t => x + pairKeys (truncPairs z N) t) (N + 1) := by
    apply epHeight_congr
    intro i hi
    rw [pairKeys_truncPairs z N i (by omega)]
  rw [hh, epHeight_le_iff_layerPivot heps (truncPairs_snd z N)
    (allLayersFinite_truncPairs eps z N) x (by omega) hell, completedPivot_lt_iff]
  omega

theorem kepPoisson_height_le_iff_completedPivot {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {eps : ℝ} (heps : 1 / 2 ≤ eps)
    (n x : ℝ) (g : ℕ → ℝ) (N : ℕ) {ell : ℕ} (hell : 1 ≤ ell) :
    epHeight eps (kepPoissonKeys hf n x g) (N + 1) ≤ ell ↔
      (N : ℕ∞) < kepPoissonPivot hf eps n x ell 1 g := by
  have hh : epHeight eps (kepPoissonKeys hf n x g) (N + 1) =
      epHeight eps (fun t => x + pairKeys (kepPoissonPairs hf n x g) t) (N + 1) := by
    apply epHeight_congr
    intro i _
    rw [pairKeys_kepPoissonPairs]
    ring
  rw [hh]
  exact epHeight_le_iff_completedPivot heps (kepPoissonPairs hf n x g) x N hell

end

end PGM
