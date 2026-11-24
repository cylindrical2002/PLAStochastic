import PLAStochastic.Index.GEP.Universality.GaussianWalkComparison
import PLAStochastic.Index.GEP.Universality.OfStrongApprox
import PLAStochastic.Brownian.Construction.ContinuousVersion

/-!
# WP5: discharge the Brownian lifetime interface

The canonical Brownian motion supplies the actual lifetime law, its exponential
moment and both Gaussian-walk comparisons. The one-layer universality rate
therefore has only the class-uniform strong approximation left as an input.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine

/-- The actual unit-tolerance optimal lifetime law of the canonical Brownian motion. -/
def brownianLifetimeLaw : Measure ℝ :=
  canonicalPreBrownianMeasure.map (optimalUnitLifetime canonicalBrownian)

/-- The Brownian side of WP5, with no Brownian-process or moment hypotheses. -/
theorem brownian_lifetimeSide : ∃ θτ Eτ : ℝ, LifetimeSide brownianLifetimeLaw θτ Eτ := by
  have hB := isBrownianReal_canonicalBrownian
  obtain ⟨θ, E, hθ, hE⟩ := brownian_lifetime_exp_moment hB
  obtain ⟨hprob, hnonneg⟩ := brownian_lifetime_law hB
  refine ⟨θ, E, ?_⟩
  exact {
    prob := hprob
    nonneg := hnonneg
    θpos := hθ
    expMom := hE
    walk_le := brownian_walk_le hB
    walk_ge := brownian_walk_ge hB
  }

/-- Only the class-uniform strong approximation remains in the WP5 universality proof. -/
theorem universality_of_SA
    (hSA : ∀ vlo vhi κ₃ B θ D c₀ : ℝ, 0 < vlo → vlo ≤ vhi → 0 < θ → 0 < c₀ →
      StrongApproxClass vlo vhi κ₃ B θ D c₀) : GEPUniversality := by
  obtain ⟨θ, E, hL⟩ := brownian_lifetimeSide
  exact universality_of_SA_lifetime hSA hL

end

end PGM
