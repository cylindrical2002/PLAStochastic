import PLAStochastic.Index.CEPS.Band.Actual
import PLAStochastic.Index.CEPS.Band.Interpolation

/-!
# Fixed-drift killed-band budgets for P-CEPS

`Decay` and `Moments` give uniform survival and pointwise density budgets at
arbitrary drift, hence on every fixed drift window. `Actual` exposes the strip,
bridge, and marked-bridge consequences. `WidthDeriv` gives genuine first width
derivatives; `SecondWidth` gives `C¹,¹` control and genuine almost-everywhere
second width derivatives; `Interpolation` supplies the derivative upgrade
without an assumption of pointwise classical second differentiability.

The slightly growing complex discount is explicit: `Re q ≥ -κ/(16w²)` for
time moments, and `Re q ≥ -κ/(64w²)` for the closed-window width budgets.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory

/-- The pointwise density representative used by the band budgets is supplied by `RegLaw`. -/
theorem cepsBand_regLaw_density {D θ vlo vhi : ℝ} (hθ : 0 < θ)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    ∃ f : ℝ → ℝ, CepsGapDensity ν f D := hν.exists_cepsGapDensity hθ.le

end
end PGM
