import PLAStochastic.Affine.Extrema.Density.DensityMeasure
import PLAStochastic.Affine.Extrema.Density.Reflection

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The other time order interchanges the two inward boundary labels. -/
def reverseOrderedExtremaDensity (p : ExtremaVector) : ℝ :=
  heatBoundaryRight (p.2.1-p.1) p.2.2.2.1 (-p.1) *
    heatCrossBoundary (p.2.1-p.1) (p.2.2.1-p.2.2.2.1) *
    heatBoundaryLeft (p.2.1-p.1) (1-p.2.2.1) (p.2.2.2.2-p.1) / 4

theorem orderedExtremaDensity_reflection {p : ExtremaVector}
    (hp : p ∈ reverseOrderedExtremaDomain) :
    orderedExtremaDensity (extremaReflection p)=reverseOrderedExtremaDensity p := by
  have hr : p.2.1-p.1 ≠ 0 := ne_of_gt (by linarith [hp.1,hp.2.1])
  unfold orderedExtremaDensity orderedContactDensityKernel extremaReflection reverseOrderedExtremaDensity
  simp only [neg_sub_neg,neg_neg]
  rw [heatBoundaryRight_reflection hr,heatBoundaryRight_reflection hr]
  rw [show 1-p.2.2.2.1-(p.2.2.1-p.2.2.2.1)=1-p.2.2.1 by ring,
    show p.2.1-p.1-(p.2.1-p.2.2.2.2)=p.2.2.2.2-p.1 by ring,
    show p.2.1-p.1-(-p.1)=p.2.1 by ring]

/-- The full five-variable density retains both time orders and vanishes elsewhere. -/
def brownianExtremaDensity (p : ExtremaVector) : ℝ :=
  orderedExtremaDomain.indicator orderedExtremaDensity p+
    reverseOrderedExtremaDomain.indicator reverseOrderedExtremaDensity p

def reverseOrderedExtremaDensityMeasure : Measure ExtremaVector :=
  (volume.withDensity (fun p => ENNReal.ofReal (reverseOrderedExtremaDensity p))).restrict
    reverseOrderedExtremaDomain

end BrownianAffine
