import PLAStochastic.Index.GEP.Kernel.NearSlope.InsertionBlocks

/-!
# Exact signed insertion integrands for the original facet blocks

The original effective-facet gate is retained in the exterior reward. Both
contact orders therefore use the same actual coefficient as the insertion
estimates, including its physical stopped-sum argument.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem kernel_IF_left_block_signed_integrand (ν : ProbabilityMeasure ℝ)
    (f H : ℝ → ℝ) (w x a : ℝ) (u l r m v : ℕ) (σ : Bool) :
    (if kernelFacetEffective (w/2) (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 then
      kernelIFLeftSignedPinFactor ν f (w/2) x (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
        (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 a *
        ∫ g, kernelIFOuterSurvival (w/2) a (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 g *
          H (kernelIFPhysicalSum a (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 g) ∂iidLaw ν
      else 0) =
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r (if σ then 0 else w) (if σ then w else 0) *
        krInsertionCoefficientTerm ν f w σ σ (kernelIFInsertionReward H w σ σ) l r (u,m,v) a := by
  classical
  by_cases h : krInsertionEffective w σ l r m
  · have hE := (kernel_IF_left_block_effective w u l r m v σ).2 h
    rw [if_pos hE, kernel_IF_left_block_pin_factor]
    simp only [krInsertionCoefficientTerm, kernelIFInsertionReward, if_pos h]
    change _ = _ * (_ * _ * ∫ g,
      kernelIFOuterSurvival (w/2) a (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 g *
        H (kernelIFPhysicalSum a (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 g) ∂iidLaw ν)
    ring
  · have hE : ¬ kernelFacetEffective (w/2) (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 :=
      fun hE => h ((kernel_IF_left_block_effective w u l r m v σ).1 hE)
    simp [hE, krInsertionCoefficientTerm, kernelIFInsertionReward, h]

theorem kernel_IF_right_block_signed_integrand (ν : ProbabilityMeasure ℝ)
    (f H : ℝ → ℝ) (w x a : ℝ) (u l r m v : ℕ) (σ : Bool) :
    (if kernelFacetEffective (w/2) (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 then
      kernelIFRightSignedPinFactor ν f (w/2) x (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
        (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 a *
        ∫ g, kernelIFOuterSurvival (w/2) a (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 g *
          H (kernelIFPhysicalSum a (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 g) ∂iidLaw ν
      else 0) =
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r (if !σ then 0 else w) (if !σ then w else 0) *
        krInsertionCoefficientTerm ν f w (!σ) σ (kernelIFInsertionReward H w (!σ) σ)
          l r (u,m,v) a := by
  classical
  by_cases h : krInsertionEffective w (!σ) l r m
  · have hE := (kernel_IF_right_block_effective w u l r m v σ).2 h
    rw [if_pos hE, kernel_IF_right_block_pin_factor]
    simp only [krInsertionCoefficientTerm, kernelIFInsertionReward, if_pos h]
    simp_rw [kernel_IF_right_block_outer_eq, kernel_IF_right_block_physical_eq]
    ring
  · have hE : ¬ kernelFacetEffective (w/2) (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 :=
      fun hE => h ((kernel_IF_right_block_effective w u l r m v σ).1 hE)
    simp [hE, krInsertionCoefficientTerm, kernelIFInsertionReward, h]

end
end PGM
