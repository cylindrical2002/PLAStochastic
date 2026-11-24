import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopePins
import PLAStochastic.Index.GEP.Kernel.Insertion.Rewards

/-! # Original left and right block coordinates in the actual insertion coefficient -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1400000

def kernelIFInsertionReward (H : ℝ → ℝ) (w : ℝ) (up outerUp : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) (g : ℕ → ℝ) : ℝ := by
  classical
  exact if krInsertionEffective w up l r t.2.1 then
    H (kernelIFPhysicalSum a (kernelIFLeftOfBlocks (t.1,l,r,t.2.1,t.2.2,outerUp)).1.2.2 g)
  else 0

theorem kernel_IF_insertion_scalar_reward (C w : ℝ) (up outerUp : Bool) :
    kernelIFInsertionReward (fun _ => 1/C) w up outerUp = krInsertionScalarReward C w up := by
  funext l r t a g
  rfl

theorem kernel_IF_insertion_output_reward (ν : ProbabilityMeasure ℝ) (C : ℝ)
    (ψ : ℝ → ℝ) (w : ℝ) (up outerUp : Bool) :
    kernelIFInsertionReward (kernelPositiveBoundaryReward ν C ψ) w up outerUp =
      krInsertionOutputReward ν C ψ w up outerUp := rfl

theorem kernel_IF_left_block_effective (w : ℝ) (u l r m v : ℕ) (σ : Bool) :
    kernelFacetEffective (w/2) (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 ↔
      krInsertionEffective w σ l r m := by
  have hvalid := (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).2.1
  unfold kernelFacetEffective
  rw [and_iff_right hvalid]
  cases σ <;>
    simp only [kernelIFLeftOfBlocks, fluxFacetSign, krInsertionEffective,
      krInsertionOtherFactor, Bool.false_eq_true, if_false, if_true,
      Nat.cast_add, Nat.cast_one]
  all_goals constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem kernel_IF_right_block_effective (w : ℝ) (u l r m v : ℕ) (σ : Bool) :
    kernelFacetEffective (w/2) (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 ↔
      krInsertionEffective w (!σ) l r m := by
  have hvalid := (kernelIFRightOfBlocks (u,l,r,m,v,σ)).2.1
  unfold kernelFacetEffective
  rw [and_iff_right hvalid]
  cases σ <;>
    simp only [kernelIFRightOfBlocks, fluxFacetSign, krInsertionEffective,
      krInsertionOtherFactor, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      if_false, if_true, Nat.cast_add, Nat.cast_one]
  all_goals constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem kernel_IF_right_block_outer_eq (w a : ℝ) (u l r m v : ℕ) (σ : Bool) (g : ℕ → ℝ) :
    kernelIFOuterSurvival (w/2) a (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 g =
      krInsertionOuter w σ l r (u,m,v) a g := by
  have ht : u+(m+1)+(l+r+1) = u+(l+r+1)+(m+1) := by omega
  simp only [kernelIFOuterSurvival, kernelIFRightOfBlocks, krInsertionOuter, kernelIFLeftOfBlocks,
    fluxFacetSign, ht]
  rfl

theorem kernel_IF_right_block_physical_eq (a : ℝ) (u l r m v : ℕ) (σ : Bool) (g : ℕ → ℝ) :
    kernelIFPhysicalSum a (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 g =
      kernelIFPhysicalSum a (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 g := by
  have ht : u+(m+1)+(l+r+1) = u+(l+r+1)+(m+1) := by omega
  simp only [kernelIFPhysicalSum, kernelIFRightOfBlocks, kernelIFLeftOfBlocks, ht]

theorem kernel_IF_left_block_pin_factor (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w x a : ℝ) (u l r m v : ℕ) (σ : Bool) :
    kernelIFLeftSignedPinFactor ν f (w/2) x (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 a =
      krInsertionOtherFactor w σ m *
        krDens (Icc 0 w) ν f 1 a (m+1) (if σ then w else 0) (if σ then 0 else w) *
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r (if σ then 0 else w) (if σ then w else 0) := by
  have hw : 2*(w/2)=w := by ring
  have h1 : u+l-u=l := by omega
  have h2 : u+(l+r+1)-(u+l)-1=r := by omega
  have h3 : u+(l+r+1)+(m+1)-(u+(l+r+1))=m+1 := by omega
  cases σ <;> simp only [kernelIFLeftSignedPinFactor, kernelIFLeftOfBlocks,
    krInsertionOtherFactor, kernelFacetQ, fluxFacetSign, Bool.false_eq_true,
    if_false, if_true, h1, h2, h3, hw, Nat.cast_add, Nat.cast_one]
  all_goals ring_nf

theorem kernel_IF_right_block_pin_factor (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w x a : ℝ) (u l r m v : ℕ) (σ : Bool) :
    kernelIFRightSignedPinFactor ν f (w/2) x (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 a =
      krInsertionOtherFactor w (!σ) m *
        krDens (Icc 0 w) ν f 1 a (m+1) (if !σ then w else 0) (if !σ then 0 else w) *
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r (if !σ then 0 else w) (if !σ then w else 0) := by
  have hw : 2*(w/2)=w := by ring
  have h1 : u+(m+1)-u=m+1 := by omega
  have h2 : u+(m+1)+l-(u+(m+1))=l := by omega
  have h3 : u+(m+1)+(l+r+1)-(u+(m+1)+l)-1=r := by omega
  cases σ <;> simp only [kernelIFRightSignedPinFactor, kernelIFRightOfBlocks,
    krInsertionOtherFactor, kernelFacetP, fluxFacetSign, Bool.false_eq_true,
    Bool.not_false, Bool.not_true, if_false, if_true, h1, h2, h3, hw, Nat.cast_add, Nat.cast_one]
  all_goals ring_nf

end
end PGM
