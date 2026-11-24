import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputBlocks
import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopeMass

/-! # Actual output block majorants restricted to an arbitrary slope set -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1600000

def kernelWeightedBulkBlockOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ)
    (S : Set ℝ) (u l h m v : ℕ) : ℝ≥0∞ :=
  ∫⁻ a in S, ENNReal.ofReal
    (kernelPhysicalOuterPairAt ν w s a u v * (((m : ℝ)+1+w) *
      (Real.exp (s*((l : ℝ)+h+m+2)/a) * kernelPairBoth ν f w a x l h m)))
    ∂volume.restrict (Ioi (0 : ℝ))

def kernelWeightedBlockMajorantOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ)
    (S : Set ℝ) (p : KernelIFBlockIndex) : ℝ≥0∞ :=
  kernelWeightedBulkBlockOn ν f w s x S p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 +
    if p.2.1 = 0 ∧ p.2.2.1 = 0 then kernelWeightedDiracBlock ν f w s x p.1 p.2.2.2.1 p.2.2.2.2.1 else 0

theorem kernel_IF_left_output_bulk_on_le {D θ vlo vhi η M C eps : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 0 ≤ eps)
    (S : Set ℝ) (x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFLeftTotalPinDensityOn ν f eps S (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBulkBlockOn ν f (2*eps) (η/C) x S u l h m v := by
  unfold kernelIFLeftTotalPinDensityOn kernelWeightedBulkBlockOn
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioi)] with a ha
  have hb := kernel_IF_left_output_outer_le (eps := eps) hν hθ hψ hη hC hscale ha u l h m v σ
  apply (mul_le_mul' le_rfl (mul_le_mul' hb le_rfl)).trans
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hq : (m : ℝ)+1+2*(if σ then 1 else -1)*eps ≤ (m : ℝ)+1+2*eps := by
    cases σ <;> norm_num
    linarith
  have hh := kernel_output_bulk_integrand_le ν hf0 (s := η/C) (a := a) (x := x)
    (show 0 ≤ 2*eps by positivity) (show 0 ≤ M*(8*D/θ^2)/C by positivity)
    u l h m v hq
    (show (if σ then 0 else 2*eps) = 0 ∨ (if σ then 0 else 2*eps) = 2*eps by cases σ <;> simp)
    (show ((if σ then 0 else 2*eps) = 0 ∧ (if σ then 2*eps else 0) = 2*eps) ∨
      ((if σ then 0 else 2*eps) = 2*eps ∧ (if σ then 2*eps else 0) = 0) by cases σ <;> simp)
  have h₁ : u+l-u=l := by omega
  have h₂ : u+(l+h+1)-(u+l)-1=h := by omega
  have h₃ : u+(l+h+1)+(m+1)-(u+(l+h+1))=m+1 := by omega
  have hc : (u : ℝ)+(l+h+1)+(m+1)-((u : ℝ)+(l+h+1))=(m : ℝ)+1 := by ring
  cases σ <;> simpa only [kernelIFLeftOfBlocks, kernelFacetQ, fluxFacetSign,
    Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul, sub_self,
    h₁, h₂, h₃, Nat.cast_add, Nat.cast_one, hc,
    show eps - -eps = 2*eps by ring, show eps + -eps = 0 by ring,
    show eps + eps = 2*eps by ring] using hh

theorem kernel_IF_right_output_bulk_on_le {D θ vlo vhi η M C eps : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 0 ≤ eps)
    (S : Set ℝ) (x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFRightTotalPinDensityOn ν f eps S (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBulkBlockOn ν f (2*eps) (η/C) x S u l h m v := by
  unfold kernelIFRightTotalPinDensityOn kernelWeightedBulkBlockOn
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioi)] with a ha
  have hb := kernel_IF_right_output_outer_le (eps := eps) hν hθ hψ hη hC hscale ha u l h m v σ
  apply (mul_le_mul' le_rfl (mul_le_mul' hb le_rfl)).trans
  rw [mul_comm (ENNReal.ofReal (krDens _ _ _ _ _ _ _ _)) (ENNReal.ofReal (kernelMarkedFullDens _ _ _ _ _ _ _ _ _ _))]
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hq : (m : ℝ)+1-2*(if σ then 1 else -1)*eps ≤ (m : ℝ)+1+2*eps := by
    cases σ <;> norm_num
    linarith
  have hh := kernel_output_bulk_integrand_le ν hf0 (s := η/C) (a := a) (x := x)
    (show 0 ≤ 2*eps by positivity) (show 0 ≤ M*(8*D/θ^2)/C by positivity)
    u l h m v hq
    (show (if σ then 0 else 2*eps) = 0 ∨ (if σ then 0 else 2*eps) = 2*eps by cases σ <;> simp)
    (show ((if σ then 2*eps else 0) = 0 ∧ (if σ then 0 else 2*eps) = 2*eps) ∨
      ((if σ then 2*eps else 0) = 2*eps ∧ (if σ then 0 else 2*eps) = 0) by cases σ <;> simp)
  have h₁ : u+(m+1)+l-(u+(m+1))=l := by omega
  have h₂ : u+(m+1)+(l+h+1)-(u+(m+1)+l)-1=h := by omega
  have h₃ : u+(m+1)-u=m+1 := by omega
  have hc : (u : ℝ)+(m+1)-u=(m : ℝ)+1 := by ring
  cases σ <;> simpa only [kernelIFRightOfBlocks, kernelFacetP, fluxFacetSign,
    Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul, sub_self,
    h₁, h₂, h₃, Nat.cast_add, Nat.cast_one, hc,
    show eps - -eps = 2*eps by ring, show eps + -eps = 0 by ring,
    show eps + eps = 2*eps by ring] using hh


theorem kernel_IF_left_dirac_on_le (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFLeftTotalDiracPinDensityOn ν f eps S q H x ≤
      kernelIFLeftTotalDiracPinDensity ν f eps q H x := by
  unfold kernelIFLeftTotalDiracPinDensityOn
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem kernel_IF_right_dirac_on_le (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFRightTotalDiracPinDensityOn ν f eps S q H x ≤
      kernelIFRightTotalDiracPinDensity ν f eps q H x := by
  unfold kernelIFRightTotalDiracPinDensityOn
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem kernel_IF_left_output_block_on_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 1 ≤ eps)
    (hx : 0 < x) (S : Set ℝ) (p : KernelIFBlockIndex) :
    kernelIFFacetTotalPinDensityOn ν f eps S (kernelIFLeftOfBlocks p).1.2.2
      (kernelIFLeftOfBlocks p).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBlockMajorantOn ν f (2*eps) (η/C) x S p := by
  classical
  rcases p with ⟨u,l,h,m,v,σ⟩
  let q := (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
  let i : ℕ := (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1
  change kernelIFFacetTotalPinDensityOn ν f eps S q i (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤ _
  unfold kernelIFFacetTotalPinDensityOn
  by_cases heff : kernelFacetEffective eps q
  · rw [if_pos heff, if_pos (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).2.2]
    by_cases hlong : (q.1 : ℕ)+1 < q.2.1
    · rw [if_pos hlong]
      exact (kernel_IF_left_output_bulk_on_le hν hθ hψ hη hC hscale hf0 (by linarith) S x u l h m v σ).trans (mul_le_mul' le_rfl le_self_add)
    · rw [if_neg hlong]
      have hl : l = 0 := by dsimp [q, kernelIFLeftOfBlocks] at hlong; omega
      have hh : h = 0 := by dsimp [q, kernelIFLeftOfBlocks] at hlong; omega
      subst l h
      cases σ
      · exact ((kernel_IF_left_dirac_on_le ν f eps S q _ x).trans
          (kernel_IF_left_output_dirac_le hν hθ hψ hη hC hscale hf0 (by linarith) hx u m v)).trans
          (by simp only [kernelWeightedBlockMajorantOn, and_self, if_true]; exact mul_le_mul' le_rfl le_add_self)
      · have hp := heff.2.1
        dsimp [q, kernelIFLeftOfBlocks, fluxFacetSign] at hp
        push_cast at hp
        linarith
  · rw [if_neg heff]
    exact bot_le


theorem kernel_IF_right_output_block_on_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 1 ≤ eps)
    (hx : 0 < x) (S : Set ℝ) (p : KernelIFBlockIndex) :
    kernelIFFacetTotalPinDensityOn ν f eps S (kernelIFRightOfBlocks p).1.2.2
      (kernelIFRightOfBlocks p).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBlockMajorantOn ν f (2*eps) (η/C) x S p := by
  classical
  rcases p with ⟨u,l,h,m,v,σ⟩
  let q := (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
  let i : ℕ := (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1
  have hnotleft : ¬((q.1 : ℕ) ≤ i ∧ i < q.2.1) := by
    dsimp [q, i, kernelIFRightOfBlocks]
    omega
  change kernelIFFacetTotalPinDensityOn ν f eps S q i (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤ _
  unfold kernelIFFacetTotalPinDensityOn
  by_cases heff : kernelFacetEffective eps q
  · rw [if_pos heff, if_neg hnotleft, if_pos (kernelIFRightOfBlocks (u,l,h,m,v,σ)).2.2]
    by_cases hlong : (q.2.1 : ℕ)+1 < q.2.2.1
    · rw [if_pos hlong]
      exact (kernel_IF_right_output_bulk_on_le hν hθ hψ hη hC hscale hf0 (by linarith) S x u l h m v σ).trans (mul_le_mul' le_rfl le_self_add)
    · rw [if_neg hlong]
      have hl : l = 0 := by dsimp [q, kernelIFRightOfBlocks] at hlong; omega
      have hh : h = 0 := by dsimp [q, kernelIFRightOfBlocks] at hlong; omega
      subst l h
      cases σ
      · have hp := heff.2.2
        dsimp [q, kernelIFRightOfBlocks, fluxFacetSign] at hp
        push_cast at hp
        linarith
      · exact ((kernel_IF_right_dirac_on_le ν f eps S q _ x).trans
          (kernel_IF_right_output_dirac_le hν hθ hψ hη hC hscale hf0 (by linarith) hx u m v)).trans
          (by simp only [kernelWeightedBlockMajorantOn, and_self, if_true]; exact mul_le_mul' le_rfl le_add_self)
  · rw [if_neg heff]
    exact bot_le

end
end PGM
