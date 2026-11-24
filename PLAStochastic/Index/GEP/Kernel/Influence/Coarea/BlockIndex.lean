import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.OneGapPrimitive
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Exact reindexing of original facets by the four physical block lengths -/

namespace PGM
noncomputable section
open scoped ENNReal

/-- Original finite-prefix facet with its mark in the first bridge. -/
def KernelIFLeftIndex := {b : (Σ k : ℕ, Fin k × FluxFacetIndex k) //
  fluxFacetValid b.2.2 ∧ (b.2.2.1 : ℕ) ≤ b.2.1 ∧ (b.2.1 : ℕ) < b.2.2.2.1}

/-- Outside prefix, steps before/after the mark, other bridge minus one,
outside suffix, and the actual facet sign. Zero-zero is the Dirac bridge. -/
abbrev KernelIFBlockIndex := ℕ × ℕ × ℕ × ℕ × ℕ × Bool

def kernelIFLeftOfBlocks (p : KernelIFBlockIndex) : KernelIFLeftIndex := by
  rcases p with ⟨u,l,h,m,v,σ⟩
  let k := u+(l+h+1)+(m+1)+v
  let q : FluxFacetIndex k :=
    (⟨u, by omega⟩, ⟨u+(l+h+1), by omega⟩, ⟨u+(l+h+1)+(m+1), by omega⟩, σ)
  exact ⟨⟨k, ⟨⟨u+l, by omega⟩, q⟩⟩, by
    change (u < u+(l+h+1) ∧ u+(l+h+1) < u+(l+h+1)+(m+1)) ∧
      u ≤ u+l ∧ u+l < u+(l+h+1)
    omega⟩

def kernelIFLeftToBlocks (b : KernelIFLeftIndex) : KernelIFBlockIndex :=
  (b.1.2.2.1, b.1.2.1-b.1.2.2.1, b.1.2.2.2.1-b.1.2.1-1,
    b.1.2.2.2.2.1-b.1.2.2.2.1-1, b.1.1-b.1.2.2.2.2.1, b.1.2.2.2.2.2)

theorem kernel_IF_left_to_of_blocks (p : KernelIFBlockIndex) :
    kernelIFLeftToBlocks (kernelIFLeftOfBlocks p) = p := by
  rcases p with ⟨u,l,h,m,v,σ⟩
  simp only [kernelIFLeftOfBlocks, kernelIFLeftToBlocks]
  congr 1
  simp +arith
  omega

theorem kernel_IF_source_ext {k k' : ℕ} {i : Fin k} {i' : Fin k'}
    {r s t : Fin (k+1)} {r' s' t' : Fin (k'+1)} {σ σ' : Bool}
    (hk : k = k') (hi : (i : ℕ) = i') (hr : (r : ℕ) = r')
    (hs : (s : ℕ) = s') (ht : (t : ℕ) = t') (hσ : σ = σ') :
    (⟨k, (i,r,s,t,σ)⟩ : Σ n : ℕ, Fin n × FluxFacetIndex n) = ⟨k', (i',r',s',t',σ')⟩ := by
  subst k'
  congr 1
  exact Prod.ext (Fin.ext hi) (Prod.ext (Fin.ext hr) (Prod.ext (Fin.ext hs) (Prod.ext (Fin.ext ht) hσ)))

theorem kernel_IF_left_of_to_blocks (b : KernelIFLeftIndex) :
    kernelIFLeftOfBlocks (kernelIFLeftToBlocks b) = b := by
  rcases b with ⟨⟨k,⟨i,⟨r,s,t,σ⟩⟩⟩, hq, hi₁, hi₂⟩
  dsimp only at hq hi₁ hi₂
  change (r : ℕ) < s ∧ (s : ℕ) < t at hq
  have hi : (r : ℕ)+(i-r) = i := by omega
  have hs : (r : ℕ)+(i-r+(s-i-1)+1) = s := by omega
  have ht : (s : ℕ)+(t-s-1+1) = t := by omega
  have hk : (t : ℕ)+(k-t) = k := by omega
  apply Subtype.ext
  dsimp [kernelIFLeftToBlocks, kernelIFLeftOfBlocks]
  apply kernel_IF_source_ext
  · omega
  · exact hi
  · rfl
  · exact hs
  · change (r : ℕ)+(i-r+(s-i-1)+1)+(t-s-1+1) = (t : ℕ)
    omega
  · rfl

def kernelIFLeftBlockEquiv : KernelIFLeftIndex ≃ KernelIFBlockIndex where
  toFun := kernelIFLeftToBlocks
  invFun := kernelIFLeftOfBlocks
  left_inv := kernel_IF_left_of_to_blocks
  right_inv := kernel_IF_left_to_of_blocks

/-- Original finite-prefix facet with its mark in the second bridge. -/
def KernelIFRightIndex := {b : (Σ k : ℕ, Fin k × FluxFacetIndex k) //
  fluxFacetValid b.2.2 ∧ (b.2.2.2.1 : ℕ) ≤ b.2.1 ∧ (b.2.1 : ℕ) < b.2.2.2.2.1}

def kernelIFRightOfBlocks (p : KernelIFBlockIndex) : KernelIFRightIndex := by
  rcases p with ⟨u,l,h,m,v,σ⟩
  let k := u+(m+1)+(l+h+1)+v
  let q : FluxFacetIndex k :=
    (⟨u, by omega⟩, ⟨u+(m+1), by omega⟩, ⟨u+(m+1)+(l+h+1), by omega⟩, σ)
  exact ⟨⟨k, ⟨⟨u+(m+1)+l, by omega⟩, q⟩⟩, by
    change (u < u+(m+1) ∧ u+(m+1) < u+(m+1)+(l+h+1)) ∧
      u+(m+1) ≤ u+(m+1)+l ∧ u+(m+1)+l < u+(m+1)+(l+h+1)
    omega⟩

def kernelIFRightToBlocks (b : KernelIFRightIndex) : KernelIFBlockIndex :=
  (b.1.2.2.1, b.1.2.1-b.1.2.2.2.1, b.1.2.2.2.2.1-b.1.2.1-1,
    b.1.2.2.2.1-b.1.2.2.1-1, b.1.1-b.1.2.2.2.2.1, b.1.2.2.2.2.2)

theorem kernel_IF_right_to_of_blocks (p : KernelIFBlockIndex) :
    kernelIFRightToBlocks (kernelIFRightOfBlocks p) = p := by
  rcases p with ⟨u,l,h,m,v,σ⟩
  simp only [kernelIFRightOfBlocks, kernelIFRightToBlocks]
  congr 1
  simp +arith
  omega

theorem kernel_IF_right_of_to_blocks (b : KernelIFRightIndex) :
    kernelIFRightOfBlocks (kernelIFRightToBlocks b) = b := by
  rcases b with ⟨⟨k,⟨i,⟨r,s,t,σ⟩⟩⟩, hq, hi₁, hi₂⟩
  dsimp only at hq hi₁ hi₂
  change (r : ℕ) < s ∧ (s : ℕ) < t at hq
  have hs : (r : ℕ)+(s-r-1+1) = s := by omega
  have ht : (s : ℕ)+(i-s+(t-i-1)+1) = t := by omega
  have hk : (t : ℕ)+(k-t) = k := by omega
  apply Subtype.ext
  dsimp [kernelIFRightToBlocks, kernelIFRightOfBlocks]
  apply kernel_IF_source_ext
  · omega
  · change (r : ℕ)+(s-r-1+1)+(i-s) = (i : ℕ)
    omega
  · rfl
  · exact hs
  · change (r : ℕ)+(s-r-1+1)+(i-s+(t-i-1)+1) = (t : ℕ)
    omega
  · rfl

def kernelIFRightBlockEquiv : KernelIFRightIndex ≃ KernelIFBlockIndex where
  toFun := kernelIFRightToBlocks
  invFun := kernelIFRightOfBlocks
  left_inv := kernel_IF_right_of_to_blocks
  right_inv := kernel_IF_right_to_of_blocks

theorem kernel_IF_left_tsum_reindex (F : KernelIFLeftIndex → ℝ≥0∞) :
    (∑' b, F b) = ∑' p, F (kernelIFLeftOfBlocks p) :=
  (kernelIFLeftBlockEquiv.symm.tsum_eq F).symm

theorem kernel_IF_right_tsum_reindex (F : KernelIFRightIndex → ℝ≥0∞) :
    (∑' b, F b) = ∑' p, F (kernelIFRightOfBlocks p) :=
  (kernelIFRightBlockEquiv.symm.tsum_eq F).symm

/-- Splitting the original source index and reindexing it does not require
summability: the identity is first proved in the nonnegative extended reals. -/
theorem kernel_IF_source_tsum_blocks
    (F : (Σ k : ℕ, Fin k × FluxFacetIndex k) → ℝ≥0∞)
    (hz : ∀ b, ¬(fluxFacetValid b.2.2 ∧ (b.2.2.1 : ℕ) ≤ b.2.1 ∧
        (b.2.1 : ℕ) < b.2.2.2.1) →
      ¬(fluxFacetValid b.2.2 ∧ (b.2.2.2.1 : ℕ) ≤ b.2.1 ∧
        (b.2.1 : ℕ) < b.2.2.2.2.1) → F b = 0) :
    (∑' b, F b) =
      (∑' p : KernelIFBlockIndex, F (kernelIFLeftOfBlocks p).1) +
      ∑' p : KernelIFBlockIndex, F (kernelIFRightOfBlocks p).1 := by
  classical
  let L : Set (Σ k : ℕ, Fin k × FluxFacetIndex k) :=
    {b | fluxFacetValid b.2.2 ∧ (b.2.2.1 : ℕ) ≤ b.2.1 ∧ (b.2.1 : ℕ) < b.2.2.2.1}
  let R : Set (Σ k : ℕ, Fin k × FluxFacetIndex k) :=
    {b | fluxFacetValid b.2.2 ∧ (b.2.2.2.1 : ℕ) ≤ b.2.1 ∧ (b.2.1 : ℕ) < b.2.2.2.2.1}
  have he (b) : F b = L.indicator F b + R.indicator F b := by
    by_cases hl : b ∈ L
    · have hr : b ∉ R := by intro hr; exact (not_lt_of_ge hr.2.1) hl.2.2
      simp only [Set.indicator_of_mem hl, Set.indicator_of_notMem hr, add_zero]
    · by_cases hr : b ∈ R
      · simp only [Set.indicator_of_notMem hl, Set.indicator_of_mem hr, zero_add]
      · rw [hz b hl hr, Set.indicator_of_notMem hl, Set.indicator_of_notMem hr, add_zero]
  calc
    _ = ∑' b, (L.indicator F b + R.indicator F b) := tsum_congr he
    _ = (∑' b, L.indicator F b) + ∑' b, R.indicator F b := ENNReal.tsum_add
    _ = (∑' b : KernelIFLeftIndex, F b.1) + ∑' b : KernelIFRightIndex, F b.1 := by
      rw [← tsum_subtype L F, ← tsum_subtype R F]
      rfl
    _ = _ := by rw [kernel_IF_left_tsum_reindex, kernel_IF_right_tsum_reindex]

end
end PGM
