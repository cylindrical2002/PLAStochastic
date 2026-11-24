import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopePartition
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveSeries

/-!
# Absolute convergence of the actual slope-restricted signed block series

Finiteness is supplied by the original absolute physical mass. Only after that
step are its four signed parts converted to real series and regrouped by the
left and right physical block coordinates.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The real contribution of one original source facet on a slope region. -/
def kernelIFSignedFacetOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) (H : ℝ → ℝ) (x : ℝ) (b : KernelIFSourceIndex) : ℝ := by
  classical
  let pos := kernelIFFacetTotalPinDensityOn ν f eps S b.2.2 b.2.1
    (fun s => ENNReal.ofReal (H s)) x
  let neg := kernelIFFacetTotalPinDensityOn ν f eps S b.2.2 b.2.1
    (fun s => ENNReal.ofReal (-H s)) x
  exact ((if fluxFacetCoef eps b.2.2 b.2.1 < 0 then pos else 0).toReal -
      (if fluxFacetCoef eps b.2.2 b.2.1 < 0 then neg else 0).toReal) -
    ((if 0 < fluxFacetCoef eps b.2.2 b.2.1 then pos else 0).toReal -
      (if 0 < fluxFacetCoef eps b.2.2 b.2.1 then neg else 0).toReal)

theorem kernel_IF_total_block_massOn_real_series (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) (eps : ℝ) (S : Set ℝ) (H : ℝ → ℝ≥0∞)
    (A : KernelIFSourceIndex → Prop) [DecidablePred A] (x : ℝ)
    (hfin : kernelIFTotalPinBlockMassOn ν f eps S H A x ≠ ∞) :
    let L := fun p : KernelIFBlockIndex =>
      (if A (kernelIFLeftOfBlocks p).1 then kernelIFFacetTotalPinDensityOn ν f eps S
        (kernelIFLeftOfBlocks p).1.2.2 (kernelIFLeftOfBlocks p).1.2.1 H x else 0).toReal
    let R := fun p : KernelIFBlockIndex =>
      (if A (kernelIFRightOfBlocks p).1 then kernelIFFacetTotalPinDensityOn ν f eps S
        (kernelIFRightOfBlocks p).1.2.2 (kernelIFRightOfBlocks p).1.2.1 H x else 0).toReal
    Summable L ∧ Summable R ∧
      (kernelIFTotalPinBlockMassOn ν f eps S H A x).toReal = (∑' p, L p) + ∑' p, R p := by
  classical
  dsimp only
  unfold kernelIFTotalPinBlockMassOn at hfin ⊢
  have hL := (ENNReal.add_ne_top.mp hfin).1
  have hR := (ENNReal.add_ne_top.mp hfin).2
  refine ⟨?_, ?_, ?_⟩
  · convert ENNReal.summable_toReal hL using 1
    ext p
    split_ifs <;> rfl
  · convert ENNReal.summable_toReal hR using 1
    ext p
    split_ifs <;> rfl
  rw [ENNReal.toReal_add hL hR,
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hL),
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hR)]
  congr 1 <;> apply tsum_congr <;> intro p <;> split_ifs <;> rfl

/-- The two physical block series are absolutely convergent and sum to the
original signed boundary on the selected slopes. Dirac terms are still present
in precisely the branch prescribed by the original facet density. -/
theorem kernel_IF_boundaryOn_block_series (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) (H : ℝ → ℝ) (x : ℝ)
    (hfin : kernelIFTotalPinBlockMassOn ν f eps S
      (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞) :
    Summable (fun p : KernelIFBlockIndex =>
      ‖kernelIFSignedFacetOn ν f eps S H x (kernelIFLeftOfBlocks p).1‖) ∧
    Summable (fun p : KernelIFBlockIndex =>
      ‖kernelIFSignedFacetOn ν f eps S H x (kernelIFRightOfBlocks p).1‖) ∧
    kernelIFTotalPinBoundaryOn ν f eps S H x =
      (∑' p : KernelIFBlockIndex, kernelIFSignedFacetOn ν f eps S H x (kernelIFLeftOfBlocks p).1) +
      ∑' p : KernelIFBlockIndex, kernelIFSignedFacetOn ν f eps S H x (kernelIFRightOfBlocks p).1 := by
  classical
  have hp (A : KernelIFSourceIndex → Prop) :
      kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (H s)) A x ≠ ∞ :=
    ne_top_of_le_ne_top hfin (kernel_IF_total_block_massOn_mono ν f eps S x
      (fun s => ENNReal.ofReal_le_ofReal (le_abs_self _)) (fun _ _ => trivial))
  have hn (A : KernelIFSourceIndex → Prop) :
      kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (-H s)) A x ≠ ∞ :=
    ne_top_of_le_ne_top hfin (kernel_IF_total_block_massOn_mono ν f eps S x
      (fun s => ENNReal.ofReal_le_ofReal (neg_le_abs _)) (fun _ _ => trivial))
  obtain ⟨hLpL, hLpR, eLp⟩ := kernel_IF_total_block_massOn_real_series ν f eps S
    (fun s => ENNReal.ofReal (H s)) (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x (hp _)
  obtain ⟨hLnL, hLnR, eLn⟩ := kernel_IF_total_block_massOn_real_series ν f eps S
    (fun s => ENNReal.ofReal (-H s)) (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x (hn _)
  obtain ⟨hUpL, hUpR, eUp⟩ := kernel_IF_total_block_massOn_real_series ν f eps S
    (fun s => ENNReal.ofReal (H s)) (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x (hp _)
  obtain ⟨hUnL, hUnR, eUn⟩ := kernel_IF_total_block_massOn_real_series ν f eps S
    (fun s => ENNReal.ofReal (-H s)) (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x (hn _)
  have hL := (hLpL.sub hLnL).sub (hUpL.sub hUnL)
  have hR := (hLpR.sub hLnR).sub (hUpR.sub hUnR)
  refine ⟨hL.norm, hR.norm, ?_⟩
  unfold kernelIFTotalPinBoundaryOn kernelIFSignedFacetOn
  rw [eLp, eLn, eUp, eUn,
    (hLpL.sub hLnL).tsum_sub (hUpL.sub hUnL),
    (hLpR.sub hLnR).tsum_sub (hUpR.sub hUnR),
    hLpL.tsum_sub hLnL, hUpL.tsum_sub hUnL,
    hLpR.tsum_sub hLnR, hUpR.tsum_sub hUnR]
  ring

/-- L1 summability supplies the pointwise absolute convergence used when
regrouping an actual block integrand. -/
theorem kernel_IF_ae_summable_norm {ι : Type*} [Countable ι] {μ : Measure ℝ}
    {F : ι → ℝ → ℝ} (hi : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ a, ‖F i a‖ ∂μ)) :
    ∀ᵐ a ∂μ, Summable (fun i => ‖F i a‖) := by
  have hfinite : (∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ) ≠ ∞ := by
    rw [lintegral_tsum fun i => (hi i).aestronglyMeasurable.enorm]
    exact kernel_tsum_lintegral_enorm_ne_top hi hs
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun i => (hi i).aestronglyMeasurable.enorm)
    hfinite] with a ha
  exact tsum_enorm_ne_top_iff_summable_norm.mp ha.ne

/-- The two countable length sums may be interchanged with the slope integral
only after their L1 mass has been proved summable. -/
theorem kernel_IF_integral_prod_tsum {ι κ : Type*} [Countable ι] [Countable κ]
    {μ : Measure ℝ} {F : (ι × κ) → ℝ → ℝ}
    (hi : ∀ p, Integrable (F p) μ)
    (hs : Summable (fun p => ∫ a, ‖F p a‖ ∂μ)) :
    (∑' i, ∑' j, ∫ a, F (i,j) a ∂μ) = ∫ a, ∑' i, ∑' j, F (i,j) a ∂μ := by
  have hI : Summable (fun p => ∫ a, F p a ∂μ) :=
    hs.of_norm_bounded (fun p => norm_integral_le_integral_norm _)
  rw [← hI.tsum_prod, integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  filter_upwards [kernel_IF_ae_summable_norm hi hs] with a ha
  exact ha.of_norm.tsum_prod

/-- Separate the contact orientation, marked-side lengths and exterior lengths. -/
def kernelIFBlockSeriesEquiv :
    KernelIFBlockIndex ≃ Bool × ((ℕ × ℕ) × (ℕ × ℕ × ℕ)) where
  toFun p := (p.2.2.2.2.2, (p.2.1,p.2.2.1), (p.1,p.2.2.2.1,p.2.2.2.2.1))
  invFun p := (p.2.2.1,p.2.1.1,p.2.1.2,p.2.2.2.1,p.2.2.2.2,p.1)
  left_inv := by rintro ⟨u,l,r,m,v,σ⟩; rfl
  right_inv := by rintro ⟨σ,⟨l,r⟩,⟨u,m,v⟩⟩; rfl

/-- Exact physical-block reindexing and Fubini, including the orientation sum. -/
theorem kernel_IF_block_integral_regroup {μ : Measure ℝ}
    {F : Bool → (ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℝ → ℝ}
    (hi : ∀ p : KernelIFBlockIndex, Integrable
      (F p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1)) μ)
    (hs : Summable (fun p : KernelIFBlockIndex =>
      ∫ a, ‖F p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a‖ ∂μ)) :
    (∑' p : KernelIFBlockIndex, ∫ a,
      F p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a ∂μ) =
      (∫ a, ∑' q, ∑' t, F true q t a ∂μ) +
        ∫ a, ∑' q, ∑' t, F false q t a ∂μ := by
  let G : (Bool × ((ℕ × ℕ) × (ℕ × ℕ × ℕ))) → ℝ → ℝ :=
    fun p => F p.1 p.2.1 p.2.2
  have hiG (p) : Integrable (G p) μ := hi (kernelIFBlockSeriesEquiv.symm p)
  have hsG : Summable (fun p => ∫ a, ‖G p a‖ ∂μ) :=
    (kernelIFBlockSeriesEquiv.summable_iff).mp hs
  have hI : Summable (fun p => ∫ a, G p a ∂μ) :=
    hsG.of_norm_bounded (fun p => norm_integral_le_integral_norm _)
  calc
    _ = ∑' p, ∫ a, G p a ∂μ := kernelIFBlockSeriesEquiv.tsum_eq _
    _ = ∑' σ : Bool, ∑' q, ∑' t, ∫ a, G (σ,q,t) a ∂μ := by
      rw [hI.tsum_prod]
      apply tsum_congr
      intro σ
      exact (hI.prod_factor σ).tsum_prod
    _ = ∑' σ : Bool, ∫ a, ∑' q, ∑' t, G (σ,q,t) a ∂μ := by
      apply tsum_congr
      intro σ
      exact kernel_IF_integral_prod_tsum (fun p => hiG (σ,p)) (hsG.prod_factor σ)
    _ = _ := by simp only [tsum_fintype, Fintype.sum_bool, G]

end
end PGM
