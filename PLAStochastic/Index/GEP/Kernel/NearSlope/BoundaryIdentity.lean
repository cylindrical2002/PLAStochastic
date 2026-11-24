import PLAStochastic.Index.GEP.Kernel.NearSlope.InsertionNorm
import PLAStochastic.Index.GEP.Kernel.Influence.Signed.BlockSeries
import PLAStochastic.Index.GEP.Kernel.NearSlope.ApproxLipschitz

/-!
# The actual near boundary equals the four signed insertion kernels

The original absolute pin mass justifies every countable regrouping and slope
integration. The finite coarea theorem includes the single-gap Dirac branch,
which vanishes on this spatial and slope window.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1800000

def kernelIFInsertionIntegrand (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w : ℝ) (H : ℝ → ℝ) (x : ℝ) (up outerUp : Bool)
    (q : ℕ × ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) : ℝ :=
  kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
    (if up then 0 else w) (if up then w else 0) *
    krInsertionCoefficientTerm ν f w up outerUp (kernelIFInsertionReward H w up outerUp)
      q.1 q.2 t a

theorem kernel_IF_insertion_integrand_integral (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w A : ℝ) (H : ℝ → ℝ) (x : ℝ) (up outerUp : Bool) :
    (∫ a in kernelNearSlopes w A, ∑' q, ∑' t,
      kernelIFInsertionIntegrand ν f w H x up outerUp q t a) =
      krInsertionNearKernel ν f w A up outerUp (kernelIFInsertionReward H w up outerUp) x := by
  unfold krInsertionNearKernel
  apply integral_congr_ae
  apply ae_of_all
  intro a
  apply tsum_congr
  intro q
  unfold kernelIFInsertionIntegrand
  rw [tsum_mul_left]
  exact mul_comm _ _

theorem kernel_IF_left_signed_direction (ν : ProbabilityMeasure ℝ) (f H : ℝ → ℝ)
    (w x : ℝ) (S : Set ℝ) (u l r m v : ℕ) (σ : Bool) :
    kernelIFSignedFacetOn ν f (w/2) S H x (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1 =
      if σ then
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (H s)) x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (-H s)) x).toReal
      else -((kernelIFFacetTotalPinDensityOn ν f (w/2) S
          (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (H s)) x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (-H s)) x).toReal) := by
  classical
  by_cases he : krInsertionEffective w σ l r m
  · obtain ⟨hneg,hpos⟩ := kernel_IF_left_block_coef_negative w u l r m v σ he
    unfold kernelIFSignedFacetOn
    cases σ <;> simp only [hneg,hpos,Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,
      ENNReal.toReal_zero,zero_sub,sub_zero,sub_self]
  · have hE : ¬ kernelFacetEffective (w/2) (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2 :=
      fun h => he ((kernel_IF_left_block_effective w u l r m v σ).1 h)
    cases σ <;> simp [kernelIFSignedFacetOn,kernelIFFacetTotalPinDensityOn,hE]

theorem kernel_IF_right_signed_direction (ν : ProbabilityMeasure ℝ) (f H : ℝ → ℝ)
    (w x : ℝ) (S : Set ℝ) (u l r m v : ℕ) (σ : Bool) :
    kernelIFSignedFacetOn ν f (w/2) S H x (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1 =
      if σ then
        -((kernelIFFacetTotalPinDensityOn ν f (w/2) S (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (H s)) x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (-H s)) x).toReal)
      else (kernelIFFacetTotalPinDensityOn ν f (w/2) S
          (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (H s)) x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
          (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (-H s)) x).toReal := by
  classical
  by_cases he : krInsertionEffective w (!σ) l r m
  · obtain ⟨hneg,hpos⟩ := kernel_IF_right_block_coef_negative w u l r m v σ he
    unfold kernelIFSignedFacetOn
    cases σ <;> simp only [hneg,hpos,Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,
      ENNReal.toReal_zero,zero_sub,sub_zero,sub_self]
  · have hE : ¬ kernelFacetEffective (w/2) (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2 :=
      fun h => he ((kernel_IF_right_block_effective w u l r m v σ).1 h)
    cases σ <;> simp [kernelIFSignedFacetOn,kernelIFFacetTotalPinDensityOn,hE]

/-- Exact identification with the original near physical boundary. All
integrability and summability premises follow from its actual absolute mass. -/
theorem kernel_IF_near_boundary_eq_insertion (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    {w A x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    (hSI : kernelNearSlopes w A ⊆ Ioo (1/2 : ℝ) 2)
    {H : ℝ → ℝ} (hH : Measurable H)
    (hfin : kernelIFTotalPinBlockMassOn ν f (w/2) (kernelNearSlopes w A)
      (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞) :
    kernelIFTotalPinBoundaryOn ν f (w/2) (kernelNearSlopes w A) H x =
      kernelIFInsertionNearBoundary ν f w A H x := by
  classical
  let S := kernelNearSlopes w A
  have hS : MeasurableSet S := measurableSet_kernelNearSlopes w A
  let L := fun (σ : Bool) (q : ℕ × ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) =>
    kernelIFInsertionIntegrand ν f w H x σ σ q t a
  let R := fun (σ : Bool) (q : ℕ × ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) =>
    kernelIFInsertionIntegrand ν f w H x (!σ) σ q t a
  let massL := fun p : KernelIFBlockIndex => kernelIFFacetTotalPinDensityOn ν f (w/2) S
    (kernelIFLeftOfBlocks p).1.2.2 (kernelIFLeftOfBlocks p).1.2.1
    (fun s => ENNReal.ofReal |H s|) x
  let massR := fun p : KernelIFBlockIndex => kernelIFFacetTotalPinDensityOn ν f (w/2) S
    (kernelIFRightOfBlocks p).1.2.2 (kernelIFRightOfBlocks p).1.2.1
    (fun s => ENNReal.ofReal |H s|) x
  have hfin' : (∑' p, massL p) + (∑' p, massR p) ≠ ∞ := by
    simpa only [kernelIFTotalPinBlockMassOn,if_true] using hfin
  have hmL := (ENNReal.add_ne_top.mp hfin').1
  have hmR := (ENNReal.add_ne_top.mp hfin').2
  have hpL (p : KernelIFBlockIndex) := ENNReal.ne_top_of_tsum_ne_top hmL p
  have hpR (p : KernelIFBlockIndex) := ENNReal.ne_top_of_tsum_ne_top hmR p
  have hiL (p : KernelIFBlockIndex) : IntegrableOn
      (L p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1)) S :=
    (kernel_IF_left_block_near_signed_integral ν hf hf0 hw hx hxw hS hSI
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 hH (hpL p)).1
  have hiR (p : KernelIFBlockIndex) : IntegrableOn
      (R p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1)) S :=
    (kernel_IF_right_block_near_signed_integral ν hf hf0 hw hx hxw hS hSI
      p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 hH (hpR p)).1
  have hsL : Summable (fun p : KernelIFBlockIndex => ∫ a in S,
      ‖L p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun p => kernel_IF_left_block_near_norm_integral ν hf hf0 hw hx hxw hS hSI
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 hH (hpL p))
      (ENNReal.summable_toReal hmL)
  have hsR : Summable (fun p : KernelIFBlockIndex => ∫ a in S,
      ‖R p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun p => kernel_IF_right_block_near_norm_integral ν hf hf0 hw hx hxw hS hSI
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 hH (hpR p))
      (ENNReal.summable_toReal hmR)
  let FL := fun (σ : Bool) q t a => if σ then L σ q t a else -L σ q t a
  let FR := fun (σ : Bool) q t a => if σ then -R σ q t a else R σ q t a
  have hiFL (p : KernelIFBlockIndex) : IntegrableOn
      (FL p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1)) S := by
    dsimp only [FL]
    split_ifs
    · exact hiL p
    · exact (hiL p).neg
  have hiFR (p : KernelIFBlockIndex) : IntegrableOn
      (FR p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1)) S := by
    dsimp only [FR]
    split_ifs
    · exact (hiR p).neg
    · exact hiR p
  have hsFL : Summable (fun p : KernelIFBlockIndex => ∫ a in S,
      ‖FL p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a‖) := by
    convert hsL using 1
    funext p
    apply integral_congr_ae
    exact ae_of_all _ (fun a => by dsimp only [FL]; split_ifs <;> simp only [norm_neg])
  have hsFR : Summable (fun p : KernelIFBlockIndex => ∫ a in S,
      ‖FR p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a‖) := by
    convert hsR using 1
    funext p
    apply integral_congr_ae
    exact ae_of_all _ (fun a => by dsimp only [FR]; split_ifs <;> simp only [norm_neg])
  have heL (p : KernelIFBlockIndex) :
      kernelIFSignedFacetOn ν f (w/2) S H x (kernelIFLeftOfBlocks p).1 =
        ∫ a in S, FL p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a := by
    rcases p with ⟨u,l,r,m,v,σ⟩
    rw [kernel_IF_left_signed_direction]
    have hh := (kernel_IF_left_block_near_signed_integral ν hf hf0 hw hx hxw hS hSI
      u l r m v σ hH (hpL (u,l,r,m,v,σ))).2
    cases σ with
    | false => simpa only [FL,L,kernelIFInsertionIntegrand,Bool.false_eq_true,if_true,if_false,integral_neg]
        using congrArg Neg.neg hh
    | true => simpa only [FL,L,kernelIFInsertionIntegrand,if_true,if_false,integral_neg] using hh
  have heR (p : KernelIFBlockIndex) :
      kernelIFSignedFacetOn ν f (w/2) S H x (kernelIFRightOfBlocks p).1 =
        ∫ a in S, FR p.2.2.2.2.2 (p.2.1,p.2.2.1) (p.1,p.2.2.2.1,p.2.2.2.2.1) a := by
    rcases p with ⟨u,l,r,m,v,σ⟩
    rw [kernel_IF_right_signed_direction]
    have hh := (kernel_IF_right_block_near_signed_integral ν hf hf0 hw hx hxw hS hSI
      u l r m v σ hH (hpR (u,l,r,m,v,σ))).2
    cases σ with
    | false => simpa only [FR,R,kernelIFInsertionIntegrand,Bool.false_eq_true,if_true,if_false,integral_neg] using hh
    | true => simpa only [FR,R,kernelIFInsertionIntegrand,if_true,if_false,integral_neg]
        using congrArg Neg.neg hh
  have hGL := kernel_IF_block_integral_regroup (μ := volume.restrict S) (F := FL) hiFL hsFL
  have hGR := kernel_IF_block_integral_regroup (μ := volume.restrict S) (F := FR) hiFR hsFR
  have hb := (kernel_IF_boundaryOn_block_series ν f (w/2) S H x hfin).2.2
  rw [hb, tsum_congr heL, tsum_congr heR, hGL, hGR]
  simp only [FL,FR,L,R,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_true,if_false,
    tsum_neg,integral_neg]
  rw [kernel_IF_insertion_integrand_integral, kernel_IF_insertion_integrand_integral,
    kernel_IF_insertion_integrand_integral, kernel_IF_insertion_integrand_integral]
  unfold kernelIFInsertionNearBoundary
  ring

end
end PGM
