import PLAStochastic.Index.GEP.Kernel.Leaves.OutputNearError
import PLAStochastic.Index.GEP.Kernel.Tail.Original.Closure
import PLAStochastic.Index.GEP.Kernel.NearSlope.BoundaryIdentity
import PLAStochastic.Index.GEP.Kernel.Leaves.ScalarFromOutput

/-!
# The original scalar and output kernel leaves

The near identity connects the actual physical boundary to the four insertion
kernels. Their AL bounds and the complementary-slope error use the same legal
density. Primitive uniqueness supplies the already proved global tail.
The output exponent precedes every input exponent, and the tail power is 16.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1800000

/-- Original output kernel regularity, including both AL and TAIL with their
original quantifier order and with no additional test regularity. -/
theorem kernelPhi : KernelPhi := by
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηE,hηE,hError⟩ := kernel_regLaw_output_near_error D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηN,hηN,hNear⟩ := kernel_regLaw_signed_insertion_near D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηP,eP,hηP,_heP,hPrimitive⟩ := output_isBdryKernel_regLaw D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηT,hηT,hTail⟩ := kernel_output_tail_all_boundaries D θ vlo vhi hD hθ hvlo hv
  let ηB := min ηE (min ηN (min ηP ηT))
  have hηB : 0 < ηB := lt_min hηE (lt_min hηN (lt_min hηP hηT))
  refine ⟨ηB,hηB,?_⟩
  intro η hη hηle
  have hηe : η ≤ ηE := hηle.trans (min_le_left _ _)
  have hηn : η ≤ ηN := hηle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηp : η ≤ ηP := hηle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηt : η ≤ ηT := hηle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨16,?_⟩
  intro b ζ hb hζ
  obtain ⟨α,KE,eE,hα,hKE,_heE,hError⟩ := hError b hb
  obtain ⟨KN,eN,hKN,_heN,hNear⟩ := hNear α b hα hb
  obtain ⟨KT,eT,hKT,_heT,hTail⟩ := hTail ζ hζ
  obtain ⟨eA,hA⟩ := eventually_atTop.mp
    (kernel_log_cutoff_eventually hα (by norm_num : (0 : ℝ) < 1/4))
  obtain ⟨eX,hX⟩ := eventually_atTop.mp (kernel_log_cutoff_eventually hb zero_lt_one)
  let K := KE+KN+KT
  let e0 := max 2 (max eE (max eN (max eP (max eT (max eA eX)))))
  have hKEN : KE+KN ≤ K := by dsimp [K]; linarith
  have hNK : KN ≤ K := by dsimp [K]; linarith
  have hTK : KT ≤ K := by dsimp [K]; linarith
  refine ⟨8,K,e0,?_⟩
  intro eps heps ν hν M ψ hψ
  have he2 : 2 ≤ eps := (le_max_left 2 _).trans heps
  have hep : 0 < eps := by linarith
  have heE : eE ≤ eps := (show eE ≤ e0 from le_max_of_le_right (le_max_left _ _)).trans heps
  have heN : eN ≤ eps := (show eN ≤ e0 from
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans heps
  have heP : eP ≤ eps := (show eP ≤ e0 from
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))).trans heps
  have heT : eT ≤ eps := (show eT ≤ e0 from le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))).trans heps
  have heA : eA ≤ eps := (show eA ≤ e0 from le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))).trans heps
  have heX : eX ≤ eps := (show eX ≤ e0 from le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))).trans heps
  have hAw : α*Real.log (2*eps) ≤ (2*eps)/4 := by
    have hh := (hA (2*eps) (by linarith : eA ≤ 2*eps)).2.2
    linarith
  have hXw : b*Real.log eps ≤ eps := by simpa only [one_mul] using (hX eps heX).2.2
  obtain ⟨f,hf,hf0,hfD,hfz,hfe,hνf,hError⟩ := hError ν hν
  obtain ⟨hFinite,hClose⟩ := hError eps heE η M hη.le hηe ψ hψ
  have hNear := (hNear ν hν f hf hf0 hfz hfD hfe hνf eps heN).2 η M hη.le hηn ψ hψ
  let S := kernelNearSlopes (2*eps) (α*Real.log (2*eps))
  let H := kernelPositiveBoundaryReward ν (lawC eps ν) ψ
  have hS : MeasurableSet S := measurableSet_kernelNearSlopes _ _
  have hSsub : S ⊆ Ioo (1/2 : ℝ) 2 := kernelNearSlopes_subset (by positivity) hAw
  have hIdentity : ∀ x ∈ Ioo (0 : ℝ) (b*Real.log eps),
      kernelIFTotalPinBoundaryOn ν f eps S H x =
        kernelIFInsertionNearBoundary ν f (2*eps) (α*Real.log (2*eps)) H x := by
    intro x hx
    have hfin : kernelIFTotalPinBlockMassOn ν f eps S
        (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞ :=
      ne_top_of_le_ne_top (hFinite x hx.1)
        (kernel_IF_total_block_massOn_le ν f eps hS _ _ x)
    have hh := kernel_IF_near_boundary_eq_insertion ν hf hf0
      (w := 2*eps) (A := α*Real.log (2*eps)) (x := x)
      (by linarith : 1 ≤ 2*eps) hx.1 (by linarith [hx.2] : 2*x ≤ 2*eps+1)
      hSsub (measurable_kernelPositiveBoundaryReward hψ ν (lawC eps ν))
      (by simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hfin)
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hClose' : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (b*Real.log eps)),
      |outputIFBoundary eps ν (fun x => ENNReal.ofReal (f x)) ψ (lawC eps ν) x -
        kernelIFInsertionNearBoundary ν f (2*eps) (α*Real.log (2*eps)) H x| ≤ M*(KE/eps) := by
    filter_upwards [hClose,ae_restrict_mem measurableSet_Ioo] with x hx hxR
    have hi := hIdentity x hxR
    dsimp only [S,H] at hi
    simpa only [hi] using hx
  have hAL := hNear.of_close hClose'
  have hM := hψ.nonneg
  have hAL' : KernelApproxLip (b*Real.log eps) (M*(K*Real.sqrt eps*Real.log eps^8))
      (M*(K/eps)) (outputIFBoundary eps ν (fun x => ENNReal.ofReal (f x)) ψ (lawC eps ν)) := by
    apply hAL.mono
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hNK (Real.sqrt_nonneg _)) (pow_nonneg (Real.log_nonneg (by linarith)) _)) hM
    · calc
        M*(KN/eps)+M*(KE/eps) = M*((KE+KN)/eps) := by ring
        _ ≤ M*(K/eps) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hKEN hep.le) hM
  have hPrimitive := hPrimitive eps heP ν hν (fun x => ENNReal.ofReal (f x))
    hf.ennreal_ofReal hνf η M hη hηp ψ hψ
  refine ⟨outputBoundaryKernel eps ν (fun x => ENNReal.ofReal (f x)) ψ,hPrimitive,?_,?_⟩
  · apply hAL'.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact output_boundary_kernel_pos eps ν _ ψ hx.1
  · exact (hTail eps heT ν hν η hη hηt M ψ hψ _ hPrimitive).mono
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTK (pow_nonneg hep.le _)) hM)

/-- The original scalar kernel follows from the proved output leaf. -/
theorem kernelC : KernelC := kernelC_of_kernelPhi kernelPhi

end
end PGM
