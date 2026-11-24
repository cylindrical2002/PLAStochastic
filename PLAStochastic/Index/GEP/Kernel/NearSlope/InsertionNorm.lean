import PLAStochastic.Index.GEP.Kernel.NearSlope.InsertionTerms
import PLAStochastic.Index.GEP.Kernel.Influence.Signed.NormBound

/-! # Actual absolute near masses control the insertion terms in L1 -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem kernel_IF_left_signed_densityOn_norm (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hQ : 0 ≤ kernelFacetQ eps q) {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ)
    (hfin : kernelIFLeftTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    (∫ a in S, ‖kernelIFLeftSignedPinFactor ν f eps x q i a *
      ∫ g, kernelIFOuterSurvival eps a q g * H (kernelIFPhysicalSum a q g) ∂iidLaw ν‖
        ∂volume.restrict (Ioi (0 : ℝ))) ≤
      (kernelIFLeftTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal |H s|) x).toReal := by
  have hc : Measurable (kernelIFLeftSignedPinFactor ν f eps x q i) := by
    unfold kernelIFLeftSignedPinFactor
    exact measurable_const.mul ((measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf
      measurable_const measurable_id measurable_const measurable_const measurable_const _ _).mul
      (measurable_krDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const _))
  have hc0 (a : ℝ) : 0 ≤ kernelIFLeftSignedPinFactor ν f eps x q i a :=
    mul_nonneg hQ (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _)
      (krDens_nonneg ν hf0 _ _ _))
  have hH' : Measurable (fun p : ℝ × (ℕ → ℝ) => H (kernelIFPhysicalSum p.1 q p.2)) :=
    hH.comp (by unfold kernelIFPhysicalSum gapKeys; fun_prop)
  have hh := kernel_IF_signed_iterated_weight_norm ((volume.restrict (Ioi (0 : ℝ))).restrict S) (iidLaw ν)
    hc hc0 (measurable_kernelIFOuterSurvival_joint eps q)
    (fun p => kernel_IF_outer_survival_nonneg eps p.1 q p.2) hH'
    (by rwa [kernel_IF_left_total_densityOn_factor ν hf0 eps S q i hQ] at hfin)
  rw [kernel_IF_left_total_densityOn_factor ν hf0 eps S q i hQ]
  exact hh

theorem kernel_IF_right_signed_densityOn_norm (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hP : 0 ≤ kernelFacetP eps q) {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ)
    (hfin : kernelIFRightTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    (∫ a in S, ‖kernelIFRightSignedPinFactor ν f eps x q i a *
      ∫ g, kernelIFOuterSurvival eps a q g * H (kernelIFPhysicalSum a q g) ∂iidLaw ν‖
        ∂volume.restrict (Ioi (0 : ℝ))) ≤
      (kernelIFRightTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal |H s|) x).toReal := by
  have hc : Measurable (kernelIFRightSignedPinFactor ν f eps x q i) := by
    unfold kernelIFRightSignedPinFactor
    exact measurable_const.mul ((measurable_krDens_param ν measurableSet_Icc hf
      measurable_const measurable_id measurable_const measurable_const _).mul
      (measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const measurable_const _ _))
  have hc0 (a : ℝ) : 0 ≤ kernelIFRightSignedPinFactor ν f eps x q i a :=
    mul_nonneg hP (mul_nonneg (krDens_nonneg ν hf0 _ _ _)
      (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _))
  have hH' : Measurable (fun p : ℝ × (ℕ → ℝ) => H (kernelIFPhysicalSum p.1 q p.2)) :=
    hH.comp (by unfold kernelIFPhysicalSum gapKeys; fun_prop)
  have hh := kernel_IF_signed_iterated_weight_norm ((volume.restrict (Ioi (0 : ℝ))).restrict S) (iidLaw ν)
    hc hc0 (measurable_kernelIFOuterSurvival_joint eps q)
    (fun p => kernel_IF_outer_survival_nonneg eps p.1 q p.2) hH'
    (by rwa [kernel_IF_right_total_densityOn_factor ν hf0 eps S q i hP] at hfin)
  rw [kernel_IF_right_total_densityOn_factor ν hf0 eps S q i hP]
  exact hh


theorem kernel_IF_left_block_near_norm_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ Ioo (1/2 : ℝ) 2)
    (u l r m v : ℕ) (σ : Bool) {H : ℝ → ℝ} (hH : Measurable H)
    (hfin : kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    (∫ a in S, ‖kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r
      (if σ then 0 else w) (if σ then w else 0) *
      krInsertionCoefficientTerm ν f w σ σ (kernelIFInsertionReward H w σ σ) l r (u,m,v) a‖) ≤
      (kernelIFFacetTotalPinDensityOn ν f (w/2) S
        (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
        (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal |H s|) x).toReal := by
  classical
  let q := (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
  let i := (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1
  have hi : (q.1 : ℕ) ≤ i ∧ (i : ℕ) < q.2.1 := (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).2.2
  by_cases he : krInsertionEffective w σ l r m
  · have hE : kernelFacetEffective (w/2) q := (kernel_IF_left_block_effective w u l r m v σ).2 he
    by_cases hl : 0 < l+r
    · have hlong : (q.1 : ℕ)+1 < q.2.1 := by dsimp only [q,kernelIFLeftOfBlocks]; omega
      have hrepr (F : ℝ → ℝ≥0∞) :
          kernelIFFacetTotalPinDensityOn ν f (w/2) S q i F x =
            kernelIFLeftTotalPinDensityOn ν f (w/2) S q i F x := by
        simp only [kernelIFFacetTotalPinDensityOn,if_pos hE,if_pos hi,if_pos hlong]
      change kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x ≠ ∞ at hfin
      rw [hrepr] at hfin
      have hnorm := kernel_IF_left_signed_densityOn_norm ν hf hf0 (w/2) S q i
        hE.2.2.le hH x hfin
      have hmeasure : (volume.restrict (Ioi (0 : ℝ))).restrict S = volume.restrict S := by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr]
        intro a ha
        exact lt_trans (by norm_num : (0 : ℝ)<1/2) (hSI ha).1
      rw [hmeasure] at hnorm
      have heqterm (a : ℝ) := kernel_IF_left_block_signed_integrand ν f H w x a u l r m v σ
      have hE' := (kernel_IF_left_block_effective w u l r m v σ).2 he
      simp only [if_pos hE'] at heqterm
      change _ ≤ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal
      rw [hrepr]
      convert hnorm using 1
      apply integral_congr_ae
      exact ae_of_all _ (fun a => congrArg norm (heqterm a).symm)
    · have hl0 : l=0 := by omega
      have hr0 : r=0 := by omega
      subst l r
      have hshort : ¬ (q.1 : ℕ)+1 < q.2.1 := by dsimp only [q,kernelIFLeftOfBlocks]; omega
      have hz (F : ℝ → ℝ≥0∞) : kernelIFFacetTotalPinDensityOn ν f (w/2) S q i F x = 0 := by
        simp only [kernelIFFacetTotalPinDensityOn,if_pos hE,if_pos hi,if_neg hshort]
        exact kernel_IF_left_dirac_near_zero ν f hw hx hxw hSI u m v σ he F
      change _ ≤ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal
      simp only [hz,kernelMarkedFullDens,zero_mul,norm_zero,integral_zero,ENNReal.toReal_zero,le_refl]
  · have hE : ¬ kernelFacetEffective (w/2) q :=
      fun hh => he ((kernel_IF_left_block_effective w u l r m v σ).1 hh)
    have hz (a : ℝ) : krInsertionCoefficientTerm ν f w σ σ
        (kernelIFInsertionReward H w σ σ) l r (u,m,v) a = 0 := by
      simp [krInsertionCoefficientTerm,kernelIFInsertionReward,he]
    change _ ≤ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal
    simp only [kernelIFFacetTotalPinDensityOn,if_neg hE,hz,mul_zero,norm_zero,integral_zero,
      ENNReal.toReal_zero,le_refl]


theorem kernel_IF_right_block_near_norm_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ Ioo (1/2 : ℝ) 2)
    (u l r m v : ℕ) (σ : Bool) {H : ℝ → ℝ} (hH : Measurable H)
    (hfin : kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    (∫ a in S, ‖kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r
      (if !σ then 0 else w) (if !σ then w else 0) *
      krInsertionCoefficientTerm ν f w (!σ) σ (kernelIFInsertionReward H w (!σ) σ) l r (u,m,v) a‖) ≤
      (kernelIFFacetTotalPinDensityOn ν f (w/2) S
        (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
        (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal |H s|) x).toReal := by
  classical
  let q := (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
  let i := (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1
  have hi : (q.2.1 : ℕ) ≤ i ∧ (i : ℕ) < q.2.2.1 := (kernelIFRightOfBlocks (u,l,r,m,v,σ)).2.2
  have hnleft : ¬ ((q.1 : ℕ) ≤ i ∧ (i : ℕ) < q.2.1) := by omega
  by_cases he : krInsertionEffective w (!σ) l r m
  · have hE : kernelFacetEffective (w/2) q := (kernel_IF_right_block_effective w u l r m v σ).2 he
    by_cases hl : 0 < l+r
    · have hlong : (q.2.1 : ℕ)+1 < q.2.2.1 := by dsimp only [q,kernelIFRightOfBlocks]; omega
      have hrepr (F : ℝ → ℝ≥0∞) :
          kernelIFFacetTotalPinDensityOn ν f (w/2) S q i F x =
            kernelIFRightTotalPinDensityOn ν f (w/2) S q i F x := by
        simp only [kernelIFFacetTotalPinDensityOn,if_pos hE,if_neg hnleft,if_pos hi,if_pos hlong]
      change kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x ≠ ∞ at hfin
      rw [hrepr] at hfin
      have hnorm := kernel_IF_right_signed_densityOn_norm ν hf hf0 (w/2) S q i
        hE.2.1.le hH x hfin
      have hmeasure : (volume.restrict (Ioi (0 : ℝ))).restrict S = volume.restrict S := by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr]
        intro a ha
        exact lt_trans (by norm_num : (0 : ℝ)<1/2) (hSI ha).1
      rw [hmeasure] at hnorm
      have heqterm (a : ℝ) := kernel_IF_right_block_signed_integrand ν f H w x a u l r m v σ
      have hE' := (kernel_IF_right_block_effective w u l r m v σ).2 he
      simp only [if_pos hE'] at heqterm
      change _ ≤ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal
      rw [hrepr]
      convert hnorm using 1
      apply integral_congr_ae
      exact ae_of_all _ (fun a => congrArg norm (heqterm a).symm)
    · have hl0 : l=0 := by omega
      have hr0 : r=0 := by omega
      subst l r
      have hshort : ¬ (q.2.1 : ℕ)+1 < q.2.2.1 := by dsimp only [q,kernelIFRightOfBlocks]; omega
      have hz (F : ℝ → ℝ≥0∞) : kernelIFFacetTotalPinDensityOn ν f (w/2) S q i F x = 0 := by
        simp only [kernelIFFacetTotalPinDensityOn,if_pos hE,if_neg hnleft,if_pos hi,if_neg hshort]
        exact kernel_IF_right_dirac_near_zero ν f hw hx hxw hSI u m v σ he F
      change _ ≤ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal
      simp only [hz,kernelMarkedFullDens,zero_mul,norm_zero,integral_zero,ENNReal.toReal_zero,le_refl]
  · have hE : ¬ kernelFacetEffective (w/2) q :=
      fun hh => he ((kernel_IF_right_block_effective w u l r m v σ).1 hh)
    have hz (a : ℝ) : krInsertionCoefficientTerm ν f w (!σ) σ
        (kernelIFInsertionReward H w (!σ) σ) l r (u,m,v) a = 0 := by
      simp [krInsertionCoefficientTerm,kernelIFInsertionReward,he]
    change _ ≤ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal
    simp only [kernelIFFacetTotalPinDensityOn,if_neg hE,hz,mul_zero,norm_zero,integral_zero,
      ENNReal.toReal_zero,le_refl]

end
end PGM
