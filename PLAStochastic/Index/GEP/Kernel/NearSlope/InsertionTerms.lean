import PLAStochastic.Index.GEP.Kernel.NearSlope.InsertionIntegrand

/-! # Exact original facet terms consumed by the near insertion AL bound -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

/-- The original left coefficient has negative sign exactly for the upward
marked bridge on the effective support. -/
theorem kernel_IF_left_block_coef_negative (w : ℝ) (u l r m v : ℕ) (σ : Bool)
    (he : krInsertionEffective w σ l r m) :
    (fluxFacetCoef (w/2) (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 < 0 ↔ σ = true) ∧
    (0 < fluxFacetCoef (w/2) (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 ↔ σ = false) := by
  have hvalid := (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).2.1
  have hi := (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).2.2
  rw [kernel_facet_coef_left hvalid hi.1 hi.2]
  have hpos := he.2
  cases σ <;> simp only [kernelIFLeftOfBlocks, fluxFacetSign, krInsertionOtherFactor,
    Bool.false_eq_true, if_false, if_true, Nat.cast_add, Nat.cast_one] at *
  all_goals constructor <;> constructor <;> intro h
  all_goals first | trivial | contradiction | linarith

/-- The original right coefficient has negative sign exactly for the downward
facet sign, equivalently for the upward marked orientation. -/
theorem kernel_IF_right_block_coef_negative (w : ℝ) (u l r m v : ℕ) (σ : Bool)
    (he : krInsertionEffective w (!σ) l r m) :
    (fluxFacetCoef (w/2) (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 < 0 ↔ σ = false) ∧
    (0 < fluxFacetCoef (w/2) (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 ↔ σ = true) := by
  have hvalid := (kernelIFRightOfBlocks (u,l,r,m,v,σ)).2.1
  have hi := (kernelIFRightOfBlocks (u,l,r,m,v,σ)).2.2
  rw [kernel_facet_coef_right hvalid hi.1 hi.2]
  have hpos := he.2
  cases σ <;> simp only [kernelIFRightOfBlocks, fluxFacetSign, krInsertionOtherFactor,
    Bool.false_eq_true, Bool.not_false, Bool.not_true, if_false, if_true,
    Nat.cast_add, Nat.cast_one] at *
  all_goals constructor <;> constructor <;> intro h
  all_goals first | trivial | contradiction | linarith


/-- At the original AL spatial scale an effective one-gap bridge has slope at
least two, and so contributes no mass to a near window contained in `(1/2,2)`. -/
theorem kernel_IF_left_dirac_near_zero (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    {S : Set ℝ} (hSI : S ⊆ Ioo (1/2 : ℝ) 2) (u m v : ℕ) (σ : Bool)
    (he : krInsertionEffective w σ 0 0 m) (H : ℝ → ℝ≥0∞) :
    kernelIFLeftTotalDiracPinDensityOn ν f (w/2) S
      (kernelIFLeftOfBlocks (u,0,0,m,v,σ)).1.2.2 H x = 0 := by
  classical
  have hs : σ = false := by
    cases σ
    · rfl
    · have hp := he.1
      norm_num at hp
      linarith
  subst σ
  have hroot : kernelFacetP (w/2) (kernelIFLeftOfBlocks (u,0,0,m,v,false)).1.2.2 = w+1 := by
    simp only [kernelFacetP,kernelIFLeftOfBlocks,fluxFacetSign,Bool.false_eq_true,if_false,
      Nat.cast_add,Nat.cast_zero,Nat.cast_one]
    ring
  unfold kernelIFLeftTotalDiracPinDensityOn
  rw [hroot, if_neg]
  intro ha
  have hh := (hSI ha).2
  have hl := (div_lt_iff₀ hx).mp hh
  linarith

theorem kernel_IF_right_dirac_near_zero (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    {S : Set ℝ} (hSI : S ⊆ Ioo (1/2 : ℝ) 2) (u m v : ℕ) (σ : Bool)
    (he : krInsertionEffective w (!σ) 0 0 m) (H : ℝ → ℝ≥0∞) :
    kernelIFRightTotalDiracPinDensityOn ν f (w/2) S
      (kernelIFRightOfBlocks (u,0,0,m,v,σ)).1.2.2 H x = 0 := by
  classical
  have hs : σ = true := by
    cases σ
    · have hp := he.1
      norm_num at hp
      linarith
    · rfl
  subst σ
  have hroot : kernelFacetQ (w/2) (kernelIFRightOfBlocks (u,0,0,m,v,true)).1.2.2 = w+1 := by
    simp only [kernelFacetQ,kernelIFRightOfBlocks,fluxFacetSign,if_true,
      Nat.cast_add,Nat.cast_zero,Nat.cast_one]
    ring
  unfold kernelIFRightTotalDiracPinDensityOn
  rw [hroot, if_neg]
  intro ha
  have hh := (hSI ha).2
  have hl := (div_lt_iff₀ hx).mp hh
  linarith

/-- Every original left facet, including its actual short Dirac branch, is the
signed near insertion integral once its absolute physical mass is finite. -/
theorem kernel_IF_left_block_near_signed_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ Ioo (1/2 : ℝ) 2)
    (u l r m v : ℕ) (σ : Bool) {H : ℝ → ℝ} (hH : Measurable H)
    (hfin : kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    IntegrableOn (fun a => kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r
      (if σ then 0 else w) (if σ then w else 0) *
      krInsertionCoefficientTerm ν f w σ σ (kernelIFInsertionReward H w σ σ) l r (u,m,v) a) S ∧
    (kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (H s)) x).toReal -
    (kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (-H s)) x).toReal =
      ∫ a in S, kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r
        (if σ then 0 else w) (if σ then w else 0) *
        krInsertionCoefficientTerm ν f w σ σ (kernelIFInsertionReward H w σ σ) l r (u,m,v) a := by
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
      obtain ⟨hint,heq⟩ := kernel_IF_left_signed_densityOn_integral ν hf hf0 (w/2) S q i
        hE.2.2.le hH x hfin
      have hmeasure : (volume.restrict (Ioi (0 : ℝ))).restrict S = volume.restrict S := by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr]
        intro a ha
        exact lt_trans (by norm_num : (0 : ℝ)<1/2) (hSI ha).1
      rw [IntegrableOn,hmeasure] at hint
      rw [hmeasure] at heq
      have heqterm (a : ℝ) := kernel_IF_left_block_signed_integrand ν f H w x a u l r m v σ
      have hE' := (kernel_IF_left_block_effective w u l r m v σ).2 he
      simp only [if_pos hE'] at heqterm
      refine ⟨hint.congr (ae_of_all _ heqterm),?_⟩
      change (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal = _
      rw [hrepr,hrepr,heq]
      exact integral_congr_ae (ae_of_all _ heqterm)
    · have hl0 : l=0 := by omega
      have hr0 : r=0 := by omega
      subst l r
      have hshort : ¬ (q.1 : ℕ)+1 < q.2.1 := by dsimp only [q,kernelIFLeftOfBlocks]; omega
      have hz (F : ℝ → ℝ≥0∞) : kernelIFFacetTotalPinDensityOn ν f (w/2) S q i F x = 0 := by
        simp only [kernelIFFacetTotalPinDensityOn,if_pos hE,if_pos hi,if_neg hshort]
        exact kernel_IF_left_dirac_near_zero ν f hw hx hxw hSI u m v σ he F
      change IntegrableOn _ S ∧ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal = _
      simp only [hz,kernelMarkedFullDens,zero_mul,integral_zero,ENNReal.toReal_zero,sub_self]
      exact ⟨integrableOn_zero,True.intro⟩
  · have hE : ¬ kernelFacetEffective (w/2) q :=
      fun hh => he ((kernel_IF_left_block_effective w u l r m v σ).1 hh)
    have hz (a : ℝ) : krInsertionCoefficientTerm ν f w σ σ
        (kernelIFInsertionReward H w σ σ) l r (u,m,v) a = 0 := by
      simp [krInsertionCoefficientTerm,kernelIFInsertionReward,he]
    change IntegrableOn _ S ∧ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal -
      (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal = _
    simp only [kernelIFFacetTotalPinDensityOn,if_neg hE,hz,mul_zero,integral_zero,
      ENNReal.toReal_zero,sub_self]
    exact ⟨integrableOn_zero,True.intro⟩


/-- Every original right facet, including its actual short Dirac branch, is the
signed near insertion integral once its absolute physical mass is finite. -/
theorem kernel_IF_right_block_near_signed_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) (hxw : 2*x ≤ w+1)
    {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ Ioo (1/2 : ℝ) 2)
    (u l r m v : ℕ) (σ : Bool) {H : ℝ → ℝ} (hH : Measurable H)
    (hfin : kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    IntegrableOn (fun a => kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r
      (if !σ then 0 else w) (if !σ then w else 0) *
      krInsertionCoefficientTerm ν f w (!σ) σ (kernelIFInsertionReward H w (!σ) σ) l r (u,m,v) a) S ∧
    (kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (H s)) x).toReal -
    (kernelIFFacetTotalPinDensityOn ν f (w/2) S
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,r,m,v,σ)).1.2.1 (fun s => ENNReal.ofReal (-H s)) x).toReal =
      ∫ a in S, kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r
        (if !σ then 0 else w) (if !σ then w else 0) *
        krInsertionCoefficientTerm ν f w (!σ) σ (kernelIFInsertionReward H w (!σ) σ) l r (u,m,v) a := by
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
      obtain ⟨hint,heq⟩ := kernel_IF_right_signed_densityOn_integral ν hf hf0 (w/2) S q i
        hE.2.1.le hH x hfin
      have hmeasure : (volume.restrict (Ioi (0 : ℝ))).restrict S = volume.restrict S := by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr]
        intro a ha
        exact lt_trans (by norm_num : (0 : ℝ)<1/2) (hSI ha).1
      rw [IntegrableOn,hmeasure] at hint
      rw [hmeasure] at heq
      have heqterm (a : ℝ) := kernel_IF_right_block_signed_integrand ν f H w x a u l r m v σ
      have hE' := (kernel_IF_right_block_effective w u l r m v σ).2 he
      simp only [if_pos hE'] at heqterm
      refine ⟨hint.congr (ae_of_all _ heqterm),?_⟩
      change (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal = _
      rw [hrepr,hrepr,heq]
      exact integral_congr_ae (ae_of_all _ heqterm)
    · have hl0 : l=0 := by omega
      have hr0 : r=0 := by omega
      subst l r
      have hshort : ¬ (q.2.1 : ℕ)+1 < q.2.2.1 := by dsimp only [q,kernelIFRightOfBlocks]; omega
      have hz (F : ℝ → ℝ≥0∞) : kernelIFFacetTotalPinDensityOn ν f (w/2) S q i F x = 0 := by
        simp only [kernelIFFacetTotalPinDensityOn,if_pos hE,if_neg hnleft,if_pos hi,if_neg hshort]
        exact kernel_IF_right_dirac_near_zero ν f hw hx hxw hSI u m v σ he F
      change IntegrableOn _ S ∧ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal -
        (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal = _
      simp only [hz,kernelMarkedFullDens,zero_mul,integral_zero,ENNReal.toReal_zero,sub_self]
      exact ⟨integrableOn_zero,True.intro⟩
  · have hE : ¬ kernelFacetEffective (w/2) q :=
      fun hh => he ((kernel_IF_right_block_effective w u l r m v σ).1 hh)
    have hz (a : ℝ) : krInsertionCoefficientTerm ν f w (!σ) σ
        (kernelIFInsertionReward H w (!σ) σ) l r (u,m,v) a = 0 := by
      simp [krInsertionCoefficientTerm,kernelIFInsertionReward,he]
    change IntegrableOn _ S ∧ (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal -
      (kernelIFFacetTotalPinDensityOn ν f (w/2) S q i _ x).toReal = _
    simp only [kernelIFFacetTotalPinDensityOn,if_neg hE,hz,mul_zero,integral_zero,
      ENNReal.toReal_zero,sub_self]
    exact ⟨integrableOn_zero,True.intro⟩

end
end PGM
