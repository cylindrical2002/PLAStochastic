import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.OutputRewardBound
import PLAStochastic.Index.GEP.Kernel.Tail.Original.ScalarBlocks
import PLAStochastic.Index.GEP.Kernel.Influence.Reward.Mass

/-! # Physical majorants for the actual output facet blocks -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1600000

def kernelPhysicalOuterPairAt (ν : ProbabilityMeasure ℝ) (w s a : ℝ) (u v : ℕ) : ℝ :=
  kernelPhysicalSurv (Icc 0 w) ν (-1) (-a) s u 0 * kernelPhysicalSurv (Icc 0 w) ν 1 a s v 0 +
  kernelPhysicalSurv (Icc 0 w) ν (-1) (-a) s u w * kernelPhysicalSurv (Icc 0 w) ν 1 a s v w

theorem kernelPhysicalOuterPairAt_nonneg (ν : ProbabilityMeasure ℝ) (w s a : ℝ) (u v : ℕ) :
    0 ≤ kernelPhysicalOuterPairAt ν w s a u v :=
  add_nonneg (mul_nonneg (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))
    (mul_nonneg (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))

theorem kernelPhysicalOuterPairAt_ge (ν : ProbabilityMeasure ℝ) (w s a y : ℝ) (u v : ℕ)
    (hy : y = 0 ∨ y = w) :
    kernelPhysicalSurv (Icc 0 w) ν (-1) (-a) s u y * kernelPhysicalSurv (Icc 0 w) ν 1 a s v y ≤
      kernelPhysicalOuterPairAt ν w s a u v := by
  rcases hy with rfl | rfl
  · exact le_add_of_nonneg_right (mul_nonneg (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))
  · exact le_add_of_nonneg_left (mul_nonneg (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))

def kernelWeightedBulkBlock (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ)
    (u l h m v : ℕ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal
    (kernelPhysicalOuterPairAt ν w s a u v * (((m : ℝ)+1+w) *
      (Real.exp (s*((l : ℝ)+h+m+2)/a) * kernelPairBoth ν f w a x l h m)))

def kernelWeightedDiracBlock (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ)
    (u m v : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s ((w+1)/x) u v * (((m : ℝ)+1+w) *
    (Real.exp (s*((m : ℝ)+2)/((w+1)/x)) * kernelDiracPin ν f w (m+1) x)))

theorem kernel_output_bulk_integrand_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w Q a x y z s A b : ℝ} (hw : 0 ≤ w) (hA : 0 ≤ A)
    (u l h m v : ℕ) (hQ : Q ≤ (m : ℝ)+1+w)
    (hy : b = 0 ∨ b = w) (hyz : (y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) :
    ENNReal.ofReal Q * ((ENNReal.ofReal A *
      (ENNReal.ofReal (Real.exp (s*((l : ℝ)+h+m+2)/a)) *
        (ENNReal.ofReal (kernelPhysicalSurv (Icc 0 w) ν (-1) (-a) s u b) *
         ENNReal.ofReal (kernelPhysicalSurv (Icc 0 w) ν 1 a s v b)))) *
      (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h y z) *
       ENNReal.ofReal (krDens (Icc 0 w) ν f 1 a (m+1) z y))) ≤
    ENNReal.ofReal A * ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v *
      (((m : ℝ)+1+w) * (Real.exp (s*((l : ℝ)+h+m+2)/a) * kernelPairBoth ν f w a x l h m))) := by
  have hrow0 := mul_nonneg (kernelPhysicalSurv_nonneg (Icc 0 w) ν (-1) (-a) s u b)
    (kernelPhysicalSurv_nonneg (Icc 0 w) ν 1 a s v b)
  have hp0 := kernelMarkedFullDens_nonneg (J := Icc 0 w) ν hf0 1 a x l h y z
  have hp1 := krDens_nonneg ν hf0 (m+1) z y (β := 1) (a := a) (J := Icc 0 w)
  apply (mul_le_mul' (ENNReal.ofReal_le_ofReal hQ) le_rfl).trans
  rw [← ENNReal.ofReal_mul (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _),
    ← ENNReal.ofReal_mul hp0,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul (mul_nonneg hA (mul_nonneg (Real.exp_nonneg _) hrow0)),
    ← ENNReal.ofReal_mul (show 0 ≤ (m : ℝ)+1+w by positivity), ← ENNReal.ofReal_mul hA]
  apply ENNReal.ofReal_le_ofReal
  have hp := mul_le_mul (kernelPhysicalOuterPairAt_ge ν w s a b u v hy)
    (kernelPairBoth_ge ν hf0 w a x y z l h m hyz) (mul_nonneg hp0 hp1)
    (kernelPhysicalOuterPairAt_nonneg ν w s a u v)
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ A*((m : ℝ)+1+w)*Real.exp (s*((l : ℝ)+h+m+2)/a) by positivity)
  nlinarith only [hh]

theorem kernel_IF_left_output_outer_le {D θ vlo vhi η M C eps a : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) (ha : 0 < a) (u l h m v : ℕ) (σ : Bool) :
    (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a
      (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2 g) *
      ENNReal.ofReal |kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a
        (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2 g)| ∂iidLaw ν) ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) *
      (ENNReal.ofReal (Real.exp ((η/C)*((l : ℝ)+h+m+2)/a)) *
        (ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν (-1) (-a) (η/C) u
          (if σ then 0 else 2*eps)) *
         ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν 1 a (η/C) v
          (if σ then 0 else 2*eps)))) := by
  have hh := kernel_IF_reward_physical_outer_le (eps := eps) hν hθ hψ hη hC hscale ha
    (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).2.1
  have ht : u+(l+h+1)+(m+1)+v-(u+(l+h+1)+(m+1))=v := by omega
  have he : ((u : ℝ)+(l+h+1)+(m+1)-u) = (l : ℝ)+h+m+2 := by ring
  have hd : (η/C)*(((l : ℝ)+h+m+2)/a) = (η/C)*((l : ℝ)+h+m+2)/a := by ring
  cases σ <;> simpa only [kernelIFLeftOfBlocks, fluxFacetSign, Bool.false_eq_true,
    if_false, if_true, one_mul, neg_one_mul, sub_self, ht, Nat.cast_add, Nat.cast_one, he, hd,
    show eps - -eps = 2*eps by ring] using hh

theorem kernel_IF_right_output_outer_le {D θ vlo vhi η M C eps a : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) (ha : 0 < a) (u l h m v : ℕ) (σ : Bool) :
    (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a
      (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2 g) *
      ENNReal.ofReal |kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a
        (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2 g)| ∂iidLaw ν) ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) *
      (ENNReal.ofReal (Real.exp ((η/C)*((l : ℝ)+h+m+2)/a)) *
        (ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν (-1) (-a) (η/C) u
          (if σ then 0 else 2*eps)) *
         ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν 1 a (η/C) v
          (if σ then 0 else 2*eps)))) := by
  have hh := kernel_IF_reward_physical_outer_le (eps := eps) hν hθ hψ hη hC hscale ha
    (kernelIFRightOfBlocks (u,l,h,m,v,σ)).2.1
  have ht : u+(m+1)+(l+h+1)+v-(u+(m+1)+(l+h+1))=v := by omega
  have he : ((u : ℝ)+(m+1)+(l+h+1)-u) = (l : ℝ)+h+m+2 := by ring
  have hd : (η/C)*(((l : ℝ)+h+m+2)/a) = (η/C)*((l : ℝ)+h+m+2)/a := by ring
  cases σ <;> simpa only [kernelIFRightOfBlocks, fluxFacetSign, Bool.false_eq_true,
    if_false, if_true, one_mul, neg_one_mul, sub_self, ht, Nat.cast_add, Nat.cast_one, he, hd,
    show eps - -eps = 2*eps by ring] using hh


theorem kernel_IF_left_output_bulk_le {D θ vlo vhi η M C eps : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 0 ≤ eps)
    (x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFLeftTotalPinDensity ν f eps (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBulkBlock ν f (2*eps) (η/C) x u l h m v := by
  unfold kernelIFLeftTotalPinDensity kernelWeightedBulkBlock
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
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

theorem kernel_IF_right_output_bulk_le {D θ vlo vhi η M C eps : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 0 ≤ eps)
    (x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFRightTotalPinDensity ν f eps (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBulkBlock ν f (2*eps) (η/C) x u l h m v := by
  unfold kernelIFRightTotalPinDensity kernelWeightedBulkBlock
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
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


theorem kernel_output_dirac_integrand_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w Q x y s A : ℝ} (hw : 0 ≤ w) (hx : 0 < x) (hA : 0 ≤ A)
    (u m v : ℕ) (hQ : Q ≤ (m : ℝ)+1+w) (hy : y = 0 ∨ y = w) :
    ENNReal.ofReal (Q/x) * ((ENNReal.ofReal A *
      (ENNReal.ofReal (Real.exp (s*((m : ℝ)+2)/((w+1)/x))) *
        (ENNReal.ofReal (kernelPhysicalSurv (Icc 0 w) ν (-1) (-((w+1)/x)) s u y) *
         ENNReal.ofReal (kernelPhysicalSurv (Icc 0 w) ν 1 ((w+1)/x) s v y)))) *
      ENNReal.ofReal (krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w)) ≤
    ENNReal.ofReal A * kernelWeightedDiracBlock ν f w s x u m v := by
  have hrow0 := mul_nonneg (kernelPhysicalSurv_nonneg (Icc 0 w) ν (-1) (-((w+1)/x)) s u y)
    (kernelPhysicalSurv_nonneg (Icc 0 w) ν 1 ((w+1)/x) s v y)
  have hp0 : 0 ≤ krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w := krDens_nonneg ν hf0 _ _ _
  apply (mul_le_mul' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hQ hx.le)) le_rfl).trans
  unfold kernelWeightedDiracBlock
  rw [← ENNReal.ofReal_mul (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul (mul_nonneg hA (mul_nonneg (Real.exp_nonneg _) hrow0)),
    ← ENNReal.ofReal_mul (show 0 ≤ ((m : ℝ)+1+w)/x by positivity), ← ENNReal.ofReal_mul hA]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right (kernelPhysicalOuterPairAt_ge ν w s ((w+1)/x) y u v hy)
    (show 0 ≤ A*((m : ℝ)+1+w)*Real.exp (s*((m : ℝ)+2)/((w+1)/x))*kernelDiracPin ν f w (m+1) x from
      mul_nonneg (by positivity) (kernelDiracPin_nonneg ν hf0 w (m+1) hx.le))
  let R := kernelPhysicalSurv (Icc 0 w) ν (-1) (-((w+1)/x)) s u y *
    kernelPhysicalSurv (Icc 0 w) ν 1 ((w+1)/x) s v y
  let O := kernelPhysicalOuterPairAt ν w s ((w+1)/x) u v
  let E := Real.exp (s*((m : ℝ)+2)/((w+1)/x))
  let P := krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w
  change R*(A*((m : ℝ)+1+w)*E*(P/x)) ≤ O*(A*((m : ℝ)+1+w)*E*(P/x)) at hh
  change ((m : ℝ)+1+w)/x*(A*(E*R)*P) ≤ A*(O*(((m : ℝ)+1+w)*(E*(P/x))))
  calc
    _ = R*(A*((m : ℝ)+1+w)*E*(P/x)) := by ring
    _ ≤ O*(A*((m : ℝ)+1+w)*E*(P/x)) := hh
    _ = _ := by ring

theorem kernel_IF_left_output_dirac_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 0 ≤ eps)
    (hx : 0 < x) (u m v : ℕ) :
    kernelIFLeftTotalDiracPinDensity ν f eps (kernelIFLeftOfBlocks (u,0,0,m,v,false)).1.2.2
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedDiracBlock ν f (2*eps) (η/C) x u m v := by
  have hP : kernelFacetP eps (kernelIFLeftOfBlocks (u,0,0,m,v,false)).1.2.2 = 2*eps+1 := by
    simp only [kernelIFLeftOfBlocks, kernelFacetP, fluxFacetSign, Bool.false_eq_true, if_false,
      Nat.zero_add, Nat.add_zero, Nat.cast_add, Nat.cast_one]
    ring
  unfold kernelIFLeftTotalDiracPinDensity
  rw [hP]
  have hb := kernel_IF_left_output_outer_le (eps := eps) hν hθ hψ hη hC hscale
    (show 0 < (2*eps+1)/x by positivity) u 0 0 m v false
  apply (mul_le_mul' le_rfl (mul_le_mul' hb le_rfl)).trans
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hh := kernel_output_dirac_integrand_le ν hf0 (s := η/C) (x := x)
    (show 0 ≤ 2*eps by positivity) hx (show 0 ≤ M*(8*D/θ^2)/C by positivity)
    u m v (show (m : ℝ)+1-2*eps ≤ (m : ℝ)+1+2*eps by linarith) (Or.inr rfl)
  have h₃ : u+1+(m+1)-(u+1)=m+1 := by omega
  have hQ : (u : ℝ)+1+(m+1)-((u : ℝ)+1)+2*(-1)*eps=(m : ℝ)+1-2*eps := by ring
  simpa only [kernelIFLeftOfBlocks, kernelFacetQ, fluxFacetSign, Bool.false_eq_true, if_false,
    Nat.zero_add, Nat.add_zero, h₃, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
    hQ, neg_one_mul, show eps - -eps = 2*eps by ring, show eps + -eps = 0 by ring] using hh

theorem kernel_IF_right_output_dirac_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 0 ≤ eps)
    (hx : 0 < x) (u m v : ℕ) :
    kernelIFRightTotalDiracPinDensity ν f eps (kernelIFRightOfBlocks (u,0,0,m,v,true)).1.2.2
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedDiracBlock ν f (2*eps) (η/C) x u m v := by
  have hQ : kernelFacetQ eps (kernelIFRightOfBlocks (u,0,0,m,v,true)).1.2.2 = 2*eps+1 := by
    simp only [kernelIFRightOfBlocks, kernelFacetQ, fluxFacetSign, if_true,
      Nat.zero_add, Nat.add_zero, Nat.cast_add, Nat.cast_one]
    ring
  unfold kernelIFRightTotalDiracPinDensity
  rw [hQ]
  have hb := kernel_IF_right_output_outer_le (eps := eps) hν hθ hψ hη hC hscale
    (show 0 < (2*eps+1)/x by positivity) u 0 0 m v true
  apply (mul_le_mul' le_rfl (mul_le_mul' hb le_rfl)).trans
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hh := kernel_output_dirac_integrand_le ν hf0 (s := η/C) (x := x)
    (show 0 ≤ 2*eps by positivity) hx (show 0 ≤ M*(8*D/θ^2)/C by positivity)
    u m v (show (m : ℝ)+1-2*eps ≤ (m : ℝ)+1+2*eps by linarith) (Or.inl rfl)
  have h₃ : u+(m+1)-u=m+1 := by omega
  have hP : (u : ℝ)+(m+1)-u-2*1*eps=(m : ℝ)+1-2*eps := by ring
  simpa only [kernelIFRightOfBlocks, kernelFacetP, fluxFacetSign, if_true,
    Nat.zero_add, Nat.add_zero, h₃, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
    hP, one_mul, sub_self, show eps + eps = 2*eps by ring] using hh


def kernelWeightedBlockMajorant (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ)
    (p : KernelIFBlockIndex) : ℝ≥0∞ :=
  kernelWeightedBulkBlock ν f w s x p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 +
    if p.2.1 = 0 ∧ p.2.2.1 = 0 then kernelWeightedDiracBlock ν f w s x p.1 p.2.2.2.1 p.2.2.2.2.1 else 0


theorem kernel_IF_left_output_block_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 1 ≤ eps)
    (hx : 0 < x) (p : KernelIFBlockIndex) :
    kernelIFFacetTotalPinDensity ν f eps (kernelIFLeftOfBlocks p).1.2.2
      (kernelIFLeftOfBlocks p).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBlockMajorant ν f (2*eps) (η/C) x p := by
  classical
  rcases p with ⟨u,l,h,m,v,σ⟩
  let q := (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
  let i : ℕ := (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1
  change kernelIFFacetTotalPinDensity ν f eps q i (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤ _
  unfold kernelIFFacetTotalPinDensity
  by_cases heff : kernelFacetEffective eps q
  · rw [if_pos heff, if_pos (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).2.2]
    by_cases hlong : (q.1 : ℕ)+1 < q.2.1
    · rw [if_pos hlong]
      exact (kernel_IF_left_output_bulk_le hν hθ hψ hη hC hscale hf0 (by linarith) x u l h m v σ).trans (mul_le_mul' le_rfl le_self_add)
    · rw [if_neg hlong]
      have hl : l = 0 := by dsimp [q, kernelIFLeftOfBlocks] at hlong; omega
      have hh : h = 0 := by dsimp [q, kernelIFLeftOfBlocks] at hlong; omega
      subst l h
      cases σ
      · exact (kernel_IF_left_output_dirac_le hν hθ hψ hη hC hscale hf0 (by linarith) hx u m v).trans
          (by simp only [kernelWeightedBlockMajorant, and_self, if_true]; exact mul_le_mul' le_rfl le_add_self)
      · have hp := heff.2.1
        dsimp [q, kernelIFLeftOfBlocks, fluxFacetSign] at hp
        push_cast at hp
        linarith
  · rw [if_neg heff]
    exact bot_le


theorem kernel_IF_right_output_block_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t) (heps : 1 ≤ eps)
    (hx : 0 < x) (p : KernelIFBlockIndex) :
    kernelIFFacetTotalPinDensity ν f eps (kernelIFRightOfBlocks p).1.2.2
      (kernelIFRightOfBlocks p).1.2.1
      (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤
    ENNReal.ofReal (M*(8*D/θ^2)/C) * kernelWeightedBlockMajorant ν f (2*eps) (η/C) x p := by
  classical
  rcases p with ⟨u,l,h,m,v,σ⟩
  let q := (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
  let i : ℕ := (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1
  have hnotleft : ¬((q.1 : ℕ) ≤ i ∧ i < q.2.1) := by
    dsimp [q, i, kernelIFRightOfBlocks]
    omega
  change kernelIFFacetTotalPinDensity ν f eps q i (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) x ≤ _
  unfold kernelIFFacetTotalPinDensity
  by_cases heff : kernelFacetEffective eps q
  · rw [if_pos heff, if_neg hnotleft, if_pos (kernelIFRightOfBlocks (u,l,h,m,v,σ)).2.2]
    by_cases hlong : (q.2.1 : ℕ)+1 < q.2.2.1
    · rw [if_pos hlong]
      exact (kernel_IF_right_output_bulk_le hν hθ hψ hη hC hscale hf0 (by linarith) x u l h m v σ).trans (mul_le_mul' le_rfl le_self_add)
    · rw [if_neg hlong]
      have hl : l = 0 := by dsimp [q, kernelIFRightOfBlocks] at hlong; omega
      have hh : h = 0 := by dsimp [q, kernelIFRightOfBlocks] at hlong; omega
      subst l h
      cases σ
      · have hp := heff.2.2
        dsimp [q, kernelIFRightOfBlocks, fluxFacetSign] at hp
        push_cast at hp
        linarith
      · exact (kernel_IF_right_output_dirac_le hν hθ hψ hη hC hscale hf0 (by linarith) hx u m v).trans
          (by simp only [kernelWeightedBlockMajorant, and_self, if_true]; exact mul_le_mul' le_rfl le_add_self)
  · rw [if_neg heff]
    exact bot_le

end
end PGM
