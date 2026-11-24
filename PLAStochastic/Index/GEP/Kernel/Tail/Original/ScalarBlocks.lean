import PLAStochastic.Index.GEP.Kernel.Influence.Pins.ScalarBlocks
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.Joint
import PLAStochastic.Index.GEP.Kernel.Tail.Original.Mass

/-! # From the actual physical block mass to the completed scalar tail series -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1600000

def kernelOuterPairAt (ν : ProbabilityMeasure ℝ) (w a : ℝ) (u v : ℕ) : ℝ :=
  krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u 0 * krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v 0 +
  krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u w * krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v w

theorem kernelOuterPairAt_nonneg (ν : ProbabilityMeasure ℝ) (w a : ℝ) (u v : ℕ) :
    0 ≤ kernelOuterPairAt ν w a u v :=
  add_nonneg (mul_nonneg (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _))
    (mul_nonneg (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _))

theorem kernelOuterPairAt_ge (ν : ProbabilityMeasure ℝ) (w a y : ℝ) (u v : ℕ)
    (hy : y = 0 ∨ y = w) :
    krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u y * krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v y ≤
      kernelOuterPairAt ν w a u v := by
  rcases hy with rfl | rfl
  · exact le_add_of_nonneg_right (mul_nonneg (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _))
  · exact le_add_of_nonneg_left (mul_nonneg (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _))

def kernelPairBoth (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w a x : ℝ) (l h m : ℕ) : ℝ :=
  kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h 0 w * krDens (Icc 0 w) ν f 1 a (m+1) w 0 +
  kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h w 0 * krDens (Icc 0 w) ν f 1 a (m+1) 0 w

theorem kernelPairBoth_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (w a x : ℝ) (l h m : ℕ) : 0 ≤ kernelPairBoth ν f w a x l h m :=
  add_nonneg (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _))
    (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _))

theorem kernelPairBoth_ge (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t)
    (w a x y z : ℝ) (l h m : ℕ) (hyz : (y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) :
    kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h y z * krDens (Icc 0 w) ν f 1 a (m+1) z y ≤
      kernelPairBoth ν f w a x l h m := by
  rcases hyz with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact le_add_of_nonneg_right (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _))
  · exact le_add_of_nonneg_left (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _))

def kernelScalarBulkBlock (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w x : ℝ)
    (u l h m v : ℕ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal
    (kernelOuterPairAt ν w a u v * (((m : ℝ) + 1 + w) * kernelPairBoth ν f w a x l h m))

def kernelScalarDiracBlock (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w x : ℝ)
    (u m v : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernelOuterPairAt ν w ((w+1)/x) u v *
    (((m : ℝ) + 1 + w) * kernelDiracPin ν f w (m+1) x))

/-- A scalar non-Dirac facet is bounded by the explicit common block kernel.
Both endpoint choices remain in the common kernel until the outer sums are taken. -/
theorem kernel_scalar_bulk_integrand_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w Q a x b y z : ℝ} (hw : 0 ≤ w)
    (u l h m v : ℕ) (hQ : Q ≤ (m : ℝ) + 1 + w)
    (hb : b = 0 ∨ b = w) (hyz : (y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) :
    ENNReal.ofReal Q * (ENNReal.ofReal (krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u b *
      krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v b) *
      (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h y z) *
        ENNReal.ofReal (krDens (Icc 0 w) ν f 1 a (m+1) z y))) ≤
      ENNReal.ofReal (kernelOuterPairAt ν w a u v * (((m : ℝ) + 1 + w) * kernelPairBoth ν f w a x l h m)) := by
  have hrow0 : 0 ≤ krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u b * krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v b :=
    mul_nonneg (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _)
  have hp0 : 0 ≤ kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h y z := kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _
  have hp1 : 0 ≤ krDens (Icc 0 w) ν f 1 a (m+1) z y := krDens_nonneg ν hf0 _ _ _
  calc
    _ ≤ ENNReal.ofReal ((m : ℝ) + 1 + w) * (ENNReal.ofReal (krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u b *
        krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v b) *
        (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h y z) *
          ENNReal.ofReal (krDens (Icc 0 w) ν f 1 a (m+1) z y))) := mul_le_mul' (ENNReal.ofReal_le_ofReal hQ) le_rfl
    _ = ENNReal.ofReal (((m : ℝ) + 1 + w) * ((krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) u b *
        krSurv (Icc 0 w) (ν : Measure ℝ) 1 a v b) *
        (kernelMarkedFullDens (Icc 0 w) ν f 1 a x l h y z * krDens (Icc 0 w) ν f 1 a (m+1) z y))) := by
      rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul hrow0,
        ← ENNReal.ofReal_mul (show 0 ≤ (m : ℝ) + 1 + w by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul (kernelOuterPairAt_ge ν w a b u v hb)
        (kernelPairBoth_ge ν hf0 w a x y z l h m hyz) (mul_nonneg hp0 hp1) (kernelOuterPairAt_nonneg ν w a u v)
      exact (mul_le_mul_of_nonneg_left hh (show 0 ≤ (m : ℝ) + 1 + w by positivity)).trans_eq (by ring))

/-- Canonical block coordinates remove all dependence on the outside lengths
from the two pins and the exact coarea coefficient. -/
theorem kernel_IF_left_scalar_block_formula (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFLeftPinDensity ν f eps (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1 (fun _ => 1) x =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal ((m : ℝ) + 1 + 2 * (if σ then 1 else -1) * eps) *
        (ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-a) u (if σ then 0 else 2*eps) *
          krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 a v (if σ then 0 else 2*eps)) *
          (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x l h
            (if σ then 0 else 2*eps) (if σ then 2*eps else 0)) *
            ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (m+1)
              (if σ then 2*eps else 0) (if σ then 0 else 2*eps)))) := by
  rw [kernel_IF_left_scalar_pin_density ν f eps _ _ (by
    simp only [kernelIFLeftOfBlocks]; omega)]
  have h₁ : u + l - u = l := by omega
  have h₂ : u + (l + h + 1) - (u + l) - 1 = h := by omega
  have h₃ : u + (l + h + 1) + (m + 1) - (u + (l + h + 1)) = m + 1 := by omega
  have h₄ : u + (l + h + 1) + (m + 1) + v - (u + (l + h + 1) + (m + 1)) = v := by omega
  simp only [kernelIFLeftOfBlocks, kernelFacetQ, fluxFacetSign, h₁, h₂, h₃, h₄]
  have hc : (u : ℝ) + (l + h + 1) + (m + 1) - ((u : ℝ) + (l + h + 1)) = (m : ℝ) + 1 := by ring
  cases σ <;> norm_num only [Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul,
    sub_self, Nat.cast_add, Nat.cast_one, hc]
  · have he : eps - -eps = 2 * eps := by ring
    have he' : eps + -eps = 0 := by ring
    simp only [he, he']
  · have he : eps + eps = 2 * eps := by ring
    simp only [he]

theorem kernel_IF_left_scalar_bulk_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {eps : ℝ} (heps : 0 ≤ eps)
    (x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFLeftPinDensity ν f eps (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1 (fun _ => 1) x ≤
        kernelScalarBulkBlock ν f (2*eps) x u l h m v := by
  rw [kernel_IF_left_scalar_block_formula]
  apply lintegral_mono
  intro a
  apply kernel_scalar_bulk_integrand_le ν hf0 (by positivity)
  · cases σ <;> norm_num
    linarith
  · cases σ <;> simp
  · cases σ <;> simp

theorem kernel_IF_right_scalar_block_formula (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFRightPinDensity ν f eps (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1 (fun _ => 1) x =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal ((m : ℝ) + 1 - 2 * (if σ then 1 else -1) * eps) *
        (ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-a) u (if σ then 0 else 2*eps) *
          krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 a v (if σ then 0 else 2*eps)) *
          (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (m+1)
              (if σ then 0 else 2*eps) (if σ then 2*eps else 0)) *
            ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x l h
              (if σ then 2*eps else 0) (if σ then 0 else 2*eps)))) := by
  rw [kernel_IF_right_scalar_pin_density ν f eps _ _ (by
    simp only [kernelIFRightOfBlocks]; omega)]
  have h₁ : u + (m+1) + l - (u + (m+1)) = l := by omega
  have h₂ : u + (m+1) + (l+h+1) - (u+(m+1)+l) - 1 = h := by omega
  have h₃ : u + (m+1) - u = m+1 := by omega
  have h₄ : u + (m+1) + (l+h+1) + v - (u + (m+1) + (l+h+1)) = v := by omega
  simp only [kernelIFRightOfBlocks, kernelFacetP, fluxFacetSign, h₁, h₂, h₃, h₄]
  have hc : (u : ℝ) + (m+1) - u = (m : ℝ)+1 := by ring
  cases σ <;> norm_num only [Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul,
    sub_self, Nat.cast_add, Nat.cast_one, hc]
  · have he : eps - -eps = 2 * eps := by ring
    have he' : eps + -eps = 0 := by ring
    simp only [he, he']
  · have he : eps + eps = 2 * eps := by ring
    simp only [he]

theorem kernel_IF_right_scalar_bulk_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {eps : ℝ} (heps : 0 ≤ eps)
    (x : ℝ) (u l h m v : ℕ) (σ : Bool) :
    kernelIFRightPinDensity ν f eps (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
      (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1 (fun _ => 1) x ≤
        kernelScalarBulkBlock ν f (2*eps) x u l h m v := by
  rw [kernel_IF_right_scalar_block_formula]
  apply lintegral_mono
  intro a
  dsimp only
  rw [mul_comm (ENNReal.ofReal (krDens _ _ _ _ _ _ _ _)) (ENNReal.ofReal (kernelMarkedFullDens _ _ _ _ _ _ _ _ _ _))]
  apply kernel_scalar_bulk_integrand_le ν hf0 (by positivity)
  · cases σ <;> norm_num
    linarith
  · cases σ <;> simp
  · cases σ <;> simp

theorem kernel_scalar_dirac_integrand_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w Q x y : ℝ} (hw : 0 ≤ w) (hx : 0 < x)
    (u m v : ℕ) (hQ : Q ≤ (m : ℝ) + 1 + w) (hy : y = 0 ∨ y = w) :
    ENNReal.ofReal (Q/x) * (ENNReal.ofReal (krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-((w+1)/x)) u y *
      krSurv (Icc 0 w) (ν : Measure ℝ) 1 ((w+1)/x) v y) *
      ENNReal.ofReal (krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w)) ≤
      kernelScalarDiracBlock ν f w x u m v := by
  have hrow0 : 0 ≤ krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-((w+1)/x)) u y *
      krSurv (Icc 0 w) (ν : Measure ℝ) 1 ((w+1)/x) v y :=
    mul_nonneg (krSurv_nonneg measurableSet_Icc ν _ _ _ _) (krSurv_nonneg measurableSet_Icc ν _ _ _ _)
  have hp0 : 0 ≤ krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w := krDens_nonneg ν hf0 _ _ _
  calc
    _ ≤ ENNReal.ofReal (((m : ℝ)+1+w)/x) * (ENNReal.ofReal (krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-((w+1)/x)) u y *
        krSurv (Icc 0 w) (ν : Measure ℝ) 1 ((w+1)/x) v y) *
        ENNReal.ofReal (krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hQ hx.le)) le_rfl
    _ = ENNReal.ofReal (((m : ℝ)+1+w)/x * ((krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-((w+1)/x)) u y *
        krSurv (Icc 0 w) (ν : Measure ℝ) 1 ((w+1)/x) v y) *
        krDens (Icc 0 w) ν f 1 ((w+1)/x) (m+1) 0 w)) := by
      rw [← ENNReal.ofReal_mul hrow0, ← ENNReal.ofReal_mul (show 0 ≤ ((m : ℝ)+1+w)/x by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_right (kernelOuterPairAt_ge ν w ((w+1)/x) y u v hy)
        (show 0 ≤ ((m : ℝ)+1+w) * kernelDiracPin ν f w (m+1) x from
          mul_nonneg (by positivity) (kernelDiracPin_nonneg ν hf0 w (m+1) hx.le))
      convert hh using 1 <;> first | rfl | (unfold kernelDiracPin; ring))

theorem kernel_IF_left_scalar_dirac_block_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {eps x : ℝ} (heps : 0 ≤ eps) (hx : 0 < x)
    (u m v : ℕ) :
    kernelIFLeftDiracPinDensity ν f eps (kernelIFLeftOfBlocks (u,0,0,m,v,false)).1.2.2
      (fun _ => 1) x ≤ kernelScalarDiracBlock ν f (2*eps) x u m v := by
  rw [kernel_IF_left_scalar_dirac_density ν f eps _ (by simp only [kernelIFLeftOfBlocks]; omega)]
  have h₃ : u+1+(m+1)-(u+1) = m+1 := by omega
  have h₄ : u+1+(m+1)+v-(u+1+(m+1)) = v := by omega
  have he : eps - -eps = 2 * eps := by ring
  have he' : eps + -eps = 0 := by ring
  have hP : (u : ℝ)+1-u-2*(-1)*eps = 2*eps+1 := by ring
  have hQ : (u : ℝ)+1+(m+1)-((u : ℝ)+1)+2*(-1)*eps = (m : ℝ)+1-2*eps := by ring
  simp only [kernelIFLeftOfBlocks, kernelFacetP, kernelFacetQ, fluxFacetSign,
    Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero, h₃, h₄,
    Nat.cast_add, Nat.cast_one, hP, hQ, neg_one_mul, he, he']
  exact kernel_scalar_dirac_integrand_le ν hf0 (by positivity) hx u m v (by linarith) (Or.inr rfl)

theorem kernel_IF_right_scalar_dirac_block_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {eps x : ℝ} (heps : 0 ≤ eps) (hx : 0 < x)
    (u m v : ℕ) :
    kernelIFRightDiracPinDensity ν f eps (kernelIFRightOfBlocks (u,0,0,m,v,true)).1.2.2
      (fun _ => 1) x ≤ kernelScalarDiracBlock ν f (2*eps) x u m v := by
  rw [kernel_IF_right_scalar_dirac_density ν f eps _ (by simp only [kernelIFRightOfBlocks]; omega)]
  have h₃ : u+(m+1)-u = m+1 := by omega
  have h₄ : u+(m+1)+1+v-(u+(m+1)+1) = v := by omega
  have he : eps + eps = 2 * eps := by ring
  have hP : (u : ℝ)+(m+1)-u-2*1*eps = (m : ℝ)+1-2*eps := by ring
  have hQ : (u : ℝ)+(m+1)+1-((u : ℝ)+(m+1))+2*1*eps = 2*eps+1 := by ring
  simp only [kernelIFRightOfBlocks, kernelFacetP, kernelFacetQ, fluxFacetSign,
    if_true, Nat.zero_add, Nat.add_zero, h₃, h₄,
    Nat.cast_add, Nat.cast_one, hP, hQ, one_mul, sub_self, he]
  exact kernel_scalar_dirac_integrand_le ν hf0 (by positivity) hx u m v (by linarith) (Or.inl rfl)

def kernelScalarBlockMajorant (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w x : ℝ)
    (p : KernelIFBlockIndex) : ℝ≥0∞ :=
  kernelScalarBulkBlock ν f w x p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 +
    if p.2.1 = 0 ∧ p.2.2.1 = 0 then kernelScalarDiracBlock ν f w x p.1 p.2.2.2.1 p.2.2.2.2.1 else 0

theorem kernel_IF_left_scalar_block_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {eps x : ℝ} (heps : 1 ≤ eps) (hx : 0 < x) (p : KernelIFBlockIndex) :
    kernelIFFacetPinDensity ν f eps (kernelIFLeftOfBlocks p).1.2.2
      (kernelIFLeftOfBlocks p).1.2.1 (fun _ => 1) x ≤ kernelScalarBlockMajorant ν f (2*eps) x p := by
  classical
  rcases p with ⟨u,l,h,m,v,σ⟩
  let q := (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.2
  let i : ℕ := (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).1.2.1
  change kernelIFFacetPinDensity ν f eps q i (fun _ => 1) x ≤ _
  unfold kernelIFFacetPinDensity
  by_cases heff : kernelFacetEffective eps q
  · rw [if_pos heff, if_pos (kernelIFLeftOfBlocks (u,l,h,m,v,σ)).2.2]
    by_cases hlong : (q.1 : ℕ)+1 < q.2.1
    · rw [if_pos hlong]
      exact (kernel_IF_left_scalar_bulk_le ν hf0 (by linarith) x u l h m v σ).trans le_self_add
    · rw [if_neg hlong]
      have hl : l = 0 := by dsimp [q, kernelIFLeftOfBlocks] at hlong; omega
      have hh : h = 0 := by dsimp [q, kernelIFLeftOfBlocks] at hlong; omega
      subst l h
      cases σ
      · exact (kernel_IF_left_scalar_dirac_block_le ν hf0 (by linarith) hx u m v).trans
          (by simp only [kernelScalarBlockMajorant, and_self, if_true]; exact le_add_self)
      · have hp := heff.2.1
        dsimp [q, kernelIFLeftOfBlocks, fluxFacetSign] at hp
        push_cast at hp
        linarith
  · rw [if_neg heff]
    exact bot_le

theorem kernel_IF_right_scalar_block_le (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {eps x : ℝ} (heps : 1 ≤ eps) (hx : 0 < x) (p : KernelIFBlockIndex) :
    kernelIFFacetPinDensity ν f eps (kernelIFRightOfBlocks p).1.2.2
      (kernelIFRightOfBlocks p).1.2.1 (fun _ => 1) x ≤ kernelScalarBlockMajorant ν f (2*eps) x p := by
  classical
  rcases p with ⟨u,l,h,m,v,σ⟩
  let q := (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.2
  let i : ℕ := (kernelIFRightOfBlocks (u,l,h,m,v,σ)).1.2.1
  have hnotleft : ¬((q.1 : ℕ) ≤ i ∧ i < q.2.1) := by
    dsimp [q, i, kernelIFRightOfBlocks]
    omega
  change kernelIFFacetPinDensity ν f eps q i (fun _ => 1) x ≤ _
  unfold kernelIFFacetPinDensity
  by_cases heff : kernelFacetEffective eps q
  · rw [if_pos heff, if_neg hnotleft, if_pos (kernelIFRightOfBlocks (u,l,h,m,v,σ)).2.2]
    by_cases hlong : (q.2.1 : ℕ)+1 < q.2.2.1
    · rw [if_pos hlong]
      exact (kernel_IF_right_scalar_bulk_le ν hf0 (by linarith) x u l h m v σ).trans le_self_add
    · rw [if_neg hlong]
      have hl : l = 0 := by dsimp [q, kernelIFRightOfBlocks] at hlong; omega
      have hh : h = 0 := by dsimp [q, kernelIFRightOfBlocks] at hlong; omega
      subst l h
      cases σ
      · have hp := heff.2.2
        dsimp [q, kernelIFRightOfBlocks, fluxFacetSign] at hp
        push_cast at hp
        linarith
      · exact (kernel_IF_right_scalar_dirac_block_le ν hf0 (by linarith) hx u m v).trans
          (by simp only [kernelScalarBlockMajorant, and_self, if_true]; exact le_add_self)
  · rw [if_neg heff]
    exact bot_le

end
end PGM
