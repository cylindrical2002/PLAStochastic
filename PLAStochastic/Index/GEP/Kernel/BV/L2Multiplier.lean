import PLAStochastic.Index.GEP.Kernel.BV.FourierInverse

/-!
# Bounded multipliers and interval projections on the actual `L²` space

The operators here are constructed from measurable scalar functions. Their
pointwise representatives and norm bounds are proved from the `Lp` API.
-/

namespace PGM
noncomputable section
open MeasureTheory FourierTransform Set

abbrev KernelL2 := Lp ℂ 2 (volume : Measure ℝ)

theorem kBVMul_memLp {m : ℝ → ℂ} (hm : Measurable m) {B : ℝ}
    (hb : ∀ x, ‖m x‖ ≤ B) (u : KernelL2) : MemLp (fun x => m x * u x) 2 :=
  (Lp.memLp u).of_le_mul (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/-- Multiplication by a bounded measurable scalar, as an actual linear map on `L²`. -/
def kBVMulL2Map (m : ℝ → ℂ) (hm : Measurable m) (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B) :
    KernelL2 →ₗ[ℂ] KernelL2 where
  toFun u := (kBVMul_memLp hm hb u).toLp (fun x => m x * u x)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(kBVMul_memLp hm hb (u + v)).coeFn_toLp,
      Lp.coeFn_add ((kBVMul_memLp hm hb u).toLp _) ((kBVMul_memLp hm hb v).toLp _),
      (kBVMul_memLp hm hb u).coeFn_toLp, (kBVMul_memLp hm hb v).coeFn_toLp,
      Lp.coeFn_add u v] with x hx hsum hu hv huv
    rw [hx, hsum]
    simp only [Pi.add_apply] at huv ⊢
    rw [hu, hv, huv, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(kBVMul_memLp hm hb (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((kBVMul_memLp hm hb u).toLp _),
      (kBVMul_memLp hm hb u).coeFn_toLp, Lp.coeFn_smul c u] with x hx hc hu hcu
    simp only [RingHom.id_apply]
    rw [hx, hc]
    simp only [Pi.smul_apply, smul_eq_mul] at hcu ⊢
    rw [hu, hcu]
    ring

theorem kBVMulL2Map_coe {m : ℝ → ℂ} (hm : Measurable m) {B : ℝ}
    (hb : ∀ x, ‖m x‖ ≤ B) (u : KernelL2) :
    (kBVMulL2Map m hm B hb u : ℝ → ℂ) =ᵐ[volume] fun x => m x * u x :=
  (kBVMul_memLp hm hb u).coeFn_toLp

theorem kBVMulL2Map_bound {m : ℝ → ℂ} (hm : Measurable m) {B : ℝ}
    (hb : ∀ x, ‖m x‖ ≤ B) (u : KernelL2) : ‖kBVMulL2Map m hm B hb u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [kBVMulL2Map_coe hm hb u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

/-- The bounded measurable multiplier as a continuous linear operator. -/
def kBVMulL2 (m : ℝ → ℂ) (hm : Measurable m) (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B) :
    KernelL2 →L[ℂ] KernelL2 :=
  (kBVMulL2Map m hm B hb).mkContinuous B (kBVMulL2Map_bound hm hb)

theorem kBVMulL2_coe {m : ℝ → ℂ} (hm : Measurable m) {B : ℝ}
    (hb : ∀ x, ‖m x‖ ≤ B) (u : KernelL2) :
    (kBVMulL2 m hm B hb u : ℝ → ℂ) =ᵐ[volume] fun x => m x * u x :=
  kBVMulL2Map_coe hm hb u

theorem kBVMulL2_bound {m : ℝ → ℂ} (hm : Measurable m) {B : ℝ}
    (hb : ∀ x, ‖m x‖ ≤ B) (u : KernelL2) : ‖kBVMulL2 m hm B hb u‖ ≤ B * ‖u‖ :=
  kBVMulL2Map_bound hm hb u

theorem kBVMulL2_opNorm_le {m : ℝ → ℂ} (hm : Measurable m) {B : ℝ}
    (hb : ∀ x, ‖m x‖ ≤ B) : ‖kBVMulL2 m hm B hb‖ ≤ B :=
  (kBVMulL2 m hm B hb).opNorm_le_bound ((norm_nonneg (m 0)).trans (hb 0))
    (kBVMulL2_bound hm hb)

theorem kBV_indicator_norm_le_one (s : Set ℝ) (x : ℝ) :
    ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ s <;> simp [hx]

/-- The spatial or frequency interval projection on `L²`. -/
def kBVProject (s : Set ℝ) (hs : MeasurableSet s) : KernelL2 →L[ℂ] KernelL2 :=
  kBVMulL2 (s.indicator fun _ => (1 : ℂ)) (measurable_const.indicator hs) 1
    (kBV_indicator_norm_le_one s)

theorem kBVProject_coe (s : Set ℝ) (hs : MeasurableSet s) (u : KernelL2) :
    (kBVProject s hs u : ℝ → ℂ) =ᵐ[volume] s.indicator (u : ℝ → ℂ) := by
  unfold kBVProject
  filter_upwards [kBVMulL2_coe (measurable_const.indicator hs)
    (kBV_indicator_norm_le_one s) u] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem kBVProject_bound (s : Set ℝ) (hs : MeasurableSet s) (u : KernelL2) :
    ‖kBVProject s hs u‖ ≤ ‖u‖ := by
  simpa only [kBVProject, one_mul] using kBVMulL2_bound (measurable_const.indicator hs)
    (kBV_indicator_norm_le_one s) u

/-- The unitary Fourier and inverse transforms as continuous linear operators. -/
def kBVFourierL2 : KernelL2 →L[ℂ] KernelL2 := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv

def kBVFourierInvL2 : KernelL2 →L[ℂ] KernelL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.toContinuousLinearEquiv

@[simp] theorem kBVFourierL2_apply (u : KernelL2) : kBVFourierL2 u = 𝓕 u := rfl
@[simp] theorem kBVFourierInvL2_apply (u : KernelL2) : kBVFourierInvL2 u = 𝓕⁻ u := rfl

@[simp] theorem kBVFourierInvL2_norm (u : KernelL2) : ‖kBVFourierInvL2 u‖ = ‖u‖ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map u

end
end PGM
