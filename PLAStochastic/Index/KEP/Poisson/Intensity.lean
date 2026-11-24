import PLAStochastic.Index.ModelK.Density
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Actual extended intensity profiles and cumulative intensity coordinates

A Model K density is extended by its endpoint values. The extension preserves
its original positive bounds and Lipschitz constant. Its cumulative integral
is a global order isomorphism; no invertibility premise is imposed on the model.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

structure KepIntensityProfile (f : ℝ → ℝ) (flo fhi L : ℝ) : Prop where
  pos : 0 < flo
  lower : ∀ x, flo ≤ f x
  upper : ∀ x, f x ≤ fhi
  lip_nonneg : 0 ≤ L
  lip : ∀ x y, |f x - f y| ≤ L * |x - y|

def kepExtendedDensity (f : ℝ → ℝ) (A B : ℝ) (x : ℝ) : ℝ :=
  f (max A (min x B))

theorem kepExtendedDensity_eq {f : ℝ → ℝ} {A B x : ℝ} (hx : x ∈ Icc A B) :
    kepExtendedDensity f A B x = f x := by
  simp only [kepExtendedDensity, min_eq_left hx.2, max_eq_right hx.1]

theorem kepExtendedDensity_profile {f : ℝ → ℝ} {A B flo fhi L : ℝ}
    (hf : DensityK f A B flo fhi L) :
    KepIntensityProfile (kepExtendedDensity f A B) flo fhi L := by
  have hm (x : ℝ) : max A (min x B) ∈ Icc A B :=
    ⟨le_max_left _ _, max_le hf.le (min_le_right _ _)⟩
  have hclamp : LipschitzWith 1 (fun x : ℝ => max A (min x B)) := by
    simpa only [max_comm, id_eq] using (LipschitzWith.id.min_const B).max_const A
  refine ⟨hf.pos, fun x => hf.lower _ (hm x), fun x => hf.upper _ (hm x),
    hf.lf_nonneg, ?_⟩
  intro x y
  apply (hf.lip _ (hm x) _ (hm y)).trans
  apply mul_le_mul_of_nonneg_left _ hf.lf_nonneg
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hclamp.dist_le_mul x y

namespace KepIntensityProfile

variable {f : ℝ → ℝ} {flo fhi L : ℝ} (hf : KepIntensityProfile f flo fhi L)
include hf

theorem f_pos (x : ℝ) : 0 < f x := hf.pos.trans_le (hf.lower x)

theorem fhi_pos : 0 < fhi := (hf.f_pos 0).trans_le (hf.upper 0)

theorem flo_le_fhi : flo ≤ fhi := (hf.lower 0).trans (hf.upper 0)

theorem lipschitzWith : LipschitzWith (Real.toNNReal L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hf.lip_nonneg]
  exact hf.lip x y

theorem continuous : Continuous f := hf.lipschitzWith.continuous

theorem intervalIntegrable (x y : ℝ) : IntervalIntegrable f volume x y :=
  hf.continuous.intervalIntegrable x y

end KepIntensityProfile

def kepIntensityPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in 0..x, f t

theorem kepIntensityPrimitive_zero (f : ℝ → ℝ) : kepIntensityPrimitive f 0 = 0 :=
  intervalIntegral.integral_same

theorem kepIntensityPrimitive_sub {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (x y : ℝ) :
    kepIntensityPrimitive f y - kepIntensityPrimitive f x = ∫ t in x..y, f t :=
  intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 y)
    (hf.intervalIntegrable 0 x)

theorem kepIntensityPrimitive_bracket {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) {x y : ℝ} (hxy : x ≤ y) :
    flo * (y - x) ≤ kepIntensityPrimitive f y - kepIntensityPrimitive f x ∧
      kepIntensityPrimitive f y - kepIntensityPrimitive f x ≤ fhi * (y - x) := by
  rw [kepIntensityPrimitive_sub hf]
  have hlo := intervalIntegral.integral_mono_on hxy intervalIntegrable_const
    (hf.intervalIntegrable x y) (fun t _ => hf.lower t)
  have hhi := intervalIntegral.integral_mono_on hxy (hf.intervalIntegrable x y)
    intervalIntegrable_const (fun t _ => hf.upper t)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  constructor <;> linarith only [hlo, hhi]

theorem kepIntensityPrimitive_hasDerivAt {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (x : ℝ) :
    HasDerivAt (kepIntensityPrimitive f) (f x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt

theorem kepIntensityPrimitive_continuous {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) : Continuous (kepIntensityPrimitive f) :=
  continuous_iff_continuousAt.mpr fun x => (kepIntensityPrimitive_hasDerivAt hf x).continuousAt

theorem kepIntensityPrimitive_strictMono {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) : StrictMono (kepIntensityPrimitive f) := by
  intro x y hxy
  have hlo := (kepIntensityPrimitive_bracket hf hxy.le).1
  have hp := mul_pos hf.pos (sub_pos.mpr hxy)
  linarith only [hlo, hp]

theorem kepIntensityPrimitive_surjective {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) : Function.Surjective (kepIntensityPrimitive f) := by
  intro z
  have hfp := hf.pos
  let b := |z| / flo + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hlo := (kepIntensityPrimitive_bracket hf (show -b ≤ 0 by linarith)).1
  have hhi := (kepIntensityPrimitive_bracket hf hb.le).1
  rw [kepIntensityPrimitive_zero] at hlo hhi
  have hbmul : flo * b = |z| + flo := by
    dsimp [b]
    field_simp [hfp.ne']
  have hlow : kepIntensityPrimitive f (-b) ≤ z := by
    nlinarith only [hlo, hbmul, neg_abs_le z, hf.pos]
  have hhigh : z ≤ kepIntensityPrimitive f b := by
    nlinarith only [hhi, hbmul, le_abs_self z, hf.pos]
  have hz := intermediate_value_Icc (show -b ≤ b by linarith)
    (kepIntensityPrimitive_continuous hf).continuousOn ⟨hlow, hhigh⟩
  obtain ⟨x, _, hx⟩ := hz
  exact ⟨x, hx⟩

def kepIntensityOrderIso {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (kepIntensityPrimitive f)
    (kepIntensityPrimitive_strictMono hf) (kepIntensityPrimitive_surjective hf)

theorem kepIntensityOrderIso_apply {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (x : ℝ) :
    kepIntensityOrderIso hf x = kepIntensityPrimitive f x := rfl

end

end PGM
