import PLAStochastic.Index.CEPS.Scaled.ZeroEndpointTaylor
import PLAStochastic.Index.CEPS.Scaled.DiscountScale
import PLAStochastic.Index.CEPS.Normal.ZeroMarkedPrimitiveLimit
import Mathlib.Topology.Piecewise

/-! # True marked and unmarked endpoint limits after physical scaling

The finite parts are defined by filling their proved punctured limits.
The marked endpoint is reconstructed from the discount and finite part;
its derivative at zero is minus the same true zero-discount endpoint.
-/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}

def cepsScaledUnmarkedEndpointMean (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (b : ℝ) : ℂ → ℂ :=
  Function.update (fun z => -(b : ℂ) ^ 2 *
    dom.halfZeroPoleRemoved ρW b (b : ℂ)⁻¹ ((b : ℂ) ^ 2 * z)) 0
      (cepsScaledZeroEndpoint dom ρW b)

def cepsScaledMarkedEndpointMean (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (b : ℝ) : ℂ → ℂ :=
  Function.update (fun z => -(b : ℂ) ^ 2 *
    dom.halfMarkedPoleRemoved ρW b (b : ℂ)⁻¹ ((b : ℂ) ^ 2 * z)) 0
      (cepsScaledZeroEndpoint dom ρW b)

def cepsScaledMarkedEndpoint (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (b : ℝ) (z : ℂ) : ℂ :=
  1 - cepsScaledMarkedDiscount ρW z b * cepsScaledMarkedEndpointMean dom ρW b z

private theorem scaled_discount_tendsto_punctured {b : ℝ} (hb : b ≠ 0) :
    Tendsto (fun z : ℂ => (b : ℂ) ^ 2 * z) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [Pi.mul_apply, id_eq, mul_zero] using!
      ((continuous_const.mul continuous_id).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simpa using mul_ne_zero (pow_ne_zero 2 (ofReal_ne_zero.mpr hb)) hz0

private theorem hasDerivAt_zero_mul_continuous {F G : ℂ → ℂ} {a : ℂ}
    (hF : HasDerivAt F a 0) (hF0 : F 0 = 0) (hG : ContinuousAt G 0) :
    HasDerivAt (fun z => F z * G z) (a * G 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := hF.tendsto_slope.mul (hG.tendsto.mono_left nhdsWithin_le_nhds)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  simp only [slope_def_field, hF0, zero_mul, sub_zero]
  ring

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledUnmarkedEndpointMean_continuousAt_zero {b : ℝ}
    (hb : 0 < b) (hsmall : |b| ≤ dom.μ₀) :
    ContinuousAt (cepsScaledUnmarkedEndpointMean dom ρW b) 0 := by
  unfold cepsScaledUnmarkedEndpointMean
  apply continuousAt_update_same.mpr
  have h := (dom.tendsto_halfZeroPoleRemoved hW hθ hD hsmall hb (b : ℂ)⁻¹).comp
    (scaled_discount_tendsto_punctured hb.ne')
  have hh := h.const_mul (-(b : ℂ) ^ 2)
  simpa only [cepsScaledZeroEndpoint_eq_physical dom hb.ne', Function.comp_apply] using! hh

include hW hθ hD in
theorem cepsScaledMarkedEndpointMean_continuousAt_zero {b : ℝ}
    (hb : 0 < b) (hsmall : |b| ≤ dom.μ₀) :
    ContinuousAt (cepsScaledMarkedEndpointMean dom ρW b) 0 := by
  unfold cepsScaledMarkedEndpointMean
  apply continuousAt_update_same.mpr
  have h := (dom.tendsto_halfMarkedPoleRemoved hW hθ hD hsmall hb (b : ℂ)⁻¹).comp
    (scaled_discount_tendsto_punctured hb.ne')
  have hh := h.const_mul (-(b : ℂ) ^ 2)
  simpa only [cepsScaledZeroEndpoint_eq_physical dom hb.ne', Function.comp_apply] using! hh

include hW hθ hD in
theorem cepsScaledMarkedDiscount_hasDerivAt_mark_zero {b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun z => cepsScaledMarkedDiscount ρW z b) 1 0 := by
  have hA := (cepsMarkedDiscount_analyticAt_zero hW hθ hD).differentiableAt.hasDerivAt
  rw [(cepsMarkedDiscount_zero_jets hW hθ hD).2.1] at hA
  have hB : HasDerivAt (fun z : ℂ => (b : ℂ) ^ 2 * z) ((b : ℂ) ^ 2) 0 :=
    by simpa only [mul_one] using! (hasDerivAt_id' (0 : ℂ)).const_mul ((b : ℂ) ^ 2)
  have hC := (hA.comp_of_eq (0 : ℂ) hB (by simp)).div_const ((b : ℂ) ^ 2)
  have hEq : (fun z => cepsScaledMarkedDiscount ρW z b) =
      (fun z => cepsMarkedDiscount ρW ((b : ℂ) ^ 2 * z) / (b : ℂ) ^ 2) :=
    funext fun z => cepsScaledMarkedDiscount_eq_div hW hθ hD z (ofReal_ne_zero.mpr hb)
  rw [hEq]
  convert! hC using 1
  field_simp [ofReal_ne_zero.mpr hb]

theorem cepsScaledMarkedEndpoint_zero (b : ℝ) :
    cepsScaledMarkedEndpoint dom ρW b 0 = 1 := by
  simp [cepsScaledMarkedEndpoint, cepsScaledMarkedDiscount]

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_hasDerivAt_zero {b : ℝ}
    (hb : 0 < b) (hsmall : |b| ≤ dom.μ₀) :
    HasDerivAt (cepsScaledMarkedEndpoint dom ρW b) (-cepsScaledZeroEndpoint dom ρW b) 0 := by
  have hD0 : cepsScaledMarkedDiscount ρW 0 b = 0 := by simp [cepsScaledMarkedDiscount]
  have hprod := hasDerivAt_zero_mul_continuous
    (cepsScaledMarkedDiscount_hasDerivAt_mark_zero hW hθ hD hb.ne') hD0
    (cepsScaledMarkedEndpointMean_continuousAt_zero dom hW hθ hD hb hsmall)
  simpa only [cepsScaledMarkedEndpoint, cepsScaledMarkedEndpointMean,
    Function.update_self, one_mul] using! hprod.const_sub 1

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_deriv_zero {b : ℝ}
    (hb : 0 < b) (hsmall : |b| ≤ dom.μ₀) :
    -deriv (cepsScaledMarkedEndpoint dom ρW b) 0 = cepsScaledZeroEndpoint dom ρW b := by
  rw [(cepsScaledMarkedEndpoint_hasDerivAt_zero dom hW hθ hD hb hsmall).deriv, neg_neg]

end PGM
