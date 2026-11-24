import PLAStochastic.Index.KEP.ReferenceScale.BridgeFluxBounds
import PLAStochastic.Index.KEP.ReferenceScale.LogSlopeNorm

/-!
# Boundary logarithmic-slope derivatives with one input first norm

The Ward identity and every internal transport pin retain the full physical
length rate. There is no product of two input derivative norms in this bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepFixedBridgeSlope_boundary_average {p p' q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hd : ∀ s t, HasDerivAt (p s) (p' s t) t)
    {σ w C J r : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hward : ∀ s t, q s t = -p s t + (σ - t) * p' s t)
    (hw : 0 ≤ w) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hK : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge p w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hfirst : ∀ m : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
      kepLogSlopeNorm (fun s => kepFixedBridgeRight p p' w s m x y) ≤
        C * J * Real.exp (-r * (m + 1 : ℕ)))
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepFixedBridgeSlope p q w s n x y) ≤
      8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J * Real.exp (-r * (n + 1 : ℕ)) := by
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> constructor <;> linarith
  have hyband : y ∈ Icc 0 w := by
    rcases hy with rfl | rfl <;> constructor <;> linarith
  let S := w + (n + 1 : ℕ)
  let E := Real.exp (-r * (n + 1 : ℕ))
  let K := fun s => kepFixedBridge p w s n x y
  let D := fun s => kepFixedBridgeRight p p' w s n x y
  let B := fun s => kepBridgeTransportFlux p w σ s n x y
  let c := (n + 1 : ℕ) * σ + x - y
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hS : 1 ≤ S := by dsimp [S]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnS : (n : ℝ) ≤ S := by dsimp [S]; push_cast; linarith
  have hS0 : 0 ≤ S := by linarith
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hc : |c| ≤ S := by
    have he : c = -(y - x - (n + 1 : ℕ) * σ) := by dsimp [c]; ring
    rw [he, abs_neg]
    exact kep_pin_coefficient_bound hσ hxband hyband n
  have hKc : Continuous K := (continuous_kepFixedBridge hp w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDc : Continuous D := (continuous_kepFixedBridgeRight hp hp' w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hBc : Continuous B := (continuous_kepBridgeTransportFlux hp w σ n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hKn : kepLogSlopeNorm K ≤ 2 * (C * E) :=
    kepLogSlopeNorm_uniform (by positivity) (fun s hs => hK s hs n x hxband y hyband)
  have hDn : kepLogSlopeNorm D ≤ C * J * E := hfirst n x y hx hy
  have hD0 := kepLogSlopeNorm_nonneg D
  have hBn : kepLogSlopeNorm B ≤ 2 * (2 * (n : ℝ) * S * C ^ 2 * E) :=
    kepLogSlopeNorm_uniform (by positivity) (fun s hs =>
      kepBridgeTransportFlux_exp_bound hp hw hC0 hσ (hK s hs) n hxband hyband)
  have he : (fun s => kepFixedBridgeSlope p q w s n x y) =
      (fun s => -K s + c * D s - B s) := by
    funext s
    exact kepFixedBridge_transport hp hp' hd hward hw s n x y
  have hC2 : C ≤ C ^ 2 := by nlinarith
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hSsq : 1 ≤ S ^ 2 := by nlinarith
  have ha : 2 * C ≤ 2 * C ^ 2 * S ^ 2 * J := by
    calc
      _ ≤ 2 * C ^ 2 := by gcongr
      _ ≤ 2 * C ^ 2 * S ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left hSsq (by positivity : 0 ≤ 2 * C ^ 2)
        nlinarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 2 * C ^ 2 * S ^ 2)
        nlinarith
  have hb : S * C * J ≤ C ^ 2 * S ^ 2 * J := by
    calc
      _ ≤ S ^ 2 * C ^ 2 * J := by gcongr
      _ = _ := by ring
  have hbb : 4 * (n : ℝ) * S * C ^ 2 ≤ 4 * C ^ 2 * S ^ 2 * J := by
    calc
      _ ≤ 4 * S * S * C ^ 2 := by gcongr
      _ ≤ 4 * S * S * C ^ 2 * J := by
        have hh := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ 4 * S * S * C ^ 2)
        nlinarith
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ kepLogSlopeNorm (fun s => -K s + c * D s) + kepLogSlopeNorm B :=
      kepLogSlopeNorm_sub_le (hKc.neg.add (hDc.const_mul c)) hBc
    _ ≤ (kepLogSlopeNorm (fun s => -K s) + kepLogSlopeNorm (fun s => c * D s)) +
        kepLogSlopeNorm B := by
      gcongr
      exact kepLogSlopeNorm_add_le hKc.neg (hDc.const_mul c)
    _ ≤ 2 * (C * E) + S * (C * J * E) + 2 * (2 * (n : ℝ) * S * C ^ 2 * E) := by
      rw [kepLogSlopeNorm_neg, kepLogSlopeNorm_const_mul]
      gcongr
    _ ≤ 8 * C ^ 2 * S ^ 2 * J * E := by
      have hm := mul_le_mul_of_nonneg_right (show 2 * C + S * C * J +
        4 * (n : ℝ) * S * C ^ 2 ≤ 8 * C ^ 2 * S ^ 2 * J by nlinarith) hE
      nlinarith

end

end PGM
