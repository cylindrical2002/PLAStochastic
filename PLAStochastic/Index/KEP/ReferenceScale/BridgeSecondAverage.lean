import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeFluxBudgets

/-!
# The second logarithmic-slope average separates its original spatial kernel

Only the original bridge carries a second spatial derivative. Every remaining
term is an explicit polynomial times one first input norm and the full killed
length rate. This is the coefficient estimate needed by the finite graph sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepLogSlopeNorm_add_six {F₁ F₂ F₃ F₄ F₅ F₆ : ℝ → ℝ}
    (h₁ : Continuous F₁) (h₂ : Continuous F₂) (h₃ : Continuous F₃)
    (h₄ : Continuous F₄) (h₅ : Continuous F₅) (h₆ : Continuous F₆) :
    kepLogSlopeNorm (fun s => F₁ s + F₂ s + F₃ s + F₄ s + F₅ s + F₆ s) ≤
      kepLogSlopeNorm F₁ + kepLogSlopeNorm F₂ + kepLogSlopeNorm F₃ +
        kepLogSlopeNorm F₄ + kepLogSlopeNorm F₅ + kepLogSlopeNorm F₆ := by
  have h12 := kepLogSlopeNorm_add_le h₁ h₂
  have h123 := kepLogSlopeNorm_add_le (h₁.add h₂) h₃
  have h1234 := kepLogSlopeNorm_add_le ((h₁.add h₂).add h₃) h₄
  have h12345 := kepLogSlopeNorm_add_le (((h₁.add h₂).add h₃).add h₄) h₅
  have h123456 := kepLogSlopeNorm_add_le ((((h₁.add h₂).add h₃).add h₄).add h₅) h₆
  simp only [kepLogSlopeNorm, Pi.add_apply] at h12 h123 h1234 h12345 h123456 ⊢
  linarith

def kepBridgeSecondRemainderBudget (C J w : ℝ) (n : ℕ) : ℝ :=
  let S := w + (n + 1 : ℕ)
  2 * C + 3 * S * C * J + 4 * (n : ℝ) * S * C ^ 2 +
    2 * (n : ℝ) * S ^ 2 * C ^ 2 * J + 32 * (n : ℝ) * S ^ 3 * C ^ 3 * J

theorem kepFixedBridgeSlopeSecondWard_boundary_average {p p' p'' q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hp'' : Continuous (Function.uncurry p'')) (hq : Continuous (Function.uncurry q))
    {σ w C J r : ℝ} (hσ : σ = 1 ∨ σ = -1) (hw : 0 ≤ w)
    (hC : 0 ≤ C) (_hJ : 0 ≤ J)
    (hK : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge p w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hfirst : ∀ m : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
      kepLogSlopeNorm (fun s => kepFixedBridgeRight p p' w s m x y) ≤
        C * J * Real.exp (-r * (m + 1 : ℕ)))
    (hBy : ∀ m : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
      kepLogSlopeNorm (fun s => kepBridgeFluxRight p p' w σ s m x y) ≤
        2 * (m : ℝ) * (w + (m + 1 : ℕ)) * C ^ 2 * J * Real.exp (-r * (m + 1 : ℕ)))
    (hBs : ∀ m : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
      kepLogSlopeNorm (fun s => kepBridgeFluxSlope p q w σ s m x y) ≤
        32 * (m : ℝ) * (w + (m + 1 : ℕ)) ^ 3 * C ^ 3 * J * Real.exp (-r * (m + 1 : ℕ)))
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepFixedBridgeSlopeSecondWard p p' p'' q w σ s n x y) ≤
      (w + (n + 1 : ℕ)) ^ 2 *
        kepLogSlopeNorm (fun s => kepFixedBridgeRight p p'' w s n x y) +
      kepBridgeSecondRemainderBudget C J w n * Real.exp (-r * (n + 1 : ℕ)) := by
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> constructor <;> linarith
  have hyband : y ∈ Icc 0 w := by
    rcases hy with rfl | rfl <;> constructor <;> linarith
  let S := w + (n + 1 : ℕ)
  let E := Real.exp (-r * (n + 1 : ℕ))
  let c := (n + 1 : ℕ) * σ + x - y
  let K := fun s => kepFixedBridge p w s n x y
  let D := fun s => kepFixedBridgeRight p p' w s n x y
  let DD := fun s => kepFixedBridgeRight p p'' w s n x y
  let B := fun s => kepBridgeTransportFlux p w σ s n x y
  let By := fun s => kepBridgeFluxRight p p' w σ s n x y
  let Bs := fun s => kepBridgeFluxSlope p q w σ s n x y
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hc : |c| ≤ S := by
    have he : c = -(y - x - (n + 1 : ℕ) * σ) := by dsimp [c]; ring
    rw [he, abs_neg]
    exact kep_pin_coefficient_bound hσ hxband hyband n
  have hc2 : c ^ 2 ≤ S ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg c) hc 2
  have hKc : Continuous K := (continuous_kepFixedBridge hp w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDc : Continuous D := (continuous_kepFixedBridgeRight hp hp' w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDDc : Continuous DD := (continuous_kepFixedBridgeRight hp hp'' w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hBc : Continuous B := (continuous_kepBridgeTransportFlux hp w σ n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hByc : Continuous By := continuous_kepBridgeFluxRight_slope hp hp' w σ n x y
  have hBsc : Continuous Bs := continuous_kepBridgeFluxSlope_slope hp hq w σ n x y
  have hKn : kepLogSlopeNorm K ≤ 2 * (C * E) :=
    kepLogSlopeNorm_uniform (by positivity) (fun s hs => hK s hs n x hxband y hyband)
  have hDn : kepLogSlopeNorm D ≤ C * J * E := hfirst n x y hx hy
  have hBn : kepLogSlopeNorm B ≤ 2 * (2 * (n : ℝ) * S * C ^ 2 * E) :=
    kepLogSlopeNorm_uniform (by positivity) (fun s hs =>
      kepBridgeTransportFlux_exp_bound hp hw hC hσ (hK s hs) n hxband hyband)
  have hByn : kepLogSlopeNorm By ≤ 2 * (n : ℝ) * S * C ^ 2 * J * E := hBy n x y hx hy
  have hBsn : kepLogSlopeNorm Bs ≤ 32 * (n : ℝ) * S ^ 3 * C ^ 3 * J * E := hBs n x y hx hy
  have hD0 := kepLogSlopeNorm_nonneg D
  have hDD0 := kepLogSlopeNorm_nonneg DD
  have hBy0 := kepLogSlopeNorm_nonneg By
  have he : (fun s => kepFixedBridgeSlopeSecondWard p p' p'' q w σ s n x y) =
      (fun s => K s + (-3 * c) * D s + c ^ 2 * DD s + B s + (-c) * By s + -Bs s) := by
    funext s
    dsimp [kepFixedBridgeSlopeSecondWard, K, D, DD, B, By, Bs, c]
    ring
  have h3 : |(-3 : ℝ) * c| = 3 * |c| := by rw [abs_mul]; norm_num
  rw [he]
  calc
    _ ≤ kepLogSlopeNorm K + kepLogSlopeNorm (fun s => (-3 * c) * D s) +
        kepLogSlopeNorm (fun s => c ^ 2 * DD s) + kepLogSlopeNorm B +
        kepLogSlopeNorm (fun s => (-c) * By s) + kepLogSlopeNorm (fun s => -Bs s) :=
      kepLogSlopeNorm_add_six hKc (hDc.const_mul _) (hDDc.const_mul _) hBc
        (hByc.const_mul _) hBsc.neg
    _ ≤ 2 * (C * E) + 3 * S * (C * J * E) + S ^ 2 * kepLogSlopeNorm DD +
        2 * (2 * (n : ℝ) * S * C ^ 2 * E) +
        S * (2 * (n : ℝ) * S * C ^ 2 * J * E) + 32 * (n : ℝ) * S ^ 3 * C ^ 3 * J * E := by
      rw [kepLogSlopeNorm_const_mul, kepLogSlopeNorm_const_mul, kepLogSlopeNorm_const_mul,
        kepLogSlopeNorm_neg, h3, abs_of_nonneg (sq_nonneg c), abs_neg]
      gcongr
    _ = _ := by dsimp [kepBridgeSecondRemainderBudget, S, E, DD]; ring

end

end PGM
