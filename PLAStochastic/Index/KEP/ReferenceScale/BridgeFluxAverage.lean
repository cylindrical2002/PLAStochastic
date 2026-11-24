import PLAStochastic.Index.KEP.ReferenceScale.BridgeSlopeBudget

/-!
# Absolute slope budgets for differentiated internal pins

Each differentiated transport pin contains one differentiated bridge. Its
other bridge retains the pointwise killed bound, so the two lengths combine
without squaring the input derivative norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepLogSlopeNorm_pin_product {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    {C A r b S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : |b| ≤ S)
    {n l : ℕ} (hl : l < n)
    (hFn : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |F s| ≤ C * Real.exp (-r * (l + 1 : ℕ)))
    (hGn : kepLogSlopeNorm G ≤ A * Real.exp (-r * (n - 1 - l + 1 : ℕ))) :
    kepLogSlopeNorm (fun s => b * F s * G s) ≤
      S * C * A * Real.exp (-r * (n + 1 : ℕ)) := by
  have he : (fun s => b * F s * G s) = fun s => b * (F s * G s) := by
    funext s
    ring
  rw [he, kepLogSlopeNorm_const_mul]
  calc
    _ ≤ S * kepLogSlopeNorm (fun s => F s * G s) :=
      mul_le_mul_of_nonneg_right hb (kepLogSlopeNorm_nonneg _)
    _ ≤ S * ((C * Real.exp (-r * (l + 1 : ℕ))) * kepLogSlopeNorm G) :=
      mul_le_mul_of_nonneg_left (kepLogSlopeNorm_mul_bound hF hG hFn) hS
    _ ≤ S * ((C * Real.exp (-r * (l + 1 : ℕ))) *
        (A * Real.exp (-r * (n - 1 - l + 1 : ℕ)))) := by
      gcongr
    _ = S * C * A *
        (Real.exp (-r * (l + 1 : ℕ)) * Real.exp (-r * (n - 1 - l + 1 : ℕ))) := by ring
    _ = _ := by rw [kep_pin_length_exp hl]

theorem kepBridgeFluxRight_boundary_average {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    {σ w C J r : ℝ} (hσ : σ = 1 ∨ σ = -1) (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hK : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge p w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hfirst : ∀ m : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
      kepLogSlopeNorm (fun s => kepFixedBridgeRight p p' w s m x y) ≤
        C * J * Real.exp (-r * (m + 1 : ℕ)))
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepBridgeFluxRight p p' w σ s n x y) ≤
      2 * (n : ℝ) * (w + (n + 1 : ℕ)) * C ^ 2 * J *
        Real.exp (-r * (n + 1 : ℕ)) := by
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> constructor <;> linarith
  have hb0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hbw : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
  let S := w + (n + 1 : ℕ)
  let E := Real.exp (-r * (n + 1 : ℕ))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hk (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridge p w s m u v) :=
    (continuous_kepFixedBridge hp w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hr (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridgeRight p p' w s m u v) :=
    (continuous_kepFixedBridgeRight hp hp' w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hcoeff (l : ℕ) (hl : l < n) (b : ℝ) (hb : b ∈ Icc 0 w) :
      |b - x - (l + 1 : ℕ) * σ| ≤ S := by
    have hh := kep_pin_coefficient_bound hσ hxband hb l
    have hln : (l : ℝ) ≤ n := by exact_mod_cast hl.le
    dsimp [S]
    push_cast at hh ⊢
    linarith
  have ht (l : ℕ) (hl : l ∈ Finset.range n) (b : ℝ) (hb : b ∈ Icc 0 w)
      (hbe : b = 0 ∨ b = w) :
      kepLogSlopeNorm (fun s => (b - x - (l + 1 : ℕ) * σ) *
        kepFixedBridge p w s l x b * kepFixedBridgeRight p p' w s (n - 1 - l) b y) ≤
      S * C ^ 2 * J * E := by
    have hln := Finset.mem_range.mp hl
    have hh := kepLogSlopeNorm_pin_product (hk l x b) (hr (n - 1 - l) b y)
      hC hS (hcoeff l hln b hb) hln (fun s hs => hK s hs l x hxband b hb)
      (hfirst (n - 1 - l) b y hbe hy)
    convert hh using 1
    dsimp [E]
    ring
  have htc (l : ℕ) : Continuous (fun s =>
      (w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
          kepFixedBridgeRight p p' w s (n - 1 - l) w y -
        (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
          kepFixedBridgeRight p p' w s (n - 1 - l) 0 y) :=
    (((hk l x w).const_mul _).mul (hr (n - 1 - l) w y)).sub
      (((hk l x 0).const_mul _).mul (hr (n - 1 - l) 0 y))
  unfold kepBridgeFluxRight
  calc
    _ ≤ ∑ l ∈ Finset.range n, kepLogSlopeNorm (fun s =>
        (w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
          kepFixedBridgeRight p p' w s (n - 1 - l) w y -
        (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
          kepFixedBridgeRight p p' w s (n - 1 - l) 0 y) :=
      kepLogSlopeNorm_sum_le _ _ (fun l _ => htc l)
    _ ≤ ∑ _l ∈ Finset.range n, 2 * (S * C ^ 2 * J * E) := by
      apply Finset.sum_le_sum
      intro l hl
      have h0 := ht l hl 0 hb0 (Or.inl rfl)
      simp only [zero_sub] at h0
      have hh := kepLogSlopeNorm_sub_le
        (F := fun s => (w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
          kepFixedBridgeRight p p' w s (n - 1 - l) w y)
        (G := fun s => (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
          kepFixedBridgeRight p p' w s (n - 1 - l) 0 y)
        (((hk l x w).const_mul (w - x - (l + 1 : ℕ) * σ)).mul (hr (n - 1 - l) w y))
        (((hk l x 0).const_mul (-x - (l + 1 : ℕ) * σ)).mul (hr (n - 1 - l) 0 y))
      exact hh.trans (by linarith [ht l hl w hbw (Or.inr rfl)])
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [S, E]; ring

end

end PGM
