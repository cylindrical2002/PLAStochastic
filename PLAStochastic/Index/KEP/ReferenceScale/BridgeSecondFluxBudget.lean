import PLAStochastic.Index.KEP.ReferenceScale.BridgeFluxAverage

/-!
# The slope derivative of every internal transport pin

After the Ward identity each differentiated pin is estimated with one first
input norm. The remaining bridges contribute their pointwise killed bounds.
All short bridge lengths and both outward endpoint signs are included.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepBridgeFluxSlope_boundary_average {p p' q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hq : Continuous (Function.uncurry q))
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
    kepLogSlopeNorm (fun s => kepBridgeFluxSlope p q w σ s n x y) ≤
      32 * (n : ℝ) * (w + (n + 1 : ℕ)) ^ 3 * C ^ 3 * J *
        Real.exp (-r * (n + 1 : ℕ)) := by
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> constructor <;> linarith
  have hyband : y ∈ Icc 0 w := by
    rcases hy with rfl | rfl <;> constructor <;> linarith
  have hb0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hbw : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
  let S := w + (n + 1 : ℕ)
  let E := Real.exp (-r * (n + 1 : ℕ))
  let A := 8 * C ^ 2 * S ^ 2 * J
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hk (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridge p w s m u v) :=
    (continuous_kepFixedBridge hp w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hdK (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridgeSlope p q w s m u v) :=
    (continuous_kepFixedBridgeSlope hp hq w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hcoeff (l : ℕ) (hl : l < n) (b : ℝ) (hb : b ∈ Icc 0 w) :
      |b - x - (l + 1 : ℕ) * σ| ≤ S := by
    have hh := kep_pin_coefficient_bound hσ hxband hb l
    have hln : (l : ℝ) ≤ n := by exact_mod_cast hl.le
    dsimp [S]
    push_cast at hh ⊢
    linarith
  have hDn (m : ℕ) (hm : m ≤ n) (u v : ℝ)
      (hu : u = 0 ∨ u = w) (hv : v = 0 ∨ v = w) :
      kepLogSlopeNorm (fun s => kepFixedBridgeSlope p q w s m u v) ≤
        A * Real.exp (-r * (m + 1 : ℕ)) := by
    apply (kepFixedBridgeSlope_boundary_average hp hp' hd hσ hward hw hC hJ
      hK hfirst m hu hv).trans
    have hmS : w + (m + 1 : ℕ) ≤ S := by
      have hm' : (m : ℝ) ≤ n := by exact_mod_cast hm
      dsimp [S]
      push_cast
      linarith
    dsimp [A]
    gcongr
  have hterm (l : ℕ) (hl : l ∈ Finset.range n) (b : ℝ) (hb : b ∈ Icc 0 w)
      (hbe : b = 0 ∨ b = w) :
      kepLogSlopeNorm (fun s => (b - x - (l + 1 : ℕ) * σ) *
        (kepFixedBridgeSlope p q w s l x b * kepFixedBridge p w s (n - 1 - l) b y +
          kepFixedBridge p w s l x b * kepFixedBridgeSlope p q w s (n - 1 - l) b y)) ≤
        2 * (S * C * A * E) := by
    have hln := Finset.mem_range.mp hl
    have hsn : n - 1 - l < n := by omega
    have hmirror : n - 1 - (n - 1 - l) = l := by omega
    let c := b - x - (l + 1 : ℕ) * σ
    have hL : kepLogSlopeNorm (fun s => c * kepFixedBridgeSlope p q w s l x b *
        kepFixedBridge p w s (n - 1 - l) b y) ≤ S * C * A * E := by
      have hh := kepLogSlopeNorm_pin_product (hk (n - 1 - l) b y) (hdK l x b)
        hC0 hS (hcoeff l hln b hb) hsn
        (fun s hs => hK s hs _ b hb y hyband)
        (by rw [hmirror]; exact hDn l hln.le x b hx hbe)
      have he : (fun s => c * kepFixedBridgeSlope p q w s l x b *
          kepFixedBridge p w s (n - 1 - l) b y) =
        (fun s => c * kepFixedBridge p w s (n - 1 - l) b y *
          kepFixedBridgeSlope p q w s l x b) := by funext s; ring
      rw [he]
      exact hh
    have hR : kepLogSlopeNorm (fun s => c * kepFixedBridge p w s l x b *
        kepFixedBridgeSlope p q w s (n - 1 - l) b y) ≤ S * C * A * E :=
      kepLogSlopeNorm_pin_product (hk l x b) (hdK (n - 1 - l) b y) hC0 hS
        (hcoeff l hln b hb) hln (fun s hs => hK s hs l x hxband b hb)
        (hDn _ hsn.le b y hbe hy)
    have he : (fun s => c * (kepFixedBridgeSlope p q w s l x b *
          kepFixedBridge p w s (n - 1 - l) b y + kepFixedBridge p w s l x b *
          kepFixedBridgeSlope p q w s (n - 1 - l) b y)) =
        (fun s => c * kepFixedBridgeSlope p q w s l x b *
          kepFixedBridge p w s (n - 1 - l) b y + c * kepFixedBridge p w s l x b *
          kepFixedBridgeSlope p q w s (n - 1 - l) b y) := by funext s; ring
    change kepLogSlopeNorm (fun s => c * _) ≤ _
    rw [he]
    exact (kepLogSlopeNorm_add_le
      (F := fun s => c * kepFixedBridgeSlope p q w s l x b *
        kepFixedBridge p w s (n - 1 - l) b y)
      (G := fun s => c * kepFixedBridge p w s l x b *
        kepFixedBridgeSlope p q w s (n - 1 - l) b y)
      (((hdK l x b).const_mul c).mul (hk (n - 1 - l) b y))
      (((hk l x b).const_mul c).mul (hdK (n - 1 - l) b y))).trans (by linarith)
  let T (l : ℕ) (b : ℝ) (s : ℝ) := (b - x - (l + 1 : ℕ) * σ) *
    (kepFixedBridgeSlope p q w s l x b * kepFixedBridge p w s (n - 1 - l) b y +
      kepFixedBridge p w s l x b * kepFixedBridgeSlope p q w s (n - 1 - l) b y)
  have hTc (l : ℕ) (b : ℝ) : Continuous (T l b) :=
    ((((hdK l x b).mul (hk (n - 1 - l) b y)).add
      ((hk l x b).mul (hdK (n - 1 - l) b y))).const_mul _)
  have he : (fun s => kepBridgeFluxSlope p q w σ s n x y) =
      fun s => ∑ l ∈ Finset.range n, (T l w s - T l 0 s) := by
    funext s
    simp only [kepBridgeFluxSlope, T, zero_sub]
  rw [he]
  calc
    _ ≤ ∑ l ∈ Finset.range n, kepLogSlopeNorm (fun s => T l w s - T l 0 s) :=
      kepLogSlopeNorm_sum_le _ _ (fun l _ => (hTc l w).sub (hTc l 0))
    _ ≤ ∑ _l ∈ Finset.range n, 4 * (S * C * A * E) := by
      apply Finset.sum_le_sum
      intro l hl
      have hW : kepLogSlopeNorm (T l w) ≤ 2 * (S * C * A * E) :=
        hterm l hl w hbw (Or.inr rfl)
      have h0 : kepLogSlopeNorm (T l 0) ≤ 2 * (S * C * A * E) :=
        hterm l hl 0 hb0 (Or.inl rfl)
      exact (kepLogSlopeNorm_sub_le (hTc l w) (hTc l 0)).trans
        (by linarith)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [S, E, A]
      ring

end

end PGM
