import PLAStochastic.Index.KEP.ReferenceScale.BridgeFlux

/-!
# Finite pin sums for the actual bridge fluxes

The suffix has at least one step. The sum is over the `n` internal positions
of an `n + 1` step bridge, and keeps the outward signs at both endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem integral_kepFixedBridge_pin_pair {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w s : ℝ) (m k : ℕ)
    (b c y U V : ℝ) :
    (∫ z in Ioc 0 w,
      (U * kepFixedBridge p w s m b z - V * kepFixedBridge p w s k c z) * p s (y - z)) =
      U * kepFixedBridge p w s (m + 1) b y - V * kepFixedBridge p w s (k + 1) c y := by
  have hm : Continuous (kepFixedBridge p w s m b) :=
    (continuous_kepFixedBridge hp w m).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hk : Continuous (kepFixedBridge p w s k c) :=
    (continuous_kepFixedBridge hp w k).comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hpt : Continuous (fun z => p s (y - z)) :=
    hp.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  simp_rw [sub_mul, mul_assoc]
  rw [integral_sub, integral_const_mul, integral_const_mul]
  · rfl
  · exact ((hm.mul hpt).const_mul U).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact ((hk.mul hpt).const_mul V).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem kepBridgeTransportFlux_eq_sum {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w σ s : ℝ) (n : ℕ) (x y : ℝ) :
    kepBridgeTransportFlux p w σ s n x y =
      ∑ l ∈ Finset.range n,
        ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
          kepFixedBridge p w s (n - 1 - l) w y -
        (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
          kepFixedBridge p w s (n - 1 - l) 0 y) := by
  induction n generalizing y with
  | zero => simp [kepBridgeTransportFlux]
  | succ n ih =>
    have hpt : Continuous (fun z => p s (y - z)) :=
      hp.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have hfinite :
        (∫ z in Ioc 0 w, kepBridgeTransportFlux p w σ s n x z * p s (y - z)) =
        ∑ l ∈ Finset.range n,
          ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
            kepFixedBridge p w s (n - l) w y -
          (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
            kepFixedBridge p w s (n - l) 0 y) := by
      calc
        _ = ∫ z in Ioc 0 w, ∑ l ∈ Finset.range n,
            ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
                kepFixedBridge p w s (n - 1 - l) w z -
              (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
                kepFixedBridge p w s (n - 1 - l) 0 z) * p s (y - z) := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => by dsimp only; rw [ih z, Finset.sum_mul]
        _ = ∑ l ∈ Finset.range n, ∫ z in Ioc 0 w,
            ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
                kepFixedBridge p w s (n - 1 - l) w z -
              (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
                kepFixedBridge p w s (n - 1 - l) 0 z) * p s (y - z) := by
          apply integral_finsetSum
          intro l hl
          have hk (b : ℝ) : Continuous (kepFixedBridge p w s (n - 1 - l) b) :=
            (continuous_kepFixedBridge hp w (n - 1 - l)).comp
              (continuous_const.prodMk (continuous_const.prodMk continuous_id))
          exact (((((hk w).const_mul _).sub ((hk 0).const_mul _)).mul hpt).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l hl
          have hlen : n - 1 - l + 1 = n - l := by
            have := Finset.mem_range.mp hl
            omega
          rw [integral_kepFixedBridge_pin_pair hp, hlen]
    rw [kepBridgeTransportFlux, hfinite, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, kepFixedBridge, sub_zero]
    ring

end

end PGM
