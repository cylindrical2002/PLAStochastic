import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Smooth real series from local summable bounds on every jet -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

section

variable {f : ℕ → ℝ → ℝ}
  (hf : ∀ n, ContDiff ℝ ∞ (f n))
  (hbound : ∀ r : ℕ, ∀ T : ℝ, 0 < T →
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n t, t ≤ T → ‖iteratedDeriv r (f n) t‖ ≤ u n)

include hbound

theorem summable_iteratedDeriv_of_local_bounds (r : ℕ) (t : ℝ) :
    Summable (fun n => iteratedDeriv r (f n) t) := by
  obtain ⟨u, hu, hb⟩ := hbound r (max t 1) (zero_lt_one.trans_le (le_max_right _ _))
  exact hu.of_norm_bounded (fun n => hb n t (le_max_left _ _))

include hf

theorem hasDerivAt_tsum_iteratedDeriv_of_local_bounds (r : ℕ) (t : ℝ) :
    HasDerivAt (fun x => ∑' n, iteratedDeriv r (f n) x)
      (∑' n, iteratedDeriv (r + 1) (f n) t) t := by
  let T := max t 1 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right t 1]
  have htT : t ∈ Iio T := by change t < T; dsimp [T]; linarith [le_max_left t 1]
  obtain ⟨u, hu, hb⟩ := hbound (r + 1) T hT
  apply hasDerivAt_tsum_of_isPreconnected hu isOpen_Iio isPreconnected_Iio
    (fun n x _ => ?_) (fun n x hx => hb n x hx.le) htT
    (summable_iteratedDeriv_of_local_bounds hbound r t) htT
  have hd := ((hf n).differentiable_iteratedDeriv r (by
    exact_mod_cast (ENat.natCast_lt_top r))).differentiableAt.hasDerivAt (x := x)
  simpa only [iteratedDeriv_succ] using hd

theorem iteratedDeriv_tsum_of_local_bounds (r : ℕ) :
    iteratedDeriv r (fun t => ∑' n, f n t) = fun t => ∑' n, iteratedDeriv r (f n) t := by
  induction r with
  | zero => simp only [iteratedDeriv_zero]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_tsum_iteratedDeriv_of_local_bounds hf hbound r t).deriv

theorem contDiff_tsum_of_local_iteratedDeriv_bounds :
    ContDiff ℝ ∞ (fun t => ∑' n, f n t) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro r _
  rw [iteratedDeriv_tsum_of_local_bounds hf hbound]
  exact fun t => (hasDerivAt_tsum_iteratedDeriv_of_local_bounds hf hbound r t).differentiableAt

end
