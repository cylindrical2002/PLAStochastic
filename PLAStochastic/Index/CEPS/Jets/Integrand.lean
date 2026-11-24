import PLAStochastic.Index.CEPS.Jets.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# X8: the jet integrands

`D_{k+1}(w) = -P_k(w/(1-w))` (`cepsLogDJet k w`) with `P_k = X Q_k`:

* `differentiableAt_cepsLogDJet`: holomorphic off `w = 1`;
* `norm_cepsLogDJet_le`: `‖D_{k+1}(w)‖ ≤ C ‖w‖` on `{‖w‖ ≤ K, ‖1 - w‖ ≥ δ}`;
* `hasDerivAt_cepsLogDJet_exp`: `∂_x D_{k+1}(e^x w) = D_{k+2}(e^x w)`;
* `hasDerivAt_log_cepsJetF_exp`: `∂_x log F̃(s, e^x w) = D_1(e^x w)` when `F̃` is in the slit plane;
* conjugation symmetry of `D_k`, `F̃` and of the jet integrands.
-/

noncomputable section

open Complex Polynomial

namespace PGM

/-- `P_k` over `ℂ`. -/
def cepsJetPolyC (k : ℕ) : ℂ[X] := (cepsJetPoly k).map (Int.castRingHom ℂ)

theorem aeval_cepsJetPoly (k : ℕ) (z : ℂ) : aeval z (cepsJetPoly k) = (cepsJetPolyC k).eval z := by
  rw [aeval_def, cepsJetPolyC, eval_map]
  rfl

theorem cepsJetPolyC_succ (k : ℕ) :
    cepsJetPolyC (k + 1) = (X + X ^ 2) * derivative (cepsJetPolyC k) := by
  simp [cepsJetPolyC, cepsJetPoly, Polynomial.map_mul, derivative_map]

theorem cepsJetPolyC_eq_X_mul (k : ℕ) : ∃ Q : ℂ[X], cepsJetPolyC k = X * Q := by
  cases k with
  | zero => exact ⟨1, by simp [cepsJetPolyC, cepsJetPoly]⟩
  | succ k => exact ⟨(1 + X) * derivative (cepsJetPolyC k), by rw [cepsJetPolyC_succ]; ring⟩

theorem cepsLogDJet_eq (k : ℕ) (w : ℂ) :
    cepsLogDJet k w = -(cepsJetPolyC k).eval (w / (1 - w)) := by
  rw [cepsLogDJet, aeval_cepsJetPoly]

theorem differentiableAt_cepsLogDJet (k : ℕ) {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ (cepsLogDJet k) w := by
  have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have e : cepsLogDJet k = fun w => -(cepsJetPolyC k).eval (w / (1 - w)) := by
    funext w; exact cepsLogDJet_eq k w
  rw [e]
  exact ((cepsJetPolyC k).differentiable.differentiableAt.comp w
    (differentiableAt_id.div (differentiableAt_const _ |>.sub differentiableAt_id) h1)).neg

/-- `‖D_{k+1}(w)‖ ≤ C ‖w‖` where `‖w‖ ≤ K` and `‖1 - w‖ ≥ δ`. -/
theorem norm_cepsLogDJet_le (k : ℕ) {K δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ K → δ ≤ ‖1 - w‖ → ‖cepsLogDJet k w‖ ≤ C * ‖w‖ := by
  obtain ⟨Q, hQ⟩ := cepsJetPolyC_eq_X_mul k
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (|K| / δ)).exists_bound_of_continuousOn
    Q.continuous.continuousOn
  refine ⟨|B| / δ, by positivity, fun w hw h1 => ?_⟩
  have h10 : 0 < ‖1 - w‖ := lt_of_lt_of_le hδ h1
  have hu : ‖w / (1 - w)‖ ≤ ‖w‖ / δ := by
    rw [norm_div]; exact div_le_div_of_nonneg_left (norm_nonneg _) hδ h1
  have hu2 : w / (1 - w) ∈ Metric.closedBall (0 : ℂ) (|K| / δ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hu.trans (div_le_div_of_nonneg_right (hw.trans (le_abs_self K)) hδ.le)
  rw [cepsLogDJet_eq, norm_neg, hQ, eval_mul, eval_X, norm_mul]
  calc ‖w / (1 - w)‖ * ‖Q.eval (w / (1 - w))‖ ≤ ‖w‖ / δ * |B| :=
        mul_le_mul hu ((hB _ hu2).trans (le_abs_self B)) (norm_nonneg _) (by positivity)
    _ = |B| / δ * ‖w‖ := by ring

/-- `∂_x D_{k+1}(e^x w) = D_{k+2}(e^x w)`. -/
theorem hasDerivAt_cepsLogDJet_exp (k : ℕ) (w x : ℂ) (hw : cexp x * w ≠ 1) :
    HasDerivAt (fun x => cepsLogDJet k (cexp x * w)) (cepsLogDJet (k + 1) (cexp x * w)) x := by
  set W := cexp x * w with hW
  have h1 : (1 : ℂ) - W ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hWd : HasDerivAt (fun x => cexp x * w) W x := (Complex.hasDerivAt_exp x).mul_const w
  have hud : HasDerivAt (fun x => cexp x * w / (1 - cexp x * w))
      ((W * (1 - W) - W * (0 - W)) / (1 - W) ^ 2) x :=
    hWd.div ((hasDerivAt_const x (1 : ℂ)).sub hWd) h1
  have hP := ((cepsJetPolyC k).hasDerivAt (W / (1 - W))).comp x hud
  have e : (fun x => cepsLogDJet k (cexp x * w)) =
      fun x => -(cepsJetPolyC k).eval (cexp x * w / (1 - cexp x * w)) := by
    funext x; exact cepsLogDJet_eq k _
  rw [e]
  refine hP.neg.congr_deriv ?_
  rw [cepsLogDJet_eq, cepsJetPolyC_succ, eval_mul, eval_add, eval_X, eval_pow, eval_X]
  field_simp
  ring

/-- `∂_x log F̃(s, e^x w) = D_1(e^x w)` when `F̃` lies in the slit plane. -/
theorem hasDerivAt_log_cepsJetF_exp (s w x : ℂ) (hF : cepsJetF s (cexp x * w) ∈ slitPlane) :
    HasDerivAt (fun x => Complex.log (cepsJetF s (cexp x * w)))
      (cepsLogDJet 0 (cexp x * w)) x := by
  set W := cexp x * w with hW
  have hF0 : cepsJetF s W ≠ 0 := slitPlane_ne_zero hF
  have hs0 : s ≠ 0 := by
    intro h; apply hF0; rw [cepsJetF, h]; simp
  have h1 : (1 : ℂ) - W ≠ 0 := by
    intro h; apply hF0; rw [cepsJetF, h]; simp
  have hR : (s ^ 2 - 1) / s ^ 2 ≠ 0 := by
    intro h; apply hF0; rw [cepsJetF, mul_div_assoc, h, mul_zero]
  have hWd : HasDerivAt (fun x => cexp x * w) W x := (Complex.hasDerivAt_exp x).mul_const w
  have h21 : s ^ 2 - 1 ≠ 0 := fun h => hR (by rw [h, zero_div])
  have e2 : (fun x => cepsJetF s (cexp x * w)) = fun y => (1 - cexp y * w) * ((s ^ 2 - 1) / s ^ 2) := by
    funext y; rw [cepsJetF, mul_div_assoc]
  have hFd : HasDerivAt (fun x => cepsJetF s (cexp x * w)) (-W * ((s ^ 2 - 1) / s ^ 2)) x := by
    rw [e2]
    exact (((hasDerivAt_const x (1 : ℂ)).sub hWd).mul_const ((s ^ 2 - 1) / s ^ 2)).congr_deriv
      (by ring)
  refine (hFd.clog hF).congr_deriv ?_
  rw [cepsLogDJet_eq, cepsJetPolyC, cepsJetPoly, Polynomial.map_X, eval_X, cepsJetF, ← hW]
  field_simp

/-! ### Conjugation symmetry -/

theorem cepsLogDJet_conj (k : ℕ) (w : ℂ) :
    cepsLogDJet k ((starRingEnd ℂ) w) = (starRingEnd ℂ) (cepsLogDJet k w) := by
  rw [cepsLogDJet, cepsLogDJet, map_neg, aeval_def, aeval_def, hom_eval₂]
  congr 2
  · exact RingHom.ext_int _ _
  · simp [map_div₀]

theorem cepsJetF_conj (s w : ℂ) :
    cepsJetF ((starRingEnd ℂ) s) ((starRingEnd ℂ) w) = (starRingEnd ℂ) (cepsJetF s w) := by
  simp [cepsJetF, map_div₀]

theorem cepsJetIntegrand_conj (j m n : ℕ) (s w : ℂ)
    (hF : j + n = 0 → cepsJetF s w ∈ slitPlane) :
    cepsJetIntegrand j m n ((starRingEnd ℂ) s) ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (cepsJetIntegrand j m n s w) := by
  unfold cepsJetIntegrand
  split_ifs with h
  · rw [cepsJetF_conj, Complex.log_conj _ (slitPlane_arg_ne_pi (hF h))]
    simp [map_div₀]
  · rw [cepsLogDJet_conj]
    simp [map_div₀]

end PGM
