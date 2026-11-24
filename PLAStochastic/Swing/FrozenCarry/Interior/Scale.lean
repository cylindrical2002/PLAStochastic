import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic

/-! Uniform deterministic scales of the intermediate Gaussian-duration window. -/
noncomputable section
open Filter
open scoped Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def frozenInteriorWindow (δ E : ℝ) (n : ℕ) : Prop :=
  E^(1+δ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ E^(2-δ)

theorem frozenInteriorWindow_ge_budget {δ E : ℝ} {n : ℕ}
    (hE : 1 ≤ E) (hδ : 0 ≤ δ) (hn : frozenInteriorWindow δ E n) : E ≤ (n : ℝ) := by
  calc
    E = E^(1 : ℝ) := (Real.rpow_one E).symm
    _ ≤ E^(1+δ) := Real.rpow_le_rpow_of_exponent_le hE (by linarith)
    _ ≤ _ := hn.1

theorem frozenInteriorWindow_le_square {δ E : ℝ} {n : ℕ}
    (hE : 1 ≤ E) (hδ : 0 ≤ δ) (hn : frozenInteriorWindow δ E n) : (n : ℝ) ≤ E^2 := by
  calc
    _ ≤ E^(2-δ) := hn.2
    _ ≤ E^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE (by linarith)
    _ = E^2 := Real.rpow_two E

theorem frozenInteriorWindow_drift_le {δ E c : ℝ} {n : ℕ}
    (hE : 1 ≤ E) (_hδ : 0 ≤ δ) (hc : 0 ≤ c) (hn : frozenInteriorWindow δ E n) :
    c*E/(n : ℝ) ≤ c*E^(-δ) := by
  have hEp : 0 < E := by linarith
  calc
    _ ≤ c*E/(E^(1+δ)) := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hEp _) hn.1
    _ = _ := by
      rw [Real.rpow_add hEp, Real.rpow_one, Real.rpow_neg hEp.le]
      field_simp

theorem frozenInteriorWindow_quadratic_ratio_ge {δ E : ℝ} {n : ℕ}
    (hE : 1 ≤ E) (hδ : 0 ≤ δ) (hn : frozenInteriorWindow δ E n) :
    E^δ ≤ E^2/(n : ℝ) := by
  have hEp : 0 < E := by linarith
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hEp (frozenInteriorWindow_ge_budget hE hδ hn)
  apply (le_div_iff₀ hnp).mpr
  have hp := mul_le_mul_of_nonneg_left hn.2 (Real.rpow_pos_of_pos hEp δ).le
  have he : E^δ*E^(2-δ) = E^2 := by
    rw [← Real.rpow_add hEp]
    convert Real.rpow_two E using 2
    ring
  rwa [he] at hp

theorem frozenInteriorWindow_exponent_ge {δ E c : ℝ} {n : ℕ}
    (hE : 2 ≤ E) (hδ : 0 ≤ δ) (hn : frozenInteriorWindow δ E n) :
    c^2/4*E^δ ≤ (c*E/(n : ℝ))^2*((n-1 : ℕ) : ℝ)/2 := by
  have hEp : 0 < E := by linarith
  have hEn := frozenInteriorWindow_ge_budget (by linarith : 1 ≤ E) hδ hn
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hEp hEn
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hsub : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by exact_mod_cast Nat.cast_sub (show 1 ≤ n by omega)
  rw [hsub]
  have hratio := frozenInteriorWindow_quadratic_ratio_ge (by linarith : 1 ≤ E) hδ hn
  calc
    _ ≤ c^2/4*(E^2/(n : ℝ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ _ := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hnp)).mp
      field_simp
      nlinarith [sq_nonneg (c*E)]

theorem frozen_polynomial_exp_rpow_tendsto_zero (k : ℕ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Tendsto (fun E : ℝ => E^k*Real.exp (-c*E^δ)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ)/δ) c hc).comp
    (tendsto_rpow_atTop hδ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with E hE
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hE, mul_div_cancel₀ _ hδ.ne', Real.rpow_natCast]

end SwingRepair
