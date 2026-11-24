import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Actual derivatives of moving divided differences away from a root collision -/

noncomputable section
open Complex Filter Topology
namespace PGM

theorem dslope_sub_complex_of_ne (G H : ℂ → ℂ) {a p : ℂ} (hne : p ≠ a) :
    dslope (fun u => G u - H u) a p = dslope G a p - dslope H a p := by
  rw [dslope_of_ne _ hne, dslope_of_ne _ hne, dslope_of_ne _ hne]
  simp only [slope_def_field]
  ring

theorem hasDerivAt_moving_dslope_of_ne {G : ℂ → ℂ → ℂ} {a p : ℂ → ℂ}
    {z A P GA GP : ℂ} (ha : HasDerivAt a A z) (hp : HasDerivAt p P z)
    (hGa : HasDerivAt (fun u => G u (a u)) GA z)
    (hGp : HasDerivAt (fun u => G u (p u)) GP z) (hne : p z ≠ a z) :
    HasDerivAt (fun u => dslope (G u) (a u) (p u))
      ((GP - GA - dslope (G z) (a z) (p z) * (P - A)) / (p z - a z)) z := by
  have hg0 : p z - a z ≠ 0 := sub_ne_zero.mpr hne
  have hev := (hp.continuousAt.sub ha.continuousAt).eventually_ne hg0
  have heq : (fun u => (G u (p u) - G u (a u)) / (p u - a u)) =ᶠ[𝓝 z]
      (fun u => dslope (G u) (a u) (p u)) := by
    filter_upwards [hev] with u hu
    rw [dslope_of_ne _ (sub_ne_zero.mp hu), slope_def_field]
  have hd := ((hGp.sub hGa).div (hp.sub ha) hg0).congr_of_eventuallyEq heq.symm
  apply hd.congr_deriv
  simp only [Pi.sub_apply]
  rw [dslope_of_ne _ hne, slope_def_field]
  field_simp [hg0]

theorem norm_deriv_moving_dslope_mul_sq_le {G : ℂ → ℂ → ℂ} {a p : ℂ → ℂ}
    {z A P GA GP : ℂ} (ha : HasDerivAt a A z) (hp : HasDerivAt p P z)
    (hGa : HasDerivAt (fun u => G u (a u)) GA z)
    (hGp : HasDerivAt (fun u => G u (p u)) GP z) (hne : p z ≠ a z)
    {L K Da Dp E R : ℝ} (hL : 0 ≤ L)
    (hgap : ‖(p z - a z)⁻¹‖ * L ≤ K)
    (hA : ‖GA‖ * L ≤ Da) (hP : ‖GP‖ * L ≤ Dp)
    (hE : ‖dslope (G z) (a z) (p z)‖ ≤ E) (hR : ‖P - A‖ * L ≤ R) :
    ‖deriv (fun u => dslope (G u) (a u) (p u)) z‖ * L ^ 2 ≤
      (Dp + Da + E * R) * K := by
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hn : ‖GP - GA - dslope (G z) (a z) (p z) * (P - A)‖ * L ≤ Dp + Da + E * R := by
    calc
      _ ≤ (‖GP‖ + ‖GA‖ + ‖dslope (G z) (a z) (p z)‖ * ‖P - A‖) * L := by
        apply mul_le_mul_of_nonneg_right _ hL
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (by rw [norm_mul]))
      _ = ‖GP‖ * L + ‖GA‖ * L + ‖dslope (G z) (a z) (p z)‖ * (‖P - A‖ * L) := by ring
      _ ≤ _ := add_le_add (add_le_add hP hA)
        (mul_le_mul hE hR (mul_nonneg (norm_nonneg _) hL) hE0)
  rw [(hasDerivAt_moving_dslope_of_ne ha hp hGa hGp hne).deriv, div_eq_mul_inv, norm_mul]
  calc
    _ = (‖GP - GA - dslope (G z) (a z) (p z) * (P - A)‖ * L) *
        (‖(p z - a z)⁻¹‖ * L) := by ring
    _ ≤ _ := mul_le_mul hn hgap (mul_nonneg (norm_nonneg _) hL)
      ((mul_nonneg (norm_nonneg _) hL).trans hn)

end PGM
