import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Compact-test weak transfers in the logarithmic radial variable

Only the test has compact support. The radial density may have unrestricted
tails. Continuity and the true first two derivatives discharge integrability
and both boundary terms, without a density derivative envelope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory

theorem kep_compact_first_weak_transfer {H H' F F' : ℝ → ℝ}
    (hH : HasCompactSupport H) (hdH : ∀ x, HasDerivAt H (H' x) x)
    (hcH' : Continuous H') (hdF : ∀ x, HasDerivAt F (F' x) x)
    (hcF' : Continuous F') :
    (∫ x, H' x * F x) = -(∫ x, H x * F' x) := by
  have hcH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hdH x).continuousAt
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hdF x).continuousAt
  have he : H' = deriv H := funext fun x => (hdH x).deriv.symm
  have hsH' : HasCompactSupport H' := by rw [he]; exact hH.deriv
  have h0 : Integrable (F * H) :=
    (hcF.mul hcH).integrable_of_hasCompactSupport hH.mul_left
  have h1 : Integrable (F * H') :=
    (hcF.mul hcH').integrable_of_hasCompactSupport hsH'.mul_left
  have h2 : Integrable (F' * H) :=
    (hcF'.mul hcH).integrable_of_hasCompactSupport hH.mul_left
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hdF x) (fun x _ => hdH x) h1 h2 h0
  simpa only [mul_comm] using hh

theorem kep_compact_second_weak_transfer {H H' H'' F F' F'' : ℝ → ℝ}
    (hH : HasCompactSupport H) (hdH : ∀ x, HasDerivAt H (H' x) x)
    (hddH : ∀ x, HasDerivAt H' (H'' x) x) (hcH'' : Continuous H'')
    (hdF : ∀ x, HasDerivAt F (F' x) x) (hddF : ∀ x, HasDerivAt F' (F'' x) x)
    (hcF'' : Continuous F'') :
    (∫ x, (H'' x + 3 * H' x + 2 * H x) * F x) =
      ∫ x, H x * (F'' x - 3 * F' x + 2 * F x) := by
  have hcH := continuous_iff_continuousAt.mpr fun x => (hdH x).continuousAt
  have hcH' := continuous_iff_continuousAt.mpr fun x => (hddH x).continuousAt
  have hcF := continuous_iff_continuousAt.mpr fun x => (hdF x).continuousAt
  have hcF' := continuous_iff_continuousAt.mpr fun x => (hddF x).continuousAt
  have he : H' = deriv H := funext fun x => (hdH x).deriv.symm
  have he' : H'' = deriv H' := funext fun x => (hddH x).deriv.symm
  have hsH' : HasCompactSupport H' := by rw [he]; exact hH.deriv
  have hsH'' : HasCompactSupport H'' := by rw [he']; exact hsH'.deriv
  have hfirst := kep_compact_first_weak_transfer hH hdH hcH' hdF hcF'
  have hsecond := kep_compact_first_weak_transfer hsH' hddH hcH'' hdF hcF'
  have hthird := kep_compact_first_weak_transfer hH hdH hcH' hddF hcF''
  have hsecond' : (∫ x, H'' x * F x) = ∫ x, H x * F'' x := by
    rw [hsecond, hthird, neg_neg]
  have hi0 : Integrable (fun x => H x * F x) :=
    (hcH.mul hcF).integrable_of_hasCompactSupport hH.mul_right
  have hi1 : Integrable (fun x => H' x * F x) :=
    (hcH'.mul hcF).integrable_of_hasCompactSupport hsH'.mul_right
  have hi2 : Integrable (fun x => H'' x * F x) :=
    (hcH''.mul hcF).integrable_of_hasCompactSupport hsH''.mul_right
  have hiF1 : Integrable (fun x => H x * F' x) :=
    (hcH.mul hcF').integrable_of_hasCompactSupport hH.mul_right
  have hiF2 : Integrable (fun x => H x * F'' x) :=
    (hcH.mul hcF'').integrable_of_hasCompactSupport hH.mul_right
  calc
    _ = (∫ x, H'' x * F x) + 3 * (∫ x, H' x * F x) + 2 * (∫ x, H x * F x) := by
      have hfun : (fun x => (H'' x + 3 * H' x + 2 * H x) * F x) =
          fun x => H'' x * F x + 3 * (H' x * F x) + 2 * (H x * F x) := by funext x; ring
      have hsum := integral_add (hi2.add (hi1.const_mul 3)) (hi0.const_mul 2)
      have hsum' := integral_add hi2 (hi1.const_mul 3)
      simp only [Pi.add_apply] at hsum hsum'
      rw [hfun, hsum, hsum', integral_const_mul, integral_const_mul]
    _ = (∫ x, H x * F'' x) - 3 * (∫ x, H x * F' x) + 2 * (∫ x, H x * F x) := by
      rw [hsecond', hfirst]
      ring
    _ = _ := by
      have hfun : (fun x => H x * (F'' x - 3 * F' x + 2 * F x)) =
          fun x => H x * F'' x - 3 * (H x * F' x) + 2 * (H x * F x) := by funext x; ring
      have hsum := integral_add (hiF2.sub (hiF1.const_mul 3)) (hi0.const_mul 2)
      have hsub := integral_sub hiF2 (hiF1.const_mul 3)
      simp only [Pi.sub_apply] at hsum
      rw [hfun, hsum, hsub, integral_const_mul, integral_const_mul]

end

end PGM
