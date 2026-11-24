import PLAStochastic.Index.KEP.ReferenceScale.RadialPhysicalTransfer

/-!
# Radial weak transfer with all integrability paid explicitly

The test may meet the physical origin or have a noncompact logarithmic tail.
Integrability of the six genuine product terms supplies both integration by
parts boundaries. This is needed by shifted convolution tests of actual
prefix laws; no boundary assumption is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_integrable_first_weak_transfer {H H' F F' : ℝ → ℝ}
    (hdH : ∀ x, HasDerivAt H (H' x) x) (hdF : ∀ x, HasDerivAt F (F' x) x)
    (hi0 : Integrable (fun x => H x * F x))
    (hi1 : Integrable (fun x => H' x * F x))
    (hi2 : Integrable (fun x => H x * F' x)) :
    (∫ x, H' x * F x) = -(∫ x, H x * F' x) := by
  have h0 : Integrable (F * H) := by
    convert hi0 using 1
    funext x
    exact mul_comm _ _
  have h1 : Integrable (F * H') := by
    convert hi1 using 1
    funext x
    exact mul_comm _ _
  have h2 : Integrable (F' * H) := by
    convert hi2 using 1
    funext x
    exact mul_comm _ _
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hdF x) (fun x _ => hdH x) h1 h2 h0
  simpa only [mul_comm] using hh

theorem kep_integrable_second_weak_transfer {H H' H'' F F' F'' : ℝ → ℝ}
    (hdH : ∀ x, HasDerivAt H (H' x) x) (hddH : ∀ x, HasDerivAt H' (H'' x) x)
    (hdF : ∀ x, HasDerivAt F (F' x) x) (hddF : ∀ x, HasDerivAt F' (F'' x) x)
    (hi0 : Integrable (fun x => H x * F x))
    (hi1 : Integrable (fun x => H' x * F x))
    (hi2 : Integrable (fun x => H'' x * F x))
    (hiF1 : Integrable (fun x => H x * F' x))
    (hiF2 : Integrable (fun x => H x * F'' x))
    (hi11 : Integrable (fun x => H' x * F' x)) :
    (∫ x, (H'' x + 3 * H' x + 2 * H x) * F x) =
      ∫ x, H x * (F'' x - 3 * F' x + 2 * F x) := by
  have hfirst := kep_integrable_first_weak_transfer hdH hdF hi0 hi1 hiF1
  have hsecond := kep_integrable_first_weak_transfer hddH hdF hi1 hi2 hi11
  have hthird := kep_integrable_first_weak_transfer hdH hddF hiF1 hi11 hiF2
  have hsecond' : (∫ x, H'' x * F x) = ∫ x, H x * F'' x := by
    rw [hsecond, hthird, neg_neg]
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


theorem kep_integrable_radial_physical_second_transfer {phi phi' phi'' F F' F'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x)
    (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x) {sigma : ℝ} (hsigma : 0 < sigma)
    (hdF : ∀ x, HasDerivAt F (F' x) x) (hddF : ∀ x, HasDerivAt F' (F'' x) x)
    (h00 : Integrable (fun s => phi (Real.exp s * sigma) / (Real.exp s * sigma) ^ 2 * F s))
    (h10 : Integrable (fun s => phi' (Real.exp s * sigma) / (Real.exp s * sigma) * F s))
    (h20 : Integrable (fun s => phi'' (Real.exp s * sigma) * F s))
    (h01 : Integrable (fun s => phi (Real.exp s * sigma) / (Real.exp s * sigma) ^ 2 * F' s))
    (h11 : Integrable (fun s => phi' (Real.exp s * sigma) / (Real.exp s * sigma) * F' s))
    (h02 : Integrable (fun s => phi (Real.exp s * sigma) / (Real.exp s * sigma) ^ 2 * F'' s)) :
    (∫ s, phi'' (Real.exp s * sigma) * F s) =
      ∫ s, phi (Real.exp s * sigma) / (Real.exp s * sigma) ^ 2 *
        (F'' s - 3 * F' s + 2 * F s) := by
  let z := fun s : ℝ => Real.exp s * sigma
  let e := fun s : ℝ => Real.exp (-2 * s)
  let H := fun s : ℝ => e s * phi (z s) / sigma ^ 2
  let H' := fun s : ℝ => e s * (z s * phi' (z s) - 2 * phi (z s)) / sigma ^ 2
  let H'' := fun s : ℝ => e s *
    ((z s) ^ 2 * phi'' (z s) - 3 * z s * phi' (z s) + 4 * phi (z s)) / sigma ^ 2
  have hz (s : ℝ) : HasDerivAt z (z s) s := (Real.hasDerivAt_exp s).mul_const sigma
  have he (s : ℝ) : HasDerivAt e (-2 * e s) s := by
    convert (Real.hasDerivAt_exp (-2 * s)).comp s ((hasDerivAt_id s).const_mul (-2)) using 1 <;> first
    | rfl
    | ring
  have hH (s : ℝ) : HasDerivAt H (H' s) s := by
    convert ((he s).mul ((hdphi (z s)).comp s (hz s))).div_const (sigma ^ 2) using 1 <;> first
    | rfl
    | (dsimp [H']; ring)
  have hH' (s : ℝ) : HasDerivAt H' (H'' s) s := by
    have hh := ((hz s).mul ((hddphi (z s)).comp s (hz s))).sub
      (((hdphi (z s)).comp s (hz s)).const_mul 2)
    convert ((he s).mul hh).div_const (sigma ^ 2) using 1 <;> first
    | rfl
    | (dsimp [H'']; ring)
  have hfac (s : ℝ) : e s / sigma ^ 2 = 1 / (z s) ^ 2 := by
    have hexp : e s * (Real.exp s) ^ 2 = 1 := by
      dsimp [e]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    apply (div_eq_div_iff (pow_ne_zero 2 hsigma.ne') (pow_ne_zero 2 (by dsimp [z]; positivity))).mpr
    calc
      e s * (z s) ^ 2 = (e s * (Real.exp s) ^ 2) * sigma ^ 2 := by dsimp [z]; ring
      _ = 1 * sigma ^ 2 := by rw [hexp]
  have hsum (s : ℝ) : H'' s + 3 * H' s + 2 * H s = phi'' (z s) := by
    calc
      _ = (e s / sigma ^ 2) * (z s) ^ 2 * phi'' (z s) := by dsimp [H, H', H'']; ring
      _ = _ := by
        rw [hfac]
        have hz0 : z s ≠ 0 := by dsimp [z]; positivity
        field_simp
  have hHeq (s : ℝ) : H s = phi (z s) / (z s) ^ 2 := by
    calc
      H s = (e s / sigma ^ 2) * phi (z s) := by dsimp [H]; ring
      _ = _ := by rw [hfac]; ring
  have hH'eq (s : ℝ) : H' s = phi' (z s) / z s - 2 * (phi (z s) / (z s) ^ 2) := by
    calc
      _ = (e s / sigma ^ 2) * (z s * phi' (z s) - 2 * phi (z s)) := by dsimp [H']; ring
      _ = _ := by rw [hfac]; field_simp [show z s ≠ 0 by dsimp [z]; positivity]
  have hH''eq (s : ℝ) : H'' s = phi'' (z s) - 3 * (phi' (z s) / z s) +
      4 * (phi (z s) / (z s) ^ 2) := by
    calc
      _ = (e s / sigma ^ 2) * ((z s) ^ 2 * phi'' (z s) - 3 * z s * phi' (z s) + 4 * phi (z s)) := by dsimp [H'']; ring
      _ = _ := by rw [hfac]; field_simp [show z s ≠ 0 by dsimp [z]; positivity]
  have hi0 : Integrable (fun s => H s * F s) := by simp_rw [hHeq]; exact h00
  have hi1 : Integrable (fun s => H' s * F s) := by
    simp_rw [hH'eq, sub_mul, mul_assoc]
    convert h10.sub (h00.const_mul 2) using 1
    rfl
  have hi2 : Integrable (fun s => H'' s * F s) := by
    simp_rw [hH''eq, add_mul, sub_mul, mul_assoc]
    convert (h20.sub (h10.const_mul 3)).add (h00.const_mul 4) using 1 <;> rfl
  have hiF1 : Integrable (fun s => H s * F' s) := by simp_rw [hHeq]; exact h01
  have hiF2 : Integrable (fun s => H s * F'' s) := by simp_rw [hHeq]; exact h02
  have hi11 : Integrable (fun s => H' s * F' s) := by
    simp_rw [hH'eq, sub_mul, mul_assoc]
    convert h11.sub (h01.const_mul 2) using 1
    rfl
  have hh := kep_integrable_second_weak_transfer hH hH' hdF hddF hi0 hi1 hi2 hiF1 hiF2 hi11
  simp_rw [hsum, hHeq] at hh
  exact hh

end

end PGM
