import PLAStochastic.Index.KEP.ReferenceScale.RadialWeakTransfer
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Physical second tests on a logarithmic ray

For positive ray sum sigma the exact transfer is
`phi''(exp(s) sigma) F(s) = phi(exp(s) sigma) (F''-3F'+2F)/(exp(s) sigma)^2`
after integration. The test is supported away from zero. Its logarithmic
transform has compact support, so all boundary and integrability inputs are
proved by the compact-test weak transfer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_radial_physical_second_transfer {phi phi' phi'' F F' F'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x)
    (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x) (hcphi'' : Continuous phi'')
    {a b sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hsupp : Function.support phi ⊆ Icc a b)
    (hdF : ∀ x, HasDerivAt F (F' x) x) (hddF : ∀ x, HasDerivAt F' (F'' x) x)
    (hcF'' : Continuous F'') :
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
  have hcphi := continuous_iff_continuousAt.mpr fun x => (hdphi x).continuousAt
  have hcphi' := continuous_iff_continuousAt.mpr fun x => (hddphi x).continuousAt
  have hcH'' : Continuous H'' := by dsimp [H'', e, z]; fun_prop
  have hHsupport : Function.support H ⊆ Icc (Real.log (a / sigma)) (Real.log (b / sigma)) := by
    intro s hs
    have hp : phi (z s) ≠ 0 := by
      intro h
      apply hs
      dsimp [H]
      rw [h, mul_zero, zero_div]
    have hb := hsupp hp
    have hlo : a / sigma ≤ Real.exp s := by
      rw [div_le_iff₀ hsigma]
      exact hb.1
    have hhi : Real.exp s ≤ b / sigma := by
      rw [le_div_iff₀ hsigma]
      exact hb.2
    exact ⟨by simpa only [Real.log_exp] using Real.log_le_log (div_pos ha hsigma) hlo,
      by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos s) hhi⟩
  have hsH : HasCompactSupport H :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hHsupport isClosed_Icc)
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
  have hh := kep_compact_second_weak_transfer hsH hH hH' hcH'' hdF hddF hcF''
  simp_rw [hsum, hHeq] at hh
  exact hh

end

end PGM
