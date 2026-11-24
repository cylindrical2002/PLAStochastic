import PLAStochastic.ForMathlib.MeasureTheory.Integral.LogRadialSlice
import PLAStochastic.Index.KEP.ReferenceScale.RadialPhysicalTransfer

/-!
# The multivariate physical second transfer on measurable dilation cones

The event indicator is constant on every positive ray. The derivatives act on
the full radial Jacobian and density, with the coefficients `1, -3, 2` kept
exactly. No angular smoothness is assumed and no selection-boundary derivative
is discarded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set Finset

theorem kep_cone_physical_second_transfer {k : ℕ}
    {A : Set (Fin (k + 1) → ℝ)} (hA : MeasurableSet A)
    (hcone : ∀ x (c : ℝ), 0 < c → (c • x ∈ A ↔ x ∈ A))
    (hpos : ∀ x ∈ A, 0 < ∑ i, x i)
    {G0 G1 G2 : (Fin (k + 1) → ℝ) → ℝ}
    (hzero : ∀ x, x (Fin.last k) ≤ 0 → G0 x = 0 ∧ G1 x = 0 ∧ G2 x = 0)
    (hd0 : ∀ x s, HasDerivAt
      (fun t => Real.exp (((k + 1 : ℕ) : ℝ) * t) * G0 (Real.exp t • x))
      (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G1 (Real.exp s • x)) s)
    (hd1 : ∀ x s, HasDerivAt
      (fun t => Real.exp (((k + 1 : ℕ) : ℝ) * t) * G1 (Real.exp t • x))
      (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G2 (Real.exp s • x)) s)
    (hc2 : ∀ x, Continuous (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) * G2 (Real.exp s • x)))
    {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ t, HasDerivAt phi (phi' t) t)
    (hddphi : ∀ t, HasDerivAt phi' (phi'' t) t) (hcphi'' : Continuous phi'')
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support phi ⊆ Icc a b)
    (hleft : Integrable (A.indicator (fun x => phi'' (∑ i, x i) * G0 x)))
    (hright : Integrable (A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 *
      (G2 x - 3 * G1 x + 2 * G0 x)))) :
    (∫ x in A, phi'' (∑ i, x i) * G0 x) =
      ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 * (G2 x - 3 * G1 x + 2 * G0 x) := by
  have hlzero (x : Fin (k + 1) → ℝ) (hx : x (Fin.last k) ≤ 0) :
      A.indicator (fun x => phi'' (∑ i, x i) * G0 x) x = 0 := by
    by_cases hxA : x ∈ A
    · rw [indicator_of_mem hxA, (hzero x hx).1, mul_zero]
    · exact indicator_of_notMem hxA _
  have hrzero (x : Fin (k + 1) → ℝ) (hx : x (Fin.last k) ≤ 0) :
      A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 *
        (G2 x - 3 * G1 x + 2 * G0 x)) x = 0 := by
    by_cases hxA : x ∈ A
    · rw [indicator_of_mem hxA, (hzero x hx).1, (hzero x hx).2.1, (hzero x hx).2.2]
      ring
    · exact indicator_of_notMem hxA _
  rw [← integral_indicator hA, ← integral_indicator hA,
    integral_eq_log_radial hleft hlzero, integral_eq_log_radial hright hrzero]
  apply integral_congr_ae
  refine ae_of_all _ fun u => ?_
  let x : Fin (k + 1) → ℝ := Fin.snoc u 1
  have hsum (s : ℝ) : (∑ i, (Real.exp s • x) i) = Real.exp s * (∑ i, x i) := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  change (∫ s, Real.exp (((k + 1 : ℕ) : ℝ) * s) *
    A.indicator (fun z => phi'' (∑ i, z i) * G0 z) (Real.exp s • x)) =
    ∫ s, Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi (∑ i, z i) / (∑ i, z i) ^ 2 *
        (G2 z - 3 * G1 z + 2 * G0 z)) (Real.exp s • x)
  by_cases hxA : x ∈ A
  · have hray (s : ℝ) : Real.exp s • x ∈ A := (hcone x (Real.exp s) (Real.exp_pos s)).mpr hxA
    simp_rw [indicator_of_mem (hray _), hsum]
    have hh := kep_radial_physical_second_transfer hdphi hddphi hcphi'' ha (hpos x hxA)
      hsupp (hd0 x) (hd1 x) (hc2 x)
    convert hh using 1
    · apply integral_congr_ae
      exact ae_of_all _ fun s => by ring
    · apply integral_congr_ae
      exact ae_of_all _ fun s => by ring
  · have hray (s : ℝ) : Real.exp s • x ∉ A := by
      intro hs
      exact hxA ((hcone x (Real.exp s) (Real.exp_pos s)).mp hs)
    simp_rw [indicator_of_notMem (hray _)]

end

end PGM
