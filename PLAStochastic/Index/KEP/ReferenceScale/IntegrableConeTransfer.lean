import PLAStochastic.ForMathlib.MeasureTheory.Integral.LogRadialSlice
import PLAStochastic.Index.KEP.ReferenceScale.IntegrableRadialTransfer
import PLAStochastic.ForMathlib.MeasureTheory.Integral.LogRadialIntegrability

/-!
# Physical second transfer on cones without an artificial test boundary

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

theorem kep_cone_integrable_physical_second_transfer {k : ℕ}
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
    {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ t, HasDerivAt phi (phi' t) t)
    (hddphi : ∀ t, HasDerivAt phi' (phi'' t) t)
    (h00 : Integrable (A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 * G0 x)))
    (h10 : Integrable (A.indicator (fun x => phi' (∑ i, x i) / (∑ i, x i) * G0 x)))
    (h20 : Integrable (A.indicator (fun x => phi'' (∑ i, x i) * G0 x)))
    (h01 : Integrable (A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 * G1 x)))
    (h11 : Integrable (A.indicator (fun x => phi' (∑ i, x i) / (∑ i, x i) * G1 x)))
    (h02 : Integrable (A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 * G2 x))) :
    (∫ x in A, phi'' (∑ i, x i) * G0 x) =
      ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 * (G2 x - 3 * G1 x + 2 * G0 x) := by
  have hrEq : A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 *
      (G2 x - 3 * G1 x + 2 * G0 x)) =
      fun x => A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 * G2 x) x -
        3 * A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 * G1 x) x +
        2 * A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 * G0 x) x := by
    funext x
    by_cases hx : x ∈ A
    · simp only [indicator_of_mem hx]; ring
    · simp only [indicator_of_notMem hx]; ring
  have hright : Integrable (A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 *
      (G2 x - 3 * G1 x + 2 * G0 x))) := by
    rw [hrEq]
    convert (h02.sub (h01.const_mul 3)).add (h00.const_mul 2) using 1 <;> rfl
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
    integral_eq_log_radial h20 hlzero, integral_eq_log_radial hright hrzero]
  apply integral_congr_ae
  filter_upwards [integrable_log_radial_sections h00, integrable_log_radial_sections h10,
    integrable_log_radial_sections h20, integrable_log_radial_sections h01,
    integrable_log_radial_sections h11, integrable_log_radial_sections h02] with u hu00 hu10 hu20 hu01 hu11 hu02
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
    change Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi (∑ i, z i) / (∑ i, z i) ^ 2 * G0 z) (Real.exp s • x)) at hu00
    change Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi' (∑ i, z i) / (∑ i, z i) * G0 z) (Real.exp s • x)) at hu10
    change Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi'' (∑ i, z i) * G0 z) (Real.exp s • x)) at hu20
    change Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi (∑ i, z i) / (∑ i, z i) ^ 2 * G1 z) (Real.exp s • x)) at hu01
    change Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi' (∑ i, z i) / (∑ i, z i) * G1 z) (Real.exp s • x)) at hu11
    change Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) *
      A.indicator (fun z => phi (∑ i, z i) / (∑ i, z i) ^ 2 * G2 z) (Real.exp s • x)) at hu02
    simp_rw [indicator_of_mem (hray _), hsum] at hu00 hu10 hu20 hu01 hu11 hu02
    have hh : (∫ s, phi'' (Real.exp s * ∑ i, x i) *
        (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G0 (Real.exp s • x))) =
        ∫ s, phi (Real.exp s * ∑ i, x i) / (Real.exp s * ∑ i, x i) ^ 2 *
          ((Real.exp (((k + 1 : ℕ) : ℝ) * s) * G2 (Real.exp s • x)) -
            3 * (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G1 (Real.exp s • x)) +
            2 * (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G0 (Real.exp s • x))) := by
      apply kep_integrable_radial_physical_second_transfer hdphi hddphi (hpos x hxA) (hd0 x) (hd1 x)
      · convert hu00 using 1; funext s; ring
      · convert hu10 using 1; funext s; ring
      · convert hu20 using 1; funext s; ring
      · convert hu01 using 1; funext s; ring
      · convert hu11 using 1; funext s; ring
      · convert hu02 using 1; funext s; ring
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
