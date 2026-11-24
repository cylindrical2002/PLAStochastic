import PLAStochastic.Index.KEP.ReferenceScale.RadialCutoff
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers

/-!
# Certificate invariance and support of the radial complement derivatives

All certificate bands are unchanged by a nonzero dilation of the keys. The
selected slope changes by the inverse dilation. On a long bridge with slope
strictly between three quarters and three halves, the rare cutoff and both
of its true radial derivatives vanish.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open Set Filter Topology

theorem certSlope_const_mul (eps : ℝ) (p : ℕ → ℝ) (i j : ℕ) (c : ℝ) :
    certSlope eps (fun t => c * p t) i j = certSlope eps p i j / c := by
  simp only [certSlope, ← mul_sub, div_eq_mul_inv, mul_inv_rev]
  ring

theorem certResid_const_mul (a : ℝ) (p : ℕ → ℝ) (t : ℕ) {c : ℝ} (hc : c ≠ 0) :
    certResid (a / c) (fun t => c * p t) t = certResid a p t := by
  unfold certResid
  field_simp

theorem certOK_const_mul (eps : ℝ) (p : ℕ → ℝ) (k i j : ℕ)
    {c : ℝ} (hc : c ≠ 0) :
    certOK eps (fun t => c * p t) k i j ↔ certOK eps p k i j := by
  unfold certOK certBand
  rw [certSlope_const_mul]
  simp only [certResid_const_mul _ _ _ hc]

theorem certSlope_gapKeys_const_mul (eps : ℝ) (g : ℕ → ℝ) (i j : ℕ) (c : ℝ) :
    certSlope eps (gapKeys (fun t => c * g t)) i j =
      certSlope eps (gapKeys g) i j / c := by
  have hg : gapKeys (fun t => c * g t) = fun t => c * gapKeys g t := by
    funext t
    exact gapKeys_const_mul g c t
  rw [hg, certSlope_const_mul]

theorem certOK_gapKeys_const_mul (eps : ℝ) (g : ℕ → ℝ) (k i j : ℕ)
    {c : ℝ} (hc : c ≠ 0) :
    certOK eps (gapKeys (fun t => c * g t)) k i j ↔
      certOK eps (gapKeys g) k i j := by
  have hg : gapKeys (fun t => c * g t) = fun t => c * gapKeys g t := by
    funext t
    exact gapKeys_const_mul g c t
  rw [hg]
  exact certOK_const_mul eps (gapKeys g) k i j hc

theorem kepCertificateLogCutoff_good_derivatives {s : ℝ}
    (hs : Real.exp s ∈ Ioo (3 / 4 : ℝ) (3 / 2)) :
    kepCertificateLogCutoff s = 1 ∧ deriv kepCertificateLogCutoff s = 0 ∧
      deriv (deriv kepCertificateLogCutoff) s = 0 := by
  have he : kepCertificateLogCutoff =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
    have hmem := Real.continuous_exp.continuousAt.eventually_mem
      (Ioo_mem_nhds hs.1 hs.2)
    filter_upwards [hmem] with t ht
    exact kepCertificateCutoff_eq_one ⟨ht.1.le, ht.2.le⟩
  refine ⟨he.eq_of_nhds, ?_, ?_⟩
  · simpa only [deriv_const] using he.deriv_eq
  · have hd : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => (0 : ℝ) := by
      funext t
      exact deriv_const t 1
    simpa only [hd, deriv_const] using he.deriv.deriv_eq

theorem kepRadialCoreWeight_good (M i j : ℕ) (hM : M ≤ j - i)
    {ell s : ℝ} (hs : Real.exp (ell - s) ∈ Ioo (3 / 4 : ℝ) (3 / 2)) :
    1 - kepRadialCoreWeight M i j ell s = 0 ∧
      kepRadialCoreWeightFirst M i j ell s = 0 ∧
      kepRadialCoreWeightSecond M i j ell s = 0 := by
  obtain ⟨h0, h1, h2⟩ := kepCertificateLogCutoff_good_derivatives hs
  simp only [kepRadialCoreWeight, kepRadialCoreWeightFirst, kepRadialCoreWeightSecond,
    hM, if_true, h0, h1, h2, sub_self, neg_zero, and_self]

theorem kepRadialCoreWeight_short (M i j : ℕ) (hM : j - i < M) (ell s : ℝ) :
    1 - kepRadialCoreWeight M i j ell s = 1 ∧
      kepRadialCoreWeightFirst M i j ell s = 0 ∧
      kepRadialCoreWeightSecond M i j ell s = 0 := by
  simp only [kepRadialCoreWeight, kepRadialCoreWeightFirst, kepRadialCoreWeightSecond,
    not_le.mpr hM, if_false, sub_zero, and_self]

end

end PGM
