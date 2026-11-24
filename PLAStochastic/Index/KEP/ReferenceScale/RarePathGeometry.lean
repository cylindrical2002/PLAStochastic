import PLAStochastic.Index.KEP.ReferenceScale.CertificateRadial
import PLAStochastic.Index.KEP.ReferenceScale.LongCoreCutoff
import PLAStochastic.Index.GEP.SurvivalBound.ShortSegments

/-!
# The three original rare supports

A stopped prefix forces a centered partial-sum deviation. On a long feasible
prefix, every slope outside the cutoff plateau forces a fixed proportion
deviation of the total gap. A bridge below the explicit core cutoff has
deficit less than thirteen; on the compact slope band its gap sum is at most
one eighth of its length once the tolerance is large.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open Set

theorem kep_stopped_prefix_forces_deviation {eps : ℝ} {k : ℕ} {g : ℕ → ℝ}
    (hstop : gapSegLen eps g ≤ (k : ℕ∞)) :
    ∃ t ≤ k, eps < |gapKeys g t - t| := by
  by_contra hn
  have hg : g ∉ surv_ld' eps k := hn
  have hs : (k : ℕ∞) < gapSegLen eps g := surv_mem_survSet_of_not_ld' hg
  exact (not_lt_of_ge hstop) hs

theorem kep_bad_core_slope_forces_deviation {eps : ℝ} {k i j : ℕ}
    {p : ℕ → ℝ} (hp0 : p 0 = 0) (hpk : 0 ≤ p k) (hk : 16 * eps ≤ k)
    (hok : certOK eps p k i j)
    (ha : certSlope eps p i j ∉ Ioo (3 / 4 : ℝ) (3 / 2)) :
    7 * k / 6 ≤ p k ∨ p k ≤ 3 * k / 4 := by
  have hb := abs_le.mp (cert_abs_sub_le_of_band hp0 hok)
  have hcases : certSlope eps p i j ≤ 3 / 4 ∨ 3 / 2 ≤ certSlope eps p i j := by
    simpa only [mem_Ioo, not_and_or, not_lt] using ha
  rcases hcases with ha | ha
  · left
    have hh := mul_le_mul_of_nonneg_right ha hpk
    nlinarith only [hb.2, hk, hh]
  · right
    have hh := mul_le_mul_of_nonneg_right ha hpk
    nlinarith only [hb.1, hk, hh]

theorem kep_short_core_bridge_deficit {eps : ℝ} (heps : 0 ≤ eps) {L : ℕ}
    (hL : L < kepReferenceGraphBridgeCutoff eps) : (L : ℝ) - 2 * eps < 13 := by
  have hceil := Nat.ceil_lt_add_one heps
  have hcast : (L : ℝ) < kepReferenceGraphBridgeCutoff eps := by exact_mod_cast hL
  unfold kepReferenceGraphBridgeCutoff kepGraphLongCutoff at hcast
  push_cast at hcast
  linarith

theorem kep_short_core_bridge_small_sum {eps S : ℝ} (heps : 104 ≤ eps) {L : ℕ}
    (hL : L < kepReferenceGraphBridgeCutoff eps) (hlong : 2 * eps < L)
    (hS : 0 < S) (ha : (1 / 2 : ℝ) ≤ ((L : ℝ) - 2 * eps) / S) :
    S ≤ (L : ℝ) / 8 := by
  have hdef := kep_short_core_bridge_deficit (by linarith : 0 ≤ eps) hL
  have hh := (le_div_iff₀ hS).mp ha
  have hS26 : S ≤ 26 := by linarith
  have hL208 : (208 : ℝ) < L := by linarith
  linarith

theorem kep_short_certificate_bridge_small_sum {eps : ℝ} (heps : 104 ≤ eps)
    {p : ℕ → ℝ} {i j : ℕ} (hij : i ≤ j)
    (hL : j - i < kepReferenceGraphBridgeCutoff eps) (hlong : 2 * eps < (j : ℝ) - i)
    (hp : p i < p j) (ha : (1 / 2 : ℝ) ≤ certSlope eps p i j) :
    p j - p i ≤ ((j - i : ℕ) : ℝ) / 8 := by
  apply kep_short_core_bridge_small_sum heps hL
  · rw [Nat.cast_sub hij]
    exact hlong
  · exact sub_pos.mpr hp
  · simpa only [certSlope, Nat.cast_sub hij] using ha

theorem kep_radial_rare_support (M i j : ℕ) (ell s : ℝ)
    (h : 1 - kepRadialCoreWeight M i j ell s ≠ 0 ∨
      kepRadialCoreWeightFirst M i j ell s ≠ 0 ∨
      kepRadialCoreWeightSecond M i j ell s ≠ 0) :
    j - i < M ∨ Real.exp (ell - s) ∉ Ioo (3 / 4 : ℝ) (3 / 2) := by
  by_contra hn
  have hM : M ≤ j - i := by
    by_contra hM
    exact hn (Or.inl (not_le.mp hM))
  have hs : Real.exp (ell - s) ∈ Ioo (3 / 4 : ℝ) (3 / 2) := by
    by_contra hs
    exact hn (Or.inr hs)
  obtain ⟨h0, h1, h2⟩ := kepRadialCoreWeight_good M i j hM hs
  rcases h with h | h | h
  · exact h h0
  · exact h h1
  · exact h h2

end

end PGM
