import PLAStochastic.Index.CEPS.Actual.Drawup
import PLAStochastic.Index.GEP.SurvivalBound.Certificate.Geometry

/-!
# Path comparisons for the actual outer tails

The positive outer certificate event is contained in drawup survival at slope
`1 / (1 + δ)`. Its missing paths have a reverse crossing of the same band.
A negative outer certificate has a forward crossing at slope `1 / (1 - δ)`.
All comparisons concern the actual gap paths, with the strict crossing convention
of `cepsDrawupOK`. No probabilistic tail estimate is assumed.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Finset

/-- A reverse crossing of the drift-`δ` walk by width `2ε(1+δ)`. -/
def cepsReverseCross (eps δ : ℝ) (g : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
    kWalk 0 (1 + δ) 1 g j - kWalk 0 (1 + δ) 1 g i < -(2 * eps * (1 + δ))

/-- Positive outer certificates, with the deterministic short prefix included. -/
def cepsPositiveOuter (eps δ : ℝ) (g : ℕ → ℝ) (k : ℕ) : Prop :=
  (k : ℝ) ≤ 2 * eps ∨ ∃ ij ∈ certPairs eps k,
    certOK eps (gapKeys g) k ij.1 ij.2 ∧ certSlope eps (gapKeys g) ij.1 ij.2 ≤ 1 / (1 + δ)

/-- Certificates strictly beyond the negative drift cutoff. -/
def cepsNegativeOuter (eps δ : ℝ) (g : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ ij ∈ certPairs eps k,
    certOK eps (gapKeys g) k ij.1 ij.2 ∧ 1 / (1 - δ) < certSlope eps (gapKeys g) ij.1 ij.2

/-- Residuals at a positive slope become drift-unit walk positions by multiplication. -/
theorem cepsWalk_eq_scaled_resid {β : ℝ} (hβ : β ≠ 0) (g : ℕ → ℝ) (n : ℕ) :
    kWalk 0 β 1 g n = β * certResid (1 / β) (gapKeys g) n := by
  unfold kWalk certResid
  field_simp
  ring

/-- All deterministic short prefixes survive the actual drawup. -/
theorem cepsDrawupOK_of_short {eps δ : ℝ} (hδ : 0 ≤ 1 + δ) {g : ℕ → ℝ}
    (hg : ∀ n, 0 ≤ g n) {k : ℕ} (hk : (k : ℝ) ≤ 2 * eps) :
    cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k := by
  intro i j hij hj
  have hsum : gapKeys g i ≤ gapKeys g j := by
    unfold gapKeys
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) (fun n _ _ => hg n)
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold kWalk
  nlinarith [mul_nonneg hδ (show 0 ≤ (2 * eps - j + i : ℝ) by linarith)]

/-- A positive outer certificate has no forward crossing at the cutoff slope. -/
theorem cepsDrawupOK_of_positiveOuter {eps δ : ℝ} (hδ : 0 < 1 + δ) {g : ℕ → ℝ}
    (hg : ∀ n, 0 < g n) {k : ℕ} (h : cepsPositiveOuter eps δ g k) :
    cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k := by
  rcases h with hk | ⟨ij, hij, hcert, hcut⟩
  · exact cepsDrawupOK_of_short hδ.le (fun n => (hg n).le) hk
  intro i j hle hj
  have hp : gapKeys g i ≤ gapKeys g j := by
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · exact (cert_gapKeys_lt (fun n _ => hg n) i j hlt hj).le
  have ho := cert_band_osc hcert (by omega : i ≤ k) hj
  have hm := mul_nonneg (sub_nonneg.mpr hcut) (sub_nonneg.mpr hp)
  rw [certResid_sub] at ho
  have hr : certResid (1 / (1 + δ)) (gapKeys g) j -
      certResid (1 / (1 + δ)) (gapKeys g) i ≤ 2 * eps := by
    rw [certResid_sub]
    nlinarith
  rw [cepsWalk_eq_scaled_resid hδ.ne', cepsWalk_eq_scaled_resid hδ.ne']
  nlinarith

/-- Residual oscillation at one slope is sufficient for feasibility. -/
theorem cepsFeasible_of_osc {eps a : ℝ} {p : ℕ → ℝ} {k : ℕ}
    (h : ∀ i ≤ k, ∀ j ≤ k, certResid a p j - certResid a p i ≤ 2 * eps) :
    prefixAffineFeasible eps p (k + 1) := by
  obtain ⟨i, hi, hmin⟩ := (Finset.range (k + 1)).exists_min_image (certResid a p)
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  exact cert_feasible_of_band (i := i) fun j hj =>
    ⟨sub_nonneg.mpr (hmin j (Finset.mem_range.mpr (by omega))), h i hik j hj⟩

/-- If drawup survives but no positive certificate exists, a reverse crossing occurred. -/
theorem cepsReverseCross_of_drawup_not_positive {eps δ : ℝ} (hδ : 0 < 1 + δ)
    {g : ℕ → ℝ} (hg : ∀ n, 0 < g n) {k : ℕ}
    (hdraw : cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k)
    (hpos : ¬ cepsPositiveOuter eps δ g k) : cepsReverseCross eps δ g k := by
  by_contra hrev
  have hk : 2 * eps < (k : ℝ) := lt_of_not_ge fun h => hpos (Or.inl h)
  have hosc : ∀ i ≤ k, ∀ j ≤ k,
      certResid (1 / (1 + δ)) (gapKeys g) j -
        certResid (1 / (1 + δ)) (gapKeys g) i ≤ 2 * eps := by
    intro i hi j hj
    rcases le_total i j with hij | hji
    · have hw := hdraw i j hij hj
      rw [cepsWalk_eq_scaled_resid hδ.ne', cepsWalk_eq_scaled_resid hδ.ne'] at hw
      nlinarith
    · have hw : -(2 * eps * (1 + δ)) ≤
          kWalk 0 (1 + δ) 1 g i - kWalk 0 (1 + δ) 1 g j := by
        by_contra hn
        exact hrev ⟨j, hj, i, hi, hji, lt_of_not_ge hn⟩
      rw [cepsWalk_eq_scaled_resid hδ.ne', cepsWalk_eq_scaled_resid hδ.ne'] at hw
      nlinarith
  have hfeas := cepsFeasible_of_osc hosc
  have hp := cert_gapKeys_lt (k := k) fun n _ => hg n
  obtain ⟨i, j, hij, hj, hL, hc⟩ := (cert_prefixAffineFeasible_iff hk hp).mp hfeas
  have hs : certSlope eps (gapKeys g) i j ≤ 1 / (1 + δ) :=
    (cert_lowerSlope_le_iff (hp i j hij hj)).mpr (hosc i (by omega) j hj)
  exact hpos (Or.inr ⟨(i, j), mem_certPairs.mpr ⟨hij, hj, hL⟩, hc, hs⟩)

/-- A negative outer certificate forces a forward crossing at drift `-δ`. -/
theorem not_cepsDrawupOK_of_negativeOuter {eps δ : ℝ} (hδ : δ < 1) {g : ℕ → ℝ}
    (hg : ∀ n, 0 < g n) {k : ℕ} (h : cepsNegativeOuter eps δ g k) :
    ¬ cepsDrawupOK (1 - δ) 1 (2 * eps * (1 - δ)) g k := by
  rintro hdraw
  obtain ⟨⟨i, j⟩, hij, -, hs⟩ := h
  obtain ⟨hij, hj, -⟩ := mem_certPairs.mp hij
  have hp := cert_gapKeys_lt (k := k) (fun n _ => hg n) i j hij hj
  have hw := hdraw i j hij.le hj
  rw [cepsWalk_eq_scaled_resid (by linarith : 1 - δ ≠ 0),
    cepsWalk_eq_scaled_resid (by linarith : 1 - δ ≠ 0)] at hw
  have hr : certResid (1 / (1 - δ)) (gapKeys g) j -
      certResid (1 / (1 - δ)) (gapKeys g) i ≤ 2 * eps := by nlinarith
  exact (not_le.mpr hs) ((cert_lowerSlope_le_iff hp).mpr hr)

end

end PGM
