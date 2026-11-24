import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullTilt
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.AllSlopes

/-! # Genuine short marked bridges, including endpoint insertions -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1000000

/-- Positive physical gaps force every true random increment below one, at
every initial point and for the fixed density representative. -/
theorem kernel_density_up_zero_shift {J : Set ℝ} {D θ vlo vhi a : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {f : ℝ → ℝ} (hfz : ∀ x ≤ 0, f x = 0) (ha : 0 < a)
    {n : ℕ} (hn : 1 ≤ n) {y z : ℝ} (hz : y + (n : ℝ) ≤ z) :
    krDens J ν f 1 a n y z = 0 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [krDens_succ]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_pos_iidLaw (hν.momClass hθ hvlo).pos] with g hg
  simp only [Pi.zero_apply]
  have hS : 0 ≤ gapKeys g n' := Finset.sum_nonneg fun i _ => (hg i).le
  have hy : kWalk y 1 a g n' ≤ y + n' := by
    unfold kWalk
    nlinarith
  have hnz : y + (n' : ℝ) + 1 ≤ z := by push_cast at hz; linarith
  have harg : (kWalk y 1 a g n' + 1 - z) / a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  unfold krKer
  rw [hfz _ harg, zero_div, mul_zero, mul_zero]

/-- The actual upward marked bridge vanishes whenever its total number of
steps is too short to cross the band. Zero random sides are included. -/
theorem kernel_full_marked_up_short_zero {D θ vlo vhi a w x : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {f : ℝ → ℝ} (hfz : ∀ t ≤ 0, f t = 0) (ha : 0 < a) (hx : 0 ≤ x)
    (l r : ℕ) (hlen : (l : ℝ) + r + 1 ≤ w) :
    kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r 0 w = 0 := by
  have hax : 0 ≤ a * x := mul_nonneg ha.le hx
  cases l with
  | zero =>
    cases r with
    | zero => rfl
    | succ r =>
      simp only [kernelMarkedFullDens]
      rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha (by omega : 1 ≤ r + 1)
        (by push_cast at hlen ⊢; linarith)]
      exact mul_zero _
  | succ l =>
    cases r with
    | zero =>
      simp only [kernelMarkedFullDens]
      rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha (by omega : 1 ≤ l + 1)
        (by push_cast at hlen ⊢; linarith)]
      exact zero_mul _
    | succ r =>
      unfold kernelMarkedFullDens kernelMarkedDens
      apply integral_eq_zero_of_ae
      filter_upwards [] with u
      simp only [Pi.zero_apply]
      by_cases hu : (l + 1 : ℕ) ≤ u
      · rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha (by omega : 1 ≤ l + 1)
          (by simpa only [zero_add] using hu), zero_mul]
      · rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha (by omega : 1 ≤ r + 1)
          (by push_cast at hlen ⊢; push_cast at hu; linarith), mul_zero]

/-- A fixed positive tilt makes every true short downward marked bridge
exponentially small. The estimate uses no derivative of the input density and
includes insertions adjacent to either endpoint. -/
theorem kernel_regLaw_full_marked_down_short (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ t, 0 ≤ f t) → (∀ t ≤ 0, f t = 0) →
        (∀ t, f t ≤ D * Real.exp (-θ * t)) →
        (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)) →
      ∀ a w x : ℝ, 1 / 2 ≤ a → a ≤ 2 → 0 < w → 0 ≤ x → x ≤ w / 8 →
      ∀ l r : ℕ, (l : ℝ) + r ≤ w / 4 →
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r w 0 ≤ K * Real.exp (-c * w) := by
  let R := kernelTiltClassRadius D θ vlo vhi
  let lam := min R (1 / (4 * vhi))
  have hvhi : 0 < vhi := hvlo.trans_le hv
  have hR : 0 < R := kernelTiltClassRadius_pos hθ hvlo hv
  have hlam : 0 < lam := lt_min hR (by positivity)
  have hlR : lam ≤ R := min_le_left _ _
  have hlv : lam ≤ 1 / (4 * vhi) := min_le_right _ _
  have hlrad : |lam| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) := by
    rw [abs_of_pos hlam]
    exact hlR.trans (min_le_left _ _)
  have hlθ : |lam| ≤ θ / 2 :=
    (hlrad.trans (saTiltRadius_le_half _ _ (by positivity))).trans (by linarith)
  refine ⟨lam / 8, 2 * D * Real.exp θ, by positivity, by positivity, ?_⟩
  intro ν hν f hf hf0 hfz hfe hνf a w x halo hahi hw hx hxw l r hlen
  have ha : 0 < a := by linarith
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hlθ
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun t => lam * t)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun t => lam * t), hp⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun t => lam * t) := rfl
  have hfD (t : ℝ) : f t ≤ D := by
    by_cases ht : t ≤ 0
    · rw [hfz t ht]
      exact hD.le
    · exact (hfe t).trans (mul_le_of_le_one_right hD.le (Real.exp_le_one_iff.mpr (by nlinarith)))
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (t : ℝ) : 0 ≤ kernelTiltDensity ν lam f t := mul_nonneg (Real.exp_nonneg _) (hf0 t)
  have hftD := hν.kernelTiltDensity_le hθ hvlo hfz hfe hlθ
  have hτf := (kernel_tilt_density_measure ν hf hf0 hνf (hU.kernel_integrable_exp_raw hlθ))
  have hh := kernel_fullDens_tilt (J := Icc 0 w) measurableSet_Icc ν τ hf hf0 hfD
    (hU.kernel_integrable_exp_raw hlθ) hτ hftD 1 x ha.ne' l r w 0
  have hb := kernelFar_fullDens_le_div (J := Icc 0 w) (β := 1) (t := x) measurableSet_Icc (by simp)
    τ hft hft0 hftD (hτ.trans hτf) ha.ne' l r w 0
  rw [abs_of_pos ha] at hb
  have hcoef : D * Real.exp θ / a ≤ 2 * D * Real.exp θ := by
    apply (div_le_iff₀ ha).mpr
    have hh' := mul_le_mul_of_nonneg_right halo (show 0 ≤ 2 * D * Real.exp θ by positivity)
    nlinarith
  have hquad := hU.kernel_centered_cgf_upper hvlo (show 0 < θ / 2 by positivity) hlrad
  have hsmall : vhi * lam ^ 2 ≤ lam / 4 := by
    have hh' := (le_div_iff₀ (show 0 < 4 * vhi by positivity)).mp hlv
    have hh'' := mul_le_mul_of_nonneg_right hh' hlam.le
    nlinarith
  have hraw : cgf id (ν : Measure ℝ) lam ≤ 5 * lam / 4 := by
    rw [hU.kernel_raw_cgf_eq hlθ]
    linarith
  have he : -((l : ℝ) + r) * (lam * 1 / a - cgf id (ν : Measure ℝ) lam) +
      lam * (0 - w) / a + lam * x - lam * 1 / a ≤ -(lam / 8) * w := by
    have hN : 0 ≤ (l : ℝ) + r := by positivity
    have hr := mul_le_mul_of_nonneg_left hraw hN
    have hlin : lam / 2 ≤ lam / a := by
      apply (le_div_iff₀ ha).mpr
      nlinarith
    have hlinN := mul_le_mul_of_nonneg_left hlin hN
    have hlinW := mul_le_mul_of_nonneg_left hlin hw.le
    have hNw := mul_le_mul_of_nonneg_left hlen hlam.le
    have hxw' := mul_le_mul_of_nonneg_left hxw hlam.le
    have he' : lam * (0 - w) / a = -(w * (lam / a)) := by ring
    rw [he']
    simp only [mul_one]
    nlinarith
  rw [hh]
  have hh' := mul_le_mul (Real.exp_le_exp.mpr he) (hb.trans hcoef)
    (kernelMarkedFullDens_nonneg τ hft0 _ _ _ _ _ _ _) (Real.exp_nonneg _)
  exact hh'.trans_eq (mul_comm _ _)

end
end PGM
