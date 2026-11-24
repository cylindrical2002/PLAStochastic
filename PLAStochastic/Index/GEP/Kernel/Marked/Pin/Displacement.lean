import PLAStochastic.Index.GEP.Kernel.Marked.Pin.SaddleScaling

/-! # Pointwise Bernstein displacement bounds for the genuine killed densities -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Optimizing the bounded quadratic Chernoff exponent, for either displacement sign. -/
theorem kernel_displacement_tilt_choice {r v N : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hN : 0 < N) (q : ℝ) :
    ∃ lam : ℝ, |lam| ≤ r ∧
      N * v * lam ^ 2 + lam * q ≤
        -(min (r / 2) (1 / (4 * v))) * min (q ^ 2 / N) |q| := by
  let t := min r (|q| / (2 * v * N))
  let c := min (r / 2) (1 / (4 * v))
  have ht0 : 0 ≤ t := le_min hr.le (by positivity)
  have htr : t ≤ r := min_le_left _ _
  have htq : t ≤ |q| / (2 * v * N) := min_le_right _ _
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have htquad : N * v * t ^ 2 - t * |q| ≤ -(t * |q| / 2) := by
    have hh := (le_div_iff₀ (show 0 < 2 * v * N by positivity)).mp htq
    have hh' := mul_le_mul_of_nonneg_right hh ht0
    nlinarith
  have hmin : c * min (q ^ 2 / N) |q| ≤ t * |q| / 2 := by
    by_cases hcase : r ≤ |q| / (2 * v * N)
    · have ht : t = r := min_eq_left hcase
      calc
        c * min (q ^ 2 / N) |q| ≤ c * |q| :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
        _ ≤ (r / 2) * |q| := mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
        _ = t * |q| / 2 := by rw [ht]; ring
    · have ht : t = |q| / (2 * v * N) := min_eq_right (not_le.mp hcase).le
      calc
        c * min (q ^ 2 / N) |q| ≤ c * (q ^ 2 / N) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
        _ ≤ (1 / (4 * v)) * (q ^ 2 / N) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = t * |q| / 2 := by rw [ht]; field_simp; nlinarith [sq_abs q]
  by_cases hq : 0 ≤ q
  · refine ⟨-t, by simpa only [abs_neg, abs_of_nonneg ht0] using htr, ?_⟩
    rw [abs_of_nonneg hq] at htquad hmin ⊢
    nlinarith
  · refine ⟨t, by simpa only [abs_of_nonneg ht0] using htr, ?_⟩
    rw [abs_of_neg (not_le.mp hq)] at htquad hmin ⊢
    nlinarith

/-- A class-uniform pointwise displacement bound for every legitimate density representative.
The statement holds at every pair of endpoints, for any measurable killing set and both directions. -/
theorem kernel_regLaw_displacement (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x ≤ 0, f x = 0) →
        (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ J : Set ℝ, MeasurableSet J → ∀ β : ℝ, (β = 1 ∨ β = -1) →
      ∀ n : ℕ, 1 ≤ n → ∀ y z : ℝ,
        krDens J ν f β β n y z ≤ D * Real.exp θ *
          Real.exp (-c * min ((z - y) ^ 2 / (n : ℝ)) |z - y|) := by
  let r := saTiltRadius vlo (2 * D / θ) (θ / 2)
  have hr : 0 < r := saTiltRadius_pos hvlo (by positivity)
  have hvhi : 0 < vhi := hvlo.trans_le hv
  let c := min (r / 2) (1 / (4 * vhi))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfz hfe hνf J hJ β hβ n hn y z
  have hβabs : |β| = 1 := by rcases hβ with rfl | rfl <;> norm_num
  have hβne : β ≠ 0 := by intro he; simp [he] at hβabs
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let q := (z - y) / β
  have hqabs : |q| = |z - y| := by
    change |(z - y) / β| = |z - y|
    rw [abs_div, hβabs, div_one]
  have hq2 : q ^ 2 = (z - y) ^ 2 := by
    nlinarith [sq_abs q, sq_abs (z - y), congrArg (fun x : ℝ => x ^ 2) hqabs]
  obtain ⟨lam, hlam, hcost⟩ := kernel_displacement_tilt_choice hr hvhi hn0 q
  have hl : |lam| ≤ θ / 2 :=
    (hlam.trans (saTiltRadius_le_half _ _ (by positivity))).trans (by linarith)
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hl
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun x => lam * x)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun x => lam * x), hp⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) := rfl
  have hfD (x : ℝ) : f x ≤ D := by
    by_cases hx : 0 < x
    · exact (hfe x).trans (mul_le_of_le_one_right hD.le (Real.exp_le_one_iff.mpr (by nlinarith)))
    · rw [hfz x (not_lt.mp hx)]
      exact hD.le
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x := mul_nonneg (Real.exp_nonneg _) (hf0 x)
  have hftD (x : ℝ) : kernelTiltDensity ν lam f x ≤ D * Real.exp θ :=
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hl x
  have hk := kernel_krDens_tilt hJ ν τ hf hf0 hfD
    (hU.kernel_integrable_exp_raw hl) hτ hftD β hβne hn y z
  have hrw := hU.kernel_raw_cgf_eq hl
  have hquad := hU.kernel_centered_cgf_upper hvlo (by positivity) hlam
  have he : -(n : ℝ) * (lam * β / β - cgf id (ν : Measure ℝ) lam) + lam * (z - y) / β ≤
      -c * min ((z - y) ^ 2 / (n : ℝ)) |z - y| := by
    rw [mul_div_cancel_right₀ lam hβne, hrw]
    have hquad' := mul_le_mul_of_nonneg_left hquad hn0.le
    rw [hq2, hqabs] at hcost
    change (n : ℝ) * vhi * lam ^ 2 + lam * ((z - y) / β) ≤ _ at hcost
    rw [← mul_div_assoc] at hcost
    dsimp [c] at *
    nlinarith
  rw [hk]
  have hb := krDens_le_div τ hft0 hftD n y z (J := J) (β := β) (a := β)
  rw [hβabs, div_one] at hb
  calc
    _ ≤ Real.exp (-(n : ℝ) * (lam * β / β - cgf id (ν : Measure ℝ) lam) + lam * (z - y) / β) *
        (D * Real.exp θ) := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ ≤ Real.exp (-c * min ((z - y) ^ 2 / (n : ℝ)) |z - y|) * (D * Real.exp θ) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by ring

end
end PGM
