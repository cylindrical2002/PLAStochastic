import PLAStochastic.Index.GEP.StrongApprox.Saddle.ConditionalGlobalBound
import PLAStochastic.Index.GEP.StrongApprox.Saddle.TiltedDensityOffMean

/-! # WP5: smoothing-independent saddle density envelopes -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped Real ENNReal NNReal

/-- Exact tilted density at an arbitrary sum observation. -/
theorem UnivClass.saCenteredSumDensity_tilt_at {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : UnivClass vlo vhi κ₃ B θ ν) {lam : ℝ} (hlam : |lam| < θ)
    {s : ℝ} (hs : 0 < s) {l : ℕ} (hl : 0 < l) (w : ℝ) :
    saCenteredSumDensity ν s l (l * w) =
      Real.exp (-(l : ℝ) * (lam * w - saSmoothCGF ν s lam)) / Real.sqrt l *
        saGaussianDensity ((convPow (saRecenteredTilt ν lam) l).map ((Real.sqrt l)⁻¹ * ·))
          (Real.toNNReal (s ^ 2)) (Real.sqrt l * (w - deriv (saSmoothCGF ν s) lam)) := by
  let μ := (ν : Measure ℝ).map (fun y => y - 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact h.integrable_exp_centered hlam.le
  have ht := saGaussianDensity_convPow_tilt_at μ hM
    (v := Real.toNNReal (s ^ 2)) (by simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge]) hl
    (deriv (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam) w
  have hc : cgf id μ lam = cgf (fun y : ℝ => y - 1) (ν : Measure ℝ) lam :=
    sa_cgf_centered_map ν lam
  have hr : (μ.tilted (fun y => lam * y)).map
      (fun y => y - deriv (cgf (fun z : ℝ => z - 1) (ν : Measure ℝ)) lam) =
      saRecenteredTilt ν lam := sa_recentered_tilt_centered_map ν lam
  rw [Real.coe_toNNReal _ (sq_nonneg s), hc, hr] at ht
  have he : (l : ℝ) * (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ) lam +
      s ^ 2 * lam ^ 2 / 2 - lam * w) = -(l : ℝ) * (lam * w - saSmoothCGF ν s lam) := by
    unfold saSmoothCGF
    ring
  have hx : Real.sqrt (l : ℝ) * (w - deriv (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam -
      s ^ 2 * lam) = Real.sqrt l * (w - deriv (saSmoothCGF ν s) lam) := by
    rw [h.deriv_saSmoothCGF hlam s]
    ring
  rw [he, hx] at ht
  exact ht

/-- The all-point local CLT bounds every normalized tilted smoothing density by
one class constant; the smoothing width is allowed to tend to zero. -/
theorem exists_uniform_saRecenteredTilt_density_upper
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ lam : ℝ, |lam| ≤ saTiltRadius vlo B θ → ∀ s : ℝ, 0 < s →
      ∀ l : ℕ, 2 ≤ l → 1 / s ≤ (l : ℝ) ^ 8 → ∀ x : ℝ,
        saGaussianDensity ((convPow (saRecenteredTilt ν lam) l).map ((Real.sqrt l)⁻¹ * ·))
          (Real.toNNReal (s ^ 2)) x ≤ K := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saRecenteredTilt_density vlo vhi κ₃ B θ D c
    hvlo hvhi hB hθ hD hc
  let M := (Real.sqrt (2 * π * (3 / 4 * vlo)))⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M + C, add_pos hM hC, ?_⟩
  intro ν hν hsm lam hlam s hs l hl hscale x
  have he := (abs_le.mp (hb ν hν hsm lam hlam s hs l hl hscale x)).2
  have hv := (hν.centered_cgf_variance_bracket hvlo hθ hlam).1
  have hlo : 3 / 4 * vlo ≤
      iteratedDeriv 2 (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam + s ^ 2 := by
    nlinarith [hν.var_ge, sq_nonneg s]
  have hV : 0 ≤ iteratedDeriv 2 (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam + s ^ 2 :=
    (by positivity : 0 ≤ 3 / 4 * vlo).trans hlo
  have hpeak := gaussianPDFReal_le_inv_sqrt 0 x
    (Real.toNNReal (iteratedDeriv 2 (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam + s ^ 2))
  rw [Real.coe_toNNReal _ hV] at hpeak
  have hroot : 0 < Real.sqrt (2 * π * (3 / 4 * vlo)) := by positivity
  have hgauss : gaussianPDFReal 0
      (Real.toNNReal (iteratedDeriv 2 (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam + s ^ 2)) x ≤ M := by
    apply hpeak.trans
    simpa only [one_div, M] using one_div_le_one_div_of_le hroot
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlo (by positivity)))
  have hlroot : 1 ≤ Real.sqrt (l : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg l)]
    exact_mod_cast (show 1 ≤ l by omega)
  have herror : C / Real.sqrt l ≤ C := div_le_self hC.le hlroot
  linarith

/-- Uniform global sum-density envelope, with no inverse smoothing factor. -/
theorem exists_uniform_saCenteredSumDensity_global_upper
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → ∀ l : ℕ, 2 ≤ l → 1 / s ≤ (l : ℝ) ^ 8 → ∀ w : ℝ,
        saCenteredSumDensity ν s l (l * w) ≤
          K / Real.sqrt l * Real.exp (-(l : ℝ) * saGlobalRate vlo B θ ν s w) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_saRecenteredTilt_density_upper
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨K, hK, ?_⟩
  intro ν hν hsm s hs l hl hscale w
  obtain ⟨lam, hlam, heq⟩ := hν.exists_saGlobalRate_saddle hvlo hθ s w
  have hlt : |lam| < θ := (hlam.trans (saTiltRadius_le_half vlo B hθ)).trans_lt (by linarith)
  rw [hν.saCenteredSumDensity_tilt_at hlt hs (by omega) w, ← heq]
  calc
    _ ≤ Real.exp (-(l : ℝ) * saGlobalRate vlo B θ ν s w) / Real.sqrt l * K :=
      mul_le_mul_of_nonneg_left (hb ν hν hsm lam hlam s hs l hl hscale _)
        (by positivity)
    _ = _ := by ring

/-- Uniform conditional envelope after cancellation of the parent saddle exponent. -/
theorem exists_uniform_saSplitDensity_rate_upper
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ u : ℝ, |u| ≤ saMeanRadius vlo B θ / 2 → ∀ t : ℝ,
        saSplitDensity (saCenteredSumDensity ν s l) (2 * l * u) (l * (u + t)) ≤
          K / Real.sqrt l *
          Real.exp (-(l : ℝ) * (4 / (5 * (vhi + 1))) *
            min (t ^ 2) (saMeanRadius vlo B θ / 2 * |t|)) := by
  obtain ⟨C, hC, hlo⟩ := exists_uniform_saCenteredSumDensity_lower
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  obtain ⟨U, hU, hhi⟩ := exists_uniform_saCenteredSumDensity_global_upper
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  have hM := saCenterNormalizer_pos hvhi
  refine ⟨C, 4 * saCenterNormalizer vhi * U ^ 2, hC, by positivity, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge u hu t
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have h2l : 2 ≤ 2 * l := by omega
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  have hroot2 : Real.sqrt (l : ℝ) ≤ Real.sqrt (2 * l : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show l ≤ 2 * l by omega))
  have hscale2 : 1 / s ≤ ((2 * l : ℕ) : ℝ) ^ 8 := hscale.trans
    (pow_le_pow_left₀ hlr.le (by exact_mod_cast (show l ≤ 2 * l by omega)) 8)
  have hu' : |u| ≤ saMeanRadius vlo B θ := by
    have := (saMeanRadius_pos (B := B) hvlo hθ).le
    linarith
  have hden := hlo ν hν hsm s hs hs1 (2 * l) h2l hscale2 (hlarge.trans hroot2) u hu'
  have hp := hhi ν hν hsm s hs l hl hscale (u + t)
  have hm := hhi ν hν hsm s hs l hl hscale (u - t)
  rw [saSplitDensity_centeredSum ν hs hl0]
  let A := U / Real.sqrt l
  let K := 2 * saCenterNormalizer vhi * Real.sqrt (2 * (l : ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  have hden' : Real.exp (-((2 * (l : ℝ)) * saRate vlo B θ ν s u)) / K ≤
      saCenteredSumDensity ν s (2 * l) (2 * l * u) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, neg_mul] using hden
  have hquot := sa_positive_quotient_exp_bound
    (a := (l : ℝ) * saGlobalRate vlo B θ ν s (u + t))
    (b := (l : ℝ) * saGlobalRate vlo B θ ν s (u - t))
    (d := 2 * (l : ℝ) * saRate vlo B θ ν s u)
    (saCenteredSumDensity_pos ν hs hl0 ((l : ℝ) * (u - t))).le
    (saCenteredSumDensity_pos ν hs (show 0 < 2 * l by omega) (2 * l * u))
    (show 0 ≤ A by dsimp [A]; positivity) hK
    (by simpa only [neg_mul] using hp) (by simpa only [neg_mul] using hm) hden'
  have hexp : -((l : ℝ) * saGlobalRate vlo B θ ν s (u + t) +
      (l : ℝ) * saGlobalRate vlo B θ ν s (u - t) -
      2 * (l : ℝ) * saRate vlo B θ ν s u) ≤
      -(l : ℝ) * (4 / (5 * (vhi + 1))) * min (t ^ 2) (saMeanRadius vlo B θ / 2 * |t|) := by
    have hthree := hν.saGlobalRate_three_point_lower hvlo hθ
      (show |s| ≤ 1 by rwa [abs_of_pos hs]) hu t
    rw [hν.saGlobalRate_eq_saRate hvlo hθ s hu'] at hthree
    nlinarith [mul_le_mul_of_nonneg_left hthree hlr.le]
  have hrt : Real.sqrt (2 * (l : ℝ)) ≤ 2 * Real.sqrt l := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * (l : ℝ) by positivity),
      Real.sq_sqrt hlr.le, Real.sqrt_nonneg (2 * (l : ℝ))]
  have hcoef : A ^ 2 * K ≤ (4 * saCenterNormalizer vhi * U ^ 2) / Real.sqrt l := by
    dsimp [K]
    calc
      _ ≤ A ^ 2 * (2 * saCenterNormalizer vhi * (2 * Real.sqrt l)) := by
        gcongr
      _ = _ := by dsimp [A]; field_simp; ring
  apply hquot.trans
  exact mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)

end

end PGM
