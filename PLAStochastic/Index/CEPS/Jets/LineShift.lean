import PLAStochastic.Index.CEPS.Jets.Integrand
import PLAStochastic.Index.CEPS.Jets.Calculus
import PLAStochastic.Index.CEPS.Jets.RootFree

/-!
# X8: shifting the line of a contour jet, and realness of contour jets

* `integral_vline_eq_of_strip`: a function holomorphic on the closed strip `a ≤ Re z ≤ b` with
  `‖f z‖ ≤ K/(1 + (Im z)²)` there has the same line integral on `Re z = a` and on `Re z = b`;
* `norm_log_le_mul_norm_sub_one`: `‖log z‖ ≤ (3 + 2(|log d| + |log C| + π)) ‖z - 1‖` for
  `Re z ≥ d > 0`, `‖z‖ ≤ C`;
* `cepsContourJetC_eq_of_strip`: the contour jet `(j, m, n)` of a transform `T` does not depend
  on the line `Re s = c ∈ [a, b]` when `T` is holomorphic on the strip, `Re F̃(s, T s) ≥ d > 0`
  and `(1 + |s|)^N |T s| ≤ K` with `N ≥ j + 2`;
* `cepsContourJetC_eq_ofReal_re`: the contour jet is real when `T (conj s) = conj (T s)` on the
  line and `F̃` stays in the slit plane.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set
open PGM.WienerHopf

namespace PGM

/-- **Finite-strip line shift.** If `f` is holomorphic on the closed strip `a ≤ Re z ≤ b` and
`‖f z‖ ≤ K/(1 + (Im z)²)` there, then `∫ f(a + i y) dy = ∫ f(b + i y) dy`. -/
theorem integral_vline_eq_of_strip {f : ℂ → ℂ} {a b K : ℝ} (hab : a ≤ b)
    (hd : ∀ z : ℂ, z.re ∈ Set.Icc a b → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ K / (1 + z.im ^ 2)) :
    ∫ y : ℝ, f (a + y * I) = ∫ y : ℝ, f (b + y * I) := by
  have hint : ∀ c : ℝ, c ∈ Icc a b → Integrable fun y : ℝ => f (c + y * I) := by
    intro c hc
    refine (integrable_inv_one_add_sq.const_mul K).mono'
      (continuous_vline_of_differentiableAt (c := c) fun y =>
        hd _ (by rw [vline_re]; exact hc)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have h := hbound (c + y * I) (by rw [vline_re]; exact hc)
    simpa [div_eq_mul_inv] using h
  have hedge : ∀ t : ℝ, ‖∫ σ in a..b, f (σ + t * I)‖ ≤ K / (1 + t ^ 2) * |b - a| := by
    intro t
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [uIoc_of_le hab] at hσ
    have h := hbound (σ + t * I) (by simp only [add_re, ofReal_re, mul_re, I_re, I_im,
      ofReal_im, mul_zero, sub_zero, mul_one, add_zero]; exact ⟨hσ.1.le, hσ.2⟩)
    simpa using h
  have hlim : Tendsto (fun k : ℕ => K / (1 + (k : ℝ) ^ 2) * |b - a|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 + (k : ℝ) ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds.div_atTop h1).mul_const |b - a|
  refine integral_vertical_eq_of_tendsto hab
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd z (Ioo_subset_Icc_self hz)) (hint a ⟨le_rfl, hab⟩) (hint b ⟨hab, le_rfl⟩)
    tendsto_natCast_atTop_atTop tendsto_natCast_atTop_atTop ?_ ?_
  · exact squeeze_zero_norm (fun k => hedge k) hlim
  · exact squeeze_zero_norm (fun k => (hedge (-(k : ℝ))).trans_eq (by rw [neg_sq])) hlim

/-- `‖log z‖ ≤ (3 + 2(|log d| + |log C| + π)) ‖z - 1‖` for `d ≤ Re z`, `‖z‖ ≤ C`, `d > 0`. -/
theorem norm_log_le_mul_norm_sub_one {z : ℂ} {d C : ℝ} (hd : 0 < d) (h1 : d ≤ z.re)
    (h2 : ‖z‖ ≤ C) :
    ‖Complex.log z‖ ≤ (3 + 2 * (|Real.log d| + |Real.log C| + Real.pi)) * ‖z - 1‖ := by
  have hL : 0 ≤ |Real.log d| + |Real.log C| + Real.pi := by positivity
  have hn := norm_nonneg (z - 1)
  rcases le_or_gt ‖z - 1‖ (1 / 2) with h | h
  · have h3 := Complex.norm_log_one_add_half_le_self h
    rw [add_sub_cancel] at h3
    nlinarith
  · have h3 := norm_log_le_of_re_ge hd h1 h2
    nlinarith

/-- **Line shift of contour jets.** If `T` is holomorphic on the strip `0 < a ≤ Re s ≤ b`,
`Re F̃(s, T s) ≥ d > 0` and `(1 + |s|)^N |T s| ≤ K` there with `N ≥ j + 2`, then the contour jet
`(j, m, n)` is the same on the lines `Re s = a` and `Re s = b`. -/
theorem cepsContourJetC_eq_of_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {T : ℂ → ℂ}
    {d K : ℝ} {N : ℕ} (hd : 0 < d)
    (hT : ∀ s : ℂ, s.re ∈ Set.Icc a b → DifferentiableAt ℂ T s)
    (hF : ∀ s : ℂ, s.re ∈ Set.Icc a b → d ≤ (cepsJetF s (T s)).re)
    (hdec : ∀ s : ℂ, s.re ∈ Set.Icc a b → (1 + ‖s‖) ^ N * ‖T s‖ ≤ K)
    (j m n : ℕ) (hN : j + 2 ≤ N) :
    cepsContourJetC a T j m n = cepsContourJetC b T j m n := by
  -- elementary facts on the strip
  have hsn : ∀ s : ℂ, s.re ∈ Icc a b → a ≤ ‖s‖ := fun s hs => hs.1.trans (re_le_norm s)
  have hs0 : ∀ s : ℂ, s.re ∈ Icc a b → s ≠ 0 := fun s hs h => by
    have := hsn s hs; rw [h, norm_zero] at this; linarith
  have hFeq : ∀ s : ℂ, cepsJetF s (T s) = (1 - T s) * ((s ^ 2 - 1) / s ^ 2) := fun s => by
    rw [cepsJetF, mul_div_assoc]
  have hR : ∀ s : ℂ, s.re ∈ Icc a b → ‖(s ^ 2 - 1) / s ^ 2‖ ≤ 1 + 1 / a ^ 2 := by
    intro s hs
    have hx := hsn s hs
    have hx0 : 0 < ‖s‖ := lt_of_lt_of_le ha hx
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    have h1 := norm_sub_le (s ^ 2) 1
    rw [norm_pow, norm_one] at h1
    have h2 : 1 ≤ ‖s‖ ^ 2 / a ^ 2 := by
      rw [one_le_div (by positivity)]; exact pow_le_pow_left₀ ha.le hx 2
    have h3 : (1 + 1 / a ^ 2) * ‖s‖ ^ 2 = ‖s‖ ^ 2 + ‖s‖ ^ 2 / a ^ 2 := by ring
    linarith
  have hTK : ∀ s : ℂ, s.re ∈ Icc a b → ‖T s‖ ≤ K := fun s hs =>
    (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg s]))).trans
      (hdec s hs)
  have hpow : ∀ s : ℂ, s.re ∈ Icc a b → ∀ i : ℕ, i ≤ N → (1 + ‖s‖) ^ i * ‖T s‖ ≤ K :=
    fun s hs i hi => (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [norm_nonneg s]) hi) (norm_nonneg _)).trans (hdec s hs)
  have hT1 : ∀ s : ℂ, s.re ∈ Icc a b → T s ≠ 1 := fun s hs h => by
    have := hF s hs; rw [cepsJetF, h, sub_self, zero_mul, zero_div, zero_re] at this; linarith
  have hR1 : 0 < 1 + 1 / a ^ 2 := by positivity
  set δ : ℝ := d / (1 + 1 / a ^ 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have h1T : ∀ s : ℂ, s.re ∈ Icc a b → δ ≤ ‖1 - T s‖ := by
    intro s hs
    rw [hδ, div_le_iff₀ hR1]
    calc d ≤ (cepsJetF s (T s)).re := hF s hs
      _ ≤ ‖cepsJetF s (T s)‖ := re_le_norm _
      _ = ‖1 - T s‖ * ‖(s ^ 2 - 1) / s ^ 2‖ := by rw [hFeq, norm_mul]
      _ ≤ ‖1 - T s‖ * (1 + 1 / a ^ 2) := by gcongr; exact hR s hs
  -- the uniform bound `‖G‖ (1 + |s|)² ≤ M` on the strip
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖cepsJetIntegrand j m n s (T s)‖ * (1 + ‖s‖) ^ 2 ≤ M := by
    by_cases hjn : j + n = 0
    · set C : ℝ := (1 + K) * (1 + 1 / a ^ 2)
      set L : ℝ := 3 + 2 * (|Real.log d| + |Real.log C| + Real.pi)
      have hL : 0 ≤ L := by positivity
      refine ⟨L / a ^ (m + 1) * (K * (1 + 1 / a ^ 2) + (1 / a + 1) ^ 2), fun s hs => ?_⟩
      have hx := hsn s hs
      have hx0 : 0 < ‖s‖ := lt_of_lt_of_le ha hx
      have hFC : ‖cepsJetF s (T s)‖ ≤ C := by
        rw [hFeq, norm_mul]
        refine mul_le_mul ((norm_sub_le _ _).trans ?_) (hR s hs) (norm_nonneg _)
          (by linarith [norm_nonneg (T s), hTK s hs])
        rw [norm_one]; linarith [hTK s hs]
      have hlog := norm_log_le_mul_norm_sub_one hd (hF s hs) hFC
      have hF1 : cepsJetF s (T s) - 1 = -(T s * ((s ^ 2 - 1) / s ^ 2)) - 1 / s ^ 2 := by
        rw [cepsJetF]; field_simp [hs0 s hs]; ring
      have hF1n : ‖cepsJetF s (T s) - 1‖ * (1 + ‖s‖) ^ 2 ≤
          K * (1 + 1 / a ^ 2) + (1 / a + 1) ^ 2 := by
        have e1 : ‖cepsJetF s (T s) - 1‖ ≤ ‖T s‖ * (1 + 1 / a ^ 2) + 1 / ‖s‖ ^ 2 := by
          rw [hF1]
          refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
          · rw [norm_neg, norm_mul]; gcongr; exact hR s hs
          · rw [norm_div, norm_one, norm_pow]
        have e2 : (1 + ‖s‖) ^ 2 * ‖T s‖ ≤ K := hpow s hs 2 (by omega)
        have e3 : 1 / ‖s‖ ^ 2 * (1 + ‖s‖) ^ 2 ≤ (1 / a + 1) ^ 2 := by
          have : 1 / ‖s‖ ^ 2 * (1 + ‖s‖) ^ 2 = (1 / ‖s‖ + 1) ^ 2 := by field_simp
          rw [this]
          gcongr
        calc ‖cepsJetF s (T s) - 1‖ * (1 + ‖s‖) ^ 2
            ≤ (‖T s‖ * (1 + 1 / a ^ 2) + 1 / ‖s‖ ^ 2) * (1 + ‖s‖) ^ 2 := by gcongr
          _ = (1 + ‖s‖) ^ 2 * ‖T s‖ * (1 + 1 / a ^ 2) + 1 / ‖s‖ ^ 2 * (1 + ‖s‖) ^ 2 := by ring
          _ ≤ K * (1 + 1 / a ^ 2) + (1 / a + 1) ^ 2 := by gcongr
      rw [cepsJetIntegrand, if_pos hjn, norm_div, norm_pow]
      calc ‖Complex.log (cepsJetF s (T s))‖ / ‖s‖ ^ (m + 1) * (1 + ‖s‖) ^ 2
          ≤ L * ‖cepsJetF s (T s) - 1‖ / a ^ (m + 1) * (1 + ‖s‖) ^ 2 := by gcongr
        _ = L / a ^ (m + 1) * (‖cepsJetF s (T s) - 1‖ * (1 + ‖s‖) ^ 2) := by ring
        _ ≤ L / a ^ (m + 1) * (K * (1 + 1 / a ^ 2) + (1 / a + 1) ^ 2) := by gcongr
    · obtain ⟨C, hC0, hC⟩ := norm_cepsLogDJet_le (j + n - 1) (K := K) hδ0
      refine ⟨C * K / a ^ (m + 1), fun s hs => ?_⟩
      have hx := hsn s hs
      have hD := hC (T s) (hTK s hs) (h1T s hs)
      rw [cepsJetIntegrand, if_neg hjn]
      simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
      calc ‖s‖ ^ j * ‖cepsLogDJet (j + n - 1) (T s)‖ / ‖s‖ ^ (m + 1) * (1 + ‖s‖) ^ 2
          ≤ (1 + ‖s‖) ^ j * (C * ‖T s‖) / a ^ (m + 1) * (1 + ‖s‖) ^ 2 := by
            gcongr
            linarith
        _ = C * ((1 + ‖s‖) ^ (j + 2) * ‖T s‖) / a ^ (m + 1) := by ring
        _ ≤ C * K / a ^ (m + 1) := by gcongr; exact hpow s hs _ hN
  -- holomorphy on the strip
  have hdiff : ∀ s : ℂ, s.re ∈ Icc a b →
      DifferentiableAt ℂ (fun s => cepsJetIntegrand j m n s (T s)) s := by
    intro s hs
    by_cases hjn : j + n = 0
    · have e : (fun s => cepsJetIntegrand j m n s (T s)) =
          fun s => Complex.log (cepsJetF s (T s)) / s ^ (m + 1) := by
        funext s; rw [cepsJetIntegrand, if_pos hjn]
      rw [e]
      have hFd : DifferentiableAt ℂ (fun s => cepsJetF s (T s)) s := by
        unfold cepsJetF
        exact (((differentiableAt_const _).sub (hT s hs)).mul
          ((differentiableAt_id.pow 2).sub_const 1)).div (differentiableAt_id.pow 2)
          (pow_ne_zero 2 (hs0 s hs))
      exact (hFd.clog (Or.inl (lt_of_lt_of_le hd (hF s hs)))).div
        (differentiableAt_id.pow _) (pow_ne_zero _ (hs0 s hs))
    · have e : (fun s => cepsJetIntegrand j m n s (T s)) =
          fun s => s ^ j * (-1) ^ n * cepsLogDJet (j + n - 1) (T s) / s ^ (m + 1) := by
        funext s; rw [cepsJetIntegrand, if_neg hjn]
      rw [e]
      exact (((differentiableAt_id.pow j).mul_const _).mul
        ((differentiableAt_cepsLogDJet _ (hT1 s hs)).comp s (hT s hs))).div
        (differentiableAt_id.pow _) (pow_ne_zero _ (hs0 s hs))
  have key : ∫ y : ℝ, cepsJetIntegrand j m n (a + y * I) (T (a + y * I)) =
      ∫ y : ℝ, cepsJetIntegrand j m n (b + y * I) (T (b + y * I)) := by
    refine integral_vline_eq_of_strip (f := fun s => cepsJetIntegrand j m n s (T s)) (K := M)
      hab hdiff fun z hz => ?_
    have him : 1 + z.im ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
      have h1 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_im_le_norm z) 2
      nlinarith [norm_nonneg z]
    rw [le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left him (norm_nonneg _)).trans (hM z hz)
  rw [cepsContourJetC, cepsContourJetC, key]

/-- **Realness.** If `T (conj s) = conj (T s)` on the line `Re s = c` and `F̃(s, T s)` lies in the
slit plane there, the contour jet `(j, m, n)` is real. -/
theorem cepsContourJetC_eq_ofReal_re {c : ℝ} {T : ℂ → ℂ}
    (hT : ∀ y : ℝ, T (c + (-y) * I) = (starRingEnd ℂ) (T (c + y * I)))
    (hF : ∀ y : ℝ, cepsJetF (c + y * I) (T (c + y * I)) ∈ slitPlane) (j m n : ℕ) :
    cepsContourJetC c T j m n = ((cepsContourJetC c T j m n).re : ℂ) := by
  have hG : ∀ y : ℝ, cepsJetIntegrand j m n (c + ((-y : ℝ) : ℂ) * I)
      (T (c + ((-y : ℝ) : ℂ) * I)) =
      (starRingEnd ℂ) (cepsJetIntegrand j m n (c + y * I) (T (c + y * I))) := by
    intro y
    have hc : (c : ℂ) + -(y : ℂ) * I = (starRingEnd ℂ) (c + y * I) := by
      apply Complex.ext <;> simp
    rw [ofReal_neg, hT y, hc]
    exact cepsJetIntegrand_conj j m n _ _ fun _ => hF y
  have hint : ∫ y : ℝ, cepsJetIntegrand j m n (c + y * I) (T (c + y * I)) =
      (((∫ y : ℝ, cepsJetIntegrand j m n (c + y * I) (T (c + y * I))).re : ℝ) : ℂ) :=
    integral_eq_ofReal_re_of_conj
      (G := fun y : ℝ => cepsJetIntegrand j m n (c + y * I) (T (c + y * I))) hG
  have him : (cepsContourJetC c T j m n).im = 0 := by
    rw [cepsContourJetC, hint, cepsJetCorr]
    split_ifs <;> simp
  exact Complex.ext (by simp) (by simp [him])

end PGM
