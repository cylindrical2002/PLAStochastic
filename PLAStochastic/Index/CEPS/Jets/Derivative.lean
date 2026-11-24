import PLAStochastic.Index.CEPS.Jets.RootFree
import PLAStochastic.Index.CEPS.Jets.Integrand
import PLAStochastic.Index.CEPS.Jets.Calculus
import PLAStochastic.ForMathlib.Analysis.Complex.LineCauchy

/-!
# X8: derivatives of the root-free factor at the origin

For a transform `T` on the line `Re s = c > 0` with

* decay `(1 + ‖s‖)^N ‖T s‖ ≤ K`,
* separation `‖1 - e^{ts - q} T s‖ ≥ δ` and `F̃(s; t, q) ∈ slitPlane` for `|t| < t₁`, `‖q‖ < q₁`,
* the logarithm bound `‖log F̃‖ ≤ K₁ (‖T s‖ + 1/‖s‖)`,

the mixed derivatives of the root-free factor `cepsRootFreeL c T` at the origin (drift `t` real,
then `ζ`, then `q`) are the contour jets:

  `∂_q^n ∂_ζ^m ∂_t^j L(0; 0, 0) = cepsContourJetC c T j m n`   (`j + 2 ≤ N`).

Writing `x = ts - q`, every parameter derivative of `log F̃(s, e^x T s)` is a derivative in `x`:
`Λ_0 = log F̃`, `Λ_{k+1} = D_{k+1}` (`cepsJetLam`), `∂_x Λ_k = Λ_{k+1}`. Each step differentiates
under the integral sign (`iteratedDeriv_integral_of_dominated`).
-/

noncomputable section

open MeasureTheory Complex Metric Set Filter Topology

namespace PGM

/-- `Λ_0(s, w) = log F̃(s, w)`, `Λ_{k+1}(s, w) = D_{k+1}(w)`. -/
def cepsJetLam (k : ℕ) (s w : ℂ) : ℂ :=
  if k = 0 then Complex.log (cepsJetF s w) else cepsLogDJet (k - 1) w

theorem cepsJetIntegrand_eq_lam (j m n : ℕ) (s w : ℂ) :
    cepsJetIntegrand j m n s w = s ^ j * (-1) ^ n * cepsJetLam (j + n) s w / s ^ (m + 1) := by
  unfold cepsJetIntegrand cepsJetLam
  by_cases h : j + n = 0
  · have hj : j = 0 := by omega
    have hn : n = 0 := by omega
    subst hj hn
    simp
  · rw [if_neg h, if_neg h]

theorem one_ne_of_cepsJetF_mem {s w : ℂ} (hF : cepsJetF s w ∈ slitPlane) : w ≠ 1 := by
  intro h; apply slitPlane_ne_zero hF; rw [cepsJetF, h]; simp

theorem hasDerivAt_cepsJetLam (k : ℕ) (s w x : ℂ) (hF : cepsJetF s (cexp x * w) ∈ slitPlane) :
    HasDerivAt (fun x => cepsJetLam k s (cexp x * w)) (cepsJetLam (k + 1) s (cexp x * w)) x := by
  rcases k with _ | k
  · simp only [cepsJetLam, if_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel]
    exact hasDerivAt_log_cepsJetF_exp s w x hF
  · simp only [cepsJetLam, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel]
    exact hasDerivAt_cepsLogDJet_exp k w x (one_ne_of_cepsJetF_mem hF)

/-- Real-drift derivative of `Λ_k(s, e^{ts - q} w)`. -/
theorem hasDerivAt_cepsJetLam_drift (k : ℕ) (s w q : ℂ) (t : ℝ)
    (hF : cepsJetF s (cexp (t * s - q) * w) ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => cepsJetLam k s (cexp (t * s - q) * w))
      (cepsJetLam (k + 1) s (cexp (t * s - q) * w) * s) t := by
  have hx : HasDerivAt (fun z : ℂ => z * s - q) s (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const s).sub_const q
  have h := ((hasDerivAt_cepsJetLam k s w ((t : ℂ) * s - q) hF).comp (t : ℂ) hx).comp_ofReal
  exact h

/-- Discount derivative of `Λ_k(s, e^{ts - q} w)`. -/
theorem hasDerivAt_cepsJetLam_disc (k : ℕ) (s w q : ℂ) (t : ℝ)
    (hF : cepsJetF s (cexp (t * s - q) * w) ∈ slitPlane) :
    HasDerivAt (fun q : ℂ => cepsJetLam k s (cexp (t * s - q) * w))
      (-cepsJetLam (k + 1) s (cexp (t * s - q) * w)) q := by
  have hx : HasDerivAt (fun q : ℂ => (t : ℂ) * s - q) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub ((t : ℂ) * s)
  have h := (hasDerivAt_cepsJetLam k s w ((t : ℂ) * s - q) hF).comp q hx
  simpa [Function.comp_def] using h

theorem norm_cepsJetLam_succ_le (k : ℕ) {K δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s w : ℂ, ‖w‖ ≤ K → δ ≤ ‖1 - w‖ → ‖cepsJetLam (k + 1) s w‖ ≤ C * ‖w‖ := by
  obtain ⟨C, hC, h⟩ := norm_cepsLogDJet_le k (K := K) hδ
  refine ⟨C, hC, fun s w hw h1 => ?_⟩
  simp only [cepsJetLam, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel]
  exact h w hw h1

/-! ### Real bounds on the line -/

theorem norm_vline_ge (c y : ℝ) : |y| ≤ ‖(c : ℂ) + y * I‖ := by
  have := abs_im_le_norm ((c : ℂ) + y * I); simpa using this

theorem norm_vline_ge_re (c y : ℝ) : c ≤ ‖(c : ℂ) + y * I‖ := by
  have := re_le_norm ((c : ℂ) + y * I); simpa using this

theorem vline_ne_zero {c : ℝ} (hc : 0 < c) (y : ℝ) : (c : ℂ) + y * I ≠ 0 := by
  intro h; have := norm_vline_ge_re c y; rw [h, norm_zero] at this; linarith

/-- `r^a/(1+r)^N ≤ (1 + y²)⁻¹` for `r = ‖c + iy‖` and `a + 2 ≤ N`. -/
theorem vline_pow_div_le (c y : ℝ) {a N : ℕ} (h : a + 2 ≤ N) :
    ‖(c : ℂ) + y * I‖ ^ a / (1 + ‖(c : ℂ) + y * I‖) ^ N ≤ (1 + y ^ 2)⁻¹ := by
  set r := ‖(c : ℂ) + y * I‖
  have hr : 0 ≤ r := norm_nonneg _
  have hy : |y| ≤ r := norm_vline_ge c y
  have hy2 : y ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have h1 : 1 + y ^ 2 ≤ (1 + r) ^ 2 := by nlinarith
  have h2 : (1 + r) ^ a * (1 + r) ^ 2 ≤ (1 + r) ^ N := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by linarith) h
  have h3 : r ^ a ≤ (1 + r) ^ a := pow_le_pow_left₀ hr (by linarith) a
  have hpos : 0 < (1 + r) ^ a := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc r ^ a ≤ (1 + r) ^ a := h3
    _ = (1 + y ^ 2)⁻¹ * ((1 + r) ^ a * (1 + y ^ 2)) := by field_simp
    _ ≤ (1 + y ^ 2)⁻¹ * (1 + r) ^ N := by
        gcongr
        exact (mul_le_mul_of_nonneg_left h1 hpos.le).trans h2

/-- `1/‖c + iy‖² ≤ max 1 (1/c²) (1 + y²)⁻¹`. -/
theorem inv_norm_vline_sq_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    (‖(c : ℂ) + y * I‖ ^ 2)⁻¹ ≤ (1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹ := by
  have e : ‖(c : ℂ) + y * I‖ ^ 2 = c ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  rw [e]
  rw [inv_le_iff_one_le_mul₀' (by positivity)]
  have : (1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹ * (c ^ 2 + y ^ 2) =
      (c ^ 2 + y ^ 2 + 1 + y ^ 2 / c ^ 2) / (1 + y ^ 2) := by field_simp; ring
  rw [mul_comm, this, le_div_iff₀ (by positivity)]
  have : 0 ≤ y ^ 2 / c ^ 2 := by positivity
  nlinarith [sq_nonneg c]

theorem integrable_const_mul_inv_one_add_sq (C : ℝ) :
    Integrable fun y : ℝ => C * (1 + y ^ 2)⁻¹ :=
  integrable_inv_one_add_sq.const_mul C

/-! ### Standing bounds on the line -/

section Line

variable {c : ℝ} {T : ℂ → ℂ} {t₁ q₁ δ K K₁ : ℝ} {N : ℕ}

theorem norm_cexp_drift_le (hc : 0 < c) {t : ℝ} (ht : |t| < t₁) {q : ℂ} (hq : ‖q‖ < q₁) (y : ℝ) :
    ‖cexp (t * ((c : ℂ) + y * I) - q)‖ ≤ Real.exp (t₁ * c + q₁) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h1 : (t * ((c : ℂ) + y * I) - q).re = t * c - q.re := by simp
  rw [h1]
  have h2 := neg_abs_le q.re
  have h3 := abs_re_le_norm q
  have h4 : t * c ≤ t₁ * c := by
    have := le_abs_self t
    nlinarith
  linarith

theorem norm_T_le_of_dec (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (y : ℝ) : ‖T (c + y * I)‖ ≤ K / (1 + ‖(c : ℂ) + y * I‖) ^ N := by
  rw [le_div_iff₀ (by positivity), mul_comm]; exact hdec y

theorem norm_T_le_K (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (y : ℝ) : ‖T (c + y * I)‖ ≤ K := by
  have h1 : 1 ≤ (1 + ‖(c : ℂ) + y * I‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg ((c : ℂ) + y * I)])
  have := hdec y
  nlinarith [norm_nonneg (T (c + y * I))]

theorem pow_mul_norm_T_le (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hK : 0 ≤ K) {a : ℕ} (ha : a + 2 ≤ N) (y : ℝ) :
    ‖(c : ℂ) + y * I‖ ^ a * ‖T (c + y * I)‖ ≤ K * (1 + y ^ 2)⁻¹ := by
  have h1 := norm_T_le_of_dec hdec y
  have h2 := vline_pow_div_le c y ha
  calc ‖(c : ℂ) + y * I‖ ^ a * ‖T (c + y * I)‖
      ≤ ‖(c : ℂ) + y * I‖ ^ a * (K / (1 + ‖(c : ℂ) + y * I‖) ^ N) := by gcongr
    _ = K * (‖(c : ℂ) + y * I‖ ^ a / (1 + ‖(c : ℂ) + y * I‖) ^ N) := by ring
    _ ≤ K * (1 + y ^ 2)⁻¹ := by gcongr

theorem norm_T_le_inv (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hc : 0 < c) (hN : 1 ≤ N) (y : ℝ) : ‖T (c + y * I)‖ ≤ K * ‖(c : ℂ) + y * I‖⁻¹ := by
  have hs : 0 < ‖(c : ℂ) + y * I‖ := lt_of_lt_of_le hc (norm_vline_ge_re c y)
  have h1 : ‖(c : ℂ) + y * I‖ ≤ (1 + ‖(c : ℂ) + y * I‖) ^ N :=
    (by linarith : ‖(c : ℂ) + y * I‖ ≤ 1 + ‖(c : ℂ) + y * I‖).trans
      (le_self_pow₀ (by linarith) (by omega))
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  calc ‖T (c + y * I)‖ * ‖(c : ℂ) + y * I‖
      ≤ ‖T (c + y * I)‖ * (1 + ‖(c : ℂ) + y * I‖) ^ N :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ := mul_comm _ _
    _ ≤ K := hdec y

theorem inv_one_add_sq_le_inv_norm {c : ℝ} (hc : 0 < c) (y : ℝ) :
    (1 + y ^ 2)⁻¹ ≤ (1 + c) * ‖(c : ℂ) + y * I‖⁻¹ := by
  have hs : 0 < ‖(c : ℂ) + y * I‖ := lt_of_lt_of_le hc (norm_vline_ge_re c y)
  have h1 : ‖(c : ℂ) + y * I‖ ≤ (1 + c) * (1 + y ^ 2) := by
    have ht : ‖(c : ℂ) + y * I‖ ≤ c + |y| := by
      calc ‖(c : ℂ) + y * I‖ ≤ ‖(c : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = c + |y| := by simp [abs_of_pos hc]
    have hy : |y| ≤ 1 + y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]
    nlinarith [sq_nonneg y]
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  calc (1 + y ^ 2)⁻¹ * ‖(c : ℂ) + y * I‖ ≤ (1 + y ^ 2)⁻¹ * ((1 + c) * (1 + y ^ 2)) := by
        gcongr
    _ = 1 + c := by field_simp

theorem cepsJetLam_zero (s w : ℂ) : cepsJetLam 0 s w = Complex.log (cepsJetF s w) := by
  simp [cepsJetLam]

theorem cepsJetLam_succ (k : ℕ) (s w : ℂ) : cepsJetLam (k + 1) s w = cepsLogDJet k w := by
  simp [cepsJetLam]

theorem continuous_cepsJetF_line (hc : 0 < c) (hTc : Continuous fun y : ℝ => T (c + y * I))
    (t : ℝ) (q : ℂ) :
    Continuous fun y : ℝ =>
      cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) := by
  have hW : Continuous fun y : ℝ => cexp (t * (c + y * I) - q) * T (c + y * I) :=
    (by fun_prop : Continuous fun y : ℝ => cexp (t * ((c : ℂ) + y * I) - q)).mul hTc
  unfold cepsJetF
  exact Continuous.div ((continuous_const.sub hW).mul (by fun_prop)) (by fun_prop)
    fun y => pow_ne_zero 2 (vline_ne_zero hc y)

theorem continuous_cepsJetLam_line (hc : 0 < c) (hTc : Continuous fun y : ℝ => T (c + y * I))
    (k : ℕ) {t : ℝ} {q : ℂ}
    (hF : ∀ y : ℝ, cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) ∈ slitPlane) :
    Continuous fun y : ℝ =>
      cepsJetLam k (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) := by
  rcases k with _ | k
  · simp only [cepsJetLam_zero]
    exact (continuous_cepsJetF_line hc hTc t q).clog hF
  · simp only [cepsJetLam_succ]
    have hW : Continuous fun y : ℝ => cexp (t * (c + y * I) - q) * T (c + y * I) :=
      (by fun_prop : Continuous fun y : ℝ => cexp (t * ((c : ℂ) + y * I) - q)).mul hTc
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact ContinuousAt.comp (g := cepsLogDJet k)
      (differentiableAt_cepsLogDJet k (one_ne_of_cepsJetF_mem (hF y))).continuousAt
      hW.continuousAt

theorem lam_pow_bound (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hsep : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      δ ≤ ‖1 - cexp (t * (c + y * I) - q) * T (c + y * I)‖)
    (i a : ℕ) (ha : a + 2 ≤ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      ‖(c : ℂ) + y * I‖ ^ a *
        ‖cepsJetLam (i + 1) (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I))‖ ≤
          B * (1 + y ^ 2)⁻¹ := by
  set E := Real.exp (t₁ * c + q₁)
  obtain ⟨C, hC, hCb⟩ := norm_cepsJetLam_succ_le i (K := E * K) hδ
  refine ⟨C * E * K, by positivity, fun y t ht q hq => ?_⟩
  have hE := norm_cexp_drift_le hc ht hq y
  have hT := norm_T_le_K hdec y
  have hW : ‖cexp (t * ((c : ℂ) + y * I) - q) * T (c + y * I)‖ ≤ E * ‖T (c + y * I)‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right hE (norm_nonneg _)
  have hWK : ‖cexp (t * ((c : ℂ) + y * I) - q) * T (c + y * I)‖ ≤ E * K :=
    hW.trans (mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le)
  have h1 := hCb (c + y * I) _ hWK (hsep y t ht q hq)
  have h2 := pow_mul_norm_T_le hdec hK ha y
  calc ‖(c : ℂ) + y * I‖ ^ a *
        ‖cepsJetLam (i + 1) (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I))‖
      ≤ ‖(c : ℂ) + y * I‖ ^ a * (C * (E * ‖T (c + y * I)‖)) := by
        gcongr; exact h1.trans (mul_le_mul_of_nonneg_left hW hC)
    _ = C * E * (‖(c : ℂ) + y * I‖ ^ a * ‖T (c + y * I)‖) := by ring
    _ ≤ C * E * (K * (1 + y ^ 2)⁻¹) := by gcongr
    _ = C * E * K * (1 + y ^ 2)⁻¹ := by ring

theorem lam_pow_bound_inv (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hsep : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      δ ≤ ‖1 - cexp (t * (c + y * I) - q) * T (c + y * I)‖)
    (hlog : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      ‖Complex.log (cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)))‖ ≤
        K₁ * (‖T (c + y * I)‖ + ‖(c : ℂ) + y * I‖⁻¹))
    (j : ℕ) (hj : j + 2 ≤ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      ‖(c : ℂ) + y * I‖ ^ j *
        ‖cepsJetLam j (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I))‖ ≤
          B * ‖(c : ℂ) + y * I‖⁻¹ := by
  rcases j with _ | i
  · refine ⟨K₁ * (K + 1), by positivity, fun y t ht q hq => ?_⟩
    rw [pow_zero, one_mul, cepsJetLam_zero]
    refine (hlog y t ht q hq).trans ?_
    have := norm_T_le_inv hdec hc (by omega) y
    have hs := inv_nonneg.mpr (norm_nonneg ((c : ℂ) + y * I))
    calc K₁ * (‖T (c + y * I)‖ + ‖(c : ℂ) + y * I‖⁻¹)
        ≤ K₁ * (K * ‖(c : ℂ) + y * I‖⁻¹ + ‖(c : ℂ) + y * I‖⁻¹) := by gcongr
      _ = K₁ * (K + 1) * ‖(c : ℂ) + y * I‖⁻¹ := by ring
  · obtain ⟨B, hB, hb⟩ := lam_pow_bound (t₁ := t₁) (q₁ := q₁) hc hδ hK hdec hsep i (i + 1) hj
    refine ⟨B * (1 + c), by positivity, fun y t ht q hq => ?_⟩
    refine (hb y t ht q hq).trans ?_
    calc B * (1 + y ^ 2)⁻¹ ≤ B * ((1 + c) * ‖(c : ℂ) + y * I‖⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_one_add_sq_le_inv_norm hc y) hB
      _ = B * (1 + c) * ‖(c : ℂ) + y * I‖⁻¹ := by ring

end Line

/-! ### Step A: drift derivatives -/

section Steps

variable {c : ℝ} {T : ℂ → ℂ} {t₁ q₁ δ K K₁ : ℝ} {N : ℕ}

theorem iteratedDeriv_sub_const_fun {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (b : F) (x : 𝕜) :
    iteratedDeriv n (fun t => f t - b) x = iteratedDeriv n f x - if n = 0 then b else 0 := by
  rcases n with _ | n
  · simp
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', if_neg (Nat.succ_ne_zero n), sub_zero]
    have : deriv (fun t => f t - b) = deriv f := funext fun t => deriv_sub_const (f := f) (x := t) b
    rw [this]

theorem iteratedDeriv_add_const_fun {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) (f : 𝕜 → F) (b : F) (x : 𝕜) :
    iteratedDeriv n (fun t => f t + b) x = iteratedDeriv n f x + if n = 0 then b else 0 := by
  rcases n with _ | n
  · simp
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', if_neg (Nat.succ_ne_zero n), add_zero]
    have : deriv (fun t => f t + b) = deriv f := funext fun t => deriv_add_const (f := f) (x := t) b
    rw [this]

theorem mem_ball_zero_real_iff {t r : ℝ} : t ∈ Metric.ball (0 : ℝ) r ↔ |t| < r := by
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]

theorem norm_two_pi_inv : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv]
  congr 1
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- **Step A.** Drift derivatives of the root-free factor at `t = 0`. -/
theorem iteratedDeriv_drift_cepsRootFreeL (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (ht₁ : 0 < t₁)
    (hTc : Continuous fun y : ℝ => T (c + y * I))
    (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hsep : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      δ ≤ ‖1 - cexp (t * (c + y * I) - q) * T (c + y * I)‖)
    (hslit : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) ∈ slitPlane)
    (hlog : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      ‖Complex.log (cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)))‖ ≤
        K₁ * (‖T (c + y * I)‖ + ‖(c : ℂ) + y * I‖⁻¹))
    (j : ℕ) (hj : j + 2 ≤ N) {q ζ : ℂ} (hq : ‖q‖ < q₁) (hζ : ζ.re < c) :
    iteratedDeriv j (fun t : ℝ => cepsRootFreeL c T t q ζ) 0 =
      (∫ y : ℝ, (2 * Real.pi : ℂ)⁻¹ * (((c : ℂ) + y * I) ^ j *
        cepsJetLam j (c + y * I) (cexp (-q) * T (c + y * I)) / (c + y * I - ζ))) -
      if j = 0 then Complex.log (1 - ζ) else 0 := by
  set φ : ℕ → ℝ → ℝ → ℂ := fun k t y => (2 * Real.pi : ℂ)⁻¹ * (((c : ℂ) + y * I) ^ k *
    cepsJetLam k (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) / (c + y * I - ζ))
    with hφ
  have hsz : ∀ y : ℝ, (c : ℂ) + y * I - ζ ≠ 0 := vline_sub_ne_zero hζ.ne
  have hszn : ∀ y : ℝ, c - ζ.re ≤ ‖(c : ℂ) + y * I - ζ‖ := fun y =>
    (le_abs_self _).trans (abs_sub_re_le_norm_vline c y ζ)
  have hcz : 0 < c - ζ.re := by linarith
  -- measurability
  have hmeas : ∀ k ≤ j, ∀ t ∈ Metric.ball (0 : ℝ) t₁, AEStronglyMeasurable (φ k t) := by
    intro k _ t ht
    have ht' := mem_ball_zero_real_iff.mp ht
    have h1 := continuous_cepsJetLam_line hc hTc k (t := t) (q := q)
      (fun y => hslit y t ht' q hq)
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.mul (((by fun_prop : Continuous fun y : ℝ =>
      ((c : ℂ) + y * I) ^ k).mul h1).div (by fun_prop) hsz)
  -- base integrability
  obtain ⟨B0, hB0, hb0⟩ := lam_pow_bound_inv (t₁ := t₁) (q₁ := q₁) hc hδ hK hK₁ hdec hsep hlog 0
    (by omega)
  have hint : ∀ t ∈ Metric.ball (0 : ℝ) t₁, Integrable (φ 0 t) := by
    intro t ht
    have ht' := mem_ball_zero_real_iff.mp ht
    refine (((integrable_inv_mul_line hc hζ).norm).const_mul ((2 * Real.pi)⁻¹ * B0)).mono'
      (hmeas 0 (Nat.zero_le _) t ht) (ae_of_all _ fun y => ?_)
    have hb := hb0 y t ht' q hq
    rw [pow_zero, one_mul] at hb
    have hs0 : 0 < ‖(c : ℂ) + y * I‖ := lt_of_lt_of_le hc (norm_vline_ge_re c y)
    have hsz0 : 0 < ‖(c : ℂ) + y * I - ζ‖ := norm_pos_iff.mpr (hsz y)
    have e : ‖φ 0 t y‖ = (2 * Real.pi)⁻¹ *
        (‖cepsJetLam 0 (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I))‖ /
          ‖(c : ℂ) + y * I - ζ‖) := by
      simp only [hφ, pow_zero, one_mul]; rw [norm_mul, norm_two_pi_inv, norm_div]
    rw [e, norm_inv, norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖cepsJetLam 0 (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I))‖ /
          ‖(c : ℂ) + y * I - ζ‖
        ≤ B0 * ‖(c : ℂ) + y * I‖⁻¹ / ‖(c : ℂ) + y * I - ζ‖ := by gcongr
      _ = B0 * (‖(c : ℂ) + y * I‖ * ‖(c : ℂ) + y * I - ζ‖)⁻¹ := by field_simp
  -- bounds for the derivatives
  have hb : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (k < j → ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q' : ℂ,
      ‖q'‖ < q₁ → ‖(c : ℂ) + y * I‖ ^ (k + 1) *
        ‖cepsJetLam (k + 1) (c + y * I) (cexp (t * (c + y * I) - q') * T (c + y * I))‖ ≤
          B * (1 + y ^ 2)⁻¹) := by
    intro k
    by_cases hk : k < j
    · obtain ⟨B, hB0, hB⟩ := lam_pow_bound (t₁ := t₁) (q₁ := q₁) hc hδ hK hdec hsep k (k + 1)
        (by omega)
      exact ⟨B, hB0, fun _ => hB⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose B hBnn hB using hb
  have key := iteratedDeriv_integral_of_dominated (𝕜 := ℝ) (μ := volume) (φ := φ)
    (B := fun k y => (2 * Real.pi)⁻¹ * (B k * (1 + y ^ 2)⁻¹ / (c - ζ.re))) (N := j)
    isOpen_ball hmeas hint ?_ ?_ ?_ 0 (Metric.mem_ball_self ht₁)
  · -- conclude
    have hfun : (fun t : ℝ => cepsRootFreeL c T t q ζ) =
        fun t => (∫ y : ℝ, φ 0 t y) - Complex.log (1 - ζ) := by
      funext t
      simp only [cepsRootFreeL, hφ, pow_zero, one_mul, cepsJetLam_zero]
      rw [integral_const_mul]
    rw [hfun, iteratedDeriv_sub_const_fun, key]
    simp only [hφ, ofReal_zero, zero_mul, zero_sub]
  · intro k hk y t ht
    have ht' := mem_ball_zero_real_iff.mp ht
    have h := hasDerivAt_cepsJetLam_drift k (c + y * I) (T (c + y * I)) q t (hslit y t ht' q hq)
    have h2 := ((h.const_mul (((c : ℂ) + y * I) ^ k)).div_const ((c : ℂ) + y * I - ζ)).const_mul
      (2 * Real.pi : ℂ)⁻¹
    refine h2.congr_deriv ?_
    simp only [hφ]
    ring
  · intro k hk y t ht
    have ht' := mem_ball_zero_real_iff.mp ht
    have h := hB k hk y t ht' q hq
    have e : ‖φ (k + 1) t y‖ = (2 * Real.pi)⁻¹ * (‖(c : ℂ) + y * I‖ ^ (k + 1) *
        ‖cepsJetLam (k + 1) (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I))‖ /
          ‖(c : ℂ) + y * I - ζ‖) := by
      simp only [hφ]; rw [norm_mul, norm_two_pi_inv, norm_div, norm_mul, norm_pow]
    rw [e]
    exact mul_le_mul_of_nonneg_left (div_le_div₀ (by have := hBnn k; positivity) h hcz
      (hszn y)) (by positivity)
  · intro k _
    exact ((integrable_inv_one_add_sq.const_mul (B k)).div_const (c - ζ.re)).const_mul _

theorem cexp_zero_drift (s q : ℂ) : cexp (((0 : ℝ) : ℂ) * s - q) = cexp (-q) := by simp

theorem norm_vline_sub_ge_half {c : ℝ} (y : ℝ) {ζ : ℂ}
    (hζ : ζ ∈ Metric.ball (0 : ℂ) (c / 2)) :
    ‖(c : ℂ) + y * I‖ / 2 ≤ ‖(c : ℂ) + y * I - ζ‖ := by
  have h1 : ‖ζ‖ < c / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hζ
  have h2 := norm_vline_ge_re c y
  have h3 := norm_sub_norm_le ((c : ℂ) + y * I) ζ
  linarith

theorem ball_half_re_lt {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) (c / 2)) :
    ζ.re < c := by
  have h1 : ‖ζ‖ < c / 2 := by rwa [Metric.mem_ball, dist_zero_right] at hζ
  have := re_le_norm ζ
  linarith

/-- `‖H‖ ‖S - ζ‖^{-(k+1)} ≤ 2^{k+1} B c^{-k} (1 + 1/c²) (1 + y²)⁻¹` when `‖H‖ ≤ B/‖S‖`. -/
theorem norm_div_vline_pow_le {c : ℝ} (hc : 0 < c) (y : ℝ) {ζ : ℂ}
    (hζ : ζ ∈ Metric.ball (0 : ℂ) (c / 2)) {H : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hH : ‖H‖ ≤ B * ‖(c : ℂ) + y * I‖⁻¹) (k : ℕ) :
    ‖H‖ * (‖(c : ℂ) + y * I - ζ‖ ^ (k + 1))⁻¹ ≤
      2 ^ (k + 1) * B * (c ^ k)⁻¹ * (1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹ := by
  set r := ‖(c : ℂ) + y * I‖
  have hr : c ≤ r := norm_vline_ge_re c y
  have hr0 : 0 < r := lt_of_lt_of_le hc hr
  have hd := norm_vline_sub_ge_half y hζ
  have hd0 : 0 < r / 2 := by positivity
  have h1 : (‖(c : ℂ) + y * I - ζ‖ ^ (k + 1))⁻¹ ≤ ((r / 2) ^ (k + 1))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hd0.le hd _)
  have h2 : (r ^ k)⁻¹ ≤ (c ^ k)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hr _)
  have h3 := inv_norm_vline_sq_le hc y
  calc ‖H‖ * (‖(c : ℂ) + y * I - ζ‖ ^ (k + 1))⁻¹
      ≤ B * r⁻¹ * ((r / 2) ^ (k + 1))⁻¹ := by gcongr
    _ = 2 ^ (k + 1) * B * (r ^ k)⁻¹ * (r ^ 2)⁻¹ := by
        rw [div_pow, inv_div]; field_simp; ring
    _ ≤ 2 ^ (k + 1) * B * (c ^ k)⁻¹ * ((1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

theorem contDiffAt_log_one_sub (n : ℕ) :
    ContDiffAt ℂ n (fun ζ : ℂ => Complex.log (1 - ζ)) 0 := by
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => Complex.log (1 - ζ)) (Metric.ball 0 1) := by
    intro ζ hζ
    have h1 : ‖ζ‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hζ
    have h2 : 0 < (1 - ζ).re := by
      have := re_le_norm ζ; simp only [sub_re, one_re]; linarith
    exact ((differentiableAt_const _).sub differentiableAt_id).clog (Or.inl h2)
      |>.differentiableWithinAt
  exact (hd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

theorem iteratedDeriv_log_one_sub_zero (m : ℕ) :
    iteratedDeriv m (fun ζ : ℂ => Complex.log (1 - ζ)) 0 =
      if m = 0 then 0 else -(((m - 1).factorial : ℕ) : ℂ) := by
  rcases m with _ | m
  · simp
  · rw [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, ← iteratedDeriv_neg_log_one_sub m,
      ← iteratedDeriv_fun_neg]
    simp

/-- **Step B.** Spatial derivatives at `ζ = 0` of the drift derivatives. -/
theorem iteratedDeriv_spatial_cepsRootFreeL (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hK₁ : 0 ≤ K₁) (ht₁ : 0 < t₁)
    (hTc : Continuous fun y : ℝ => T (c + y * I))
    (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hsep : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      δ ≤ ‖1 - cexp (t * (c + y * I) - q) * T (c + y * I)‖)
    (hslit : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) ∈ slitPlane)
    (hlog : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      ‖Complex.log (cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)))‖ ≤
        K₁ * (‖T (c + y * I)‖ + ‖(c : ℂ) + y * I‖⁻¹))
    (j m : ℕ) (hj : j + 2 ≤ N) {q : ℂ} (hq : ‖q‖ < q₁) :
    iteratedDeriv m (fun ζ : ℂ => iteratedDeriv j (fun t : ℝ => cepsRootFreeL c T t q ζ) 0) 0 =
      (∫ y : ℝ, (2 * Real.pi : ℂ)⁻¹ * ((m.factorial : ℂ) * (((c : ℂ) + y * I) ^ j *
        cepsJetLam j (c + y * I) (cexp (-q) * T (c + y * I))) * (((c : ℂ) + y * I) ^ (m + 1))⁻¹)) +
      if j = 0 ∧ m ≠ 0 then (((m - 1).factorial : ℕ) : ℂ) else 0 := by
  set H : ℝ → ℂ := fun y => ((c : ℂ) + y * I) ^ j *
    cepsJetLam j (c + y * I) (cexp (-q) * T (c + y * I)) with hH
  set U : Set ℂ := Metric.ball 0 (c / 2) with hU
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self (by positivity)
  have hslit0 : ∀ y : ℝ, cepsJetF (c + y * I) (cexp (((0 : ℝ) : ℂ) * (c + y * I) - q) *
      T (c + y * I)) ∈ slitPlane := fun y => hslit y 0 (by simpa using ht₁) q hq
  have hHc : Continuous H := by
    have := continuous_cepsJetLam_line hc hTc j hslit0
    simp only [cexp_zero_drift] at this
    exact (by fun_prop : Continuous fun y : ℝ => ((c : ℂ) + y * I) ^ j).mul this
  obtain ⟨BH, hBH, hbH⟩ := lam_pow_bound_inv (t₁ := t₁) (q₁ := q₁) hc hδ hK hK₁ hdec hsep hlog j hj
  have hHb : ∀ y : ℝ, ‖H y‖ ≤ BH * ‖(c : ℂ) + y * I‖⁻¹ := by
    intro y
    have := hbH y 0 (by simpa using ht₁) q hq
    simp only [cexp_zero_drift] at this
    simpa only [hH, norm_mul, norm_pow] using this
  have hsz : ∀ ζ ∈ U, ∀ y : ℝ, (c : ℂ) + y * I - ζ ≠ 0 := fun ζ hζ y =>
    vline_sub_ne_zero (ball_half_re_lt hc hζ).ne y
  set φ : ℕ → ℂ → ℝ → ℂ := fun k ζ y =>
    (2 * Real.pi : ℂ)⁻¹ * ((k.factorial : ℂ) * H y * (((c : ℂ) + y * I - ζ) ^ (k + 1))⁻¹)
    with hφ
  have hmeas : ∀ k ≤ m + 1, ∀ ζ ∈ U, AEStronglyMeasurable (φ k ζ) := by
    intro k _ ζ hζ
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.mul ((continuous_const.mul hHc).mul
      ((by fun_prop : Continuous fun y : ℝ => ((c : ℂ) + y * I - ζ) ^ (k + 1)).inv₀
        fun y => pow_ne_zero _ (hsz ζ hζ y)))
  have hnorm : ∀ k ζ y, ‖φ k ζ y‖ = (2 * Real.pi)⁻¹ * ((k.factorial : ℝ) *
      (‖H y‖ * (‖(c : ℂ) + y * I - ζ‖ ^ (k + 1))⁻¹)) := by
    intro k ζ y
    simp only [hφ]
    rw [norm_mul, norm_two_pi_inv, norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    ring
  set Bf : ℕ → ℝ → ℝ := fun k y => (2 * Real.pi)⁻¹ * ((k.factorial : ℝ) *
    (2 ^ (k + 1) * BH * (c ^ k)⁻¹ * (1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹)) with hBf
  have hbound' : ∀ k, ∀ y, ∀ ζ ∈ U, ‖φ k ζ y‖ ≤ Bf k y := by
    intro k y ζ hζ
    rw [hnorm]
    simp only [hBf]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (norm_div_vline_pow_le hc y hζ hBH (hHb y) k) (by positivity)) (by positivity)
  have hBfi : ∀ k, Integrable (Bf k) := fun k =>
    (integrable_inv_one_add_sq.const_mul (2 ^ (k + 1) * BH * (c ^ k)⁻¹ * (1 + 1 / c ^ 2))).const_mul
      _ |>.const_mul _
  have hint : ∀ ζ ∈ U, Integrable (φ 0 ζ) := fun ζ hζ =>
    (hBfi 0).mono' (hmeas 0 (Nat.zero_le _) ζ hζ) (ae_of_all _ fun y => hbound' 0 y ζ hζ)
  have hderiv : ∀ k, ∀ y, ∀ ζ ∈ U, HasDerivAt (fun ζ => φ k ζ y) (φ (k + 1) ζ y) ζ := by
    intro k y ζ hζ
    have hne := hsz ζ hζ y
    have h0 := (hasDerivAt_pow (k + 1) ((c : ℂ) + y * I - ζ)).comp ζ
      ((hasDerivAt_id ζ).const_sub ((c : ℂ) + y * I))
    have h1 : HasDerivAt (fun ζ : ℂ => ((c : ℂ) + y * I - ζ) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * ((c : ℂ) + y * I - ζ) ^ (k + 1 - 1) * (-1)) ζ := h0
    have h2 := ((h1.inv (pow_ne_zero _ hne)).const_mul ((k.factorial : ℂ) * H y)).const_mul
      (2 * Real.pi : ℂ)⁻¹
    refine h2.congr_deriv ?_
    simp only [hφ, Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have key := iteratedDeriv_integral_of_dominated (𝕜 := ℂ) (μ := volume) (φ := φ)
    (B := fun k y => Bf (k + 1) y) (N := m) isOpen_ball
    (fun k hk ζ hζ => hmeas k (by omega) ζ hζ) hint (fun k _ y ζ hζ => hderiv k y ζ hζ)
    (fun k _ y ζ hζ => hbound' (k + 1) y ζ hζ) (fun k _ => hBfi (k + 1)) 0 h0U
  -- differentiability of the integral (for the subtraction of `log(1 - ζ)`)
  have hdiff : DifferentiableOn ℂ (fun ζ => ∫ y, φ 0 ζ y) U := by
    intro ζ₀ hζ₀
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun ζ y => φ 0 ζ y) (F' := fun ζ y => φ 1 ζ y) (bound := Bf 1)
      (isOpen_ball.mem_nhds hζ₀)
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds hζ₀) fun ζ hζ => hmeas 0 (Nat.zero_le _) ζ hζ)
      (hint ζ₀ hζ₀) (hmeas 1 (by omega) ζ₀ hζ₀)
      (ae_of_all _ fun y ζ hζ => hbound' 1 y ζ hζ) (hBfi 1)
      (ae_of_all _ fun y ζ hζ => hderiv 0 y ζ hζ)
    exact this.2.differentiableAt.differentiableWithinAt
  have hcd : ContDiffAt ℂ m (fun ζ => ∫ y, φ 0 ζ y) 0 :=
    (hdiff.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds h0U)
  -- the function near `0`
  have hev : (fun ζ : ℂ => iteratedDeriv j (fun t : ℝ => cepsRootFreeL c T t q ζ) 0) =ᶠ[𝓝 0]
      fun ζ => (∫ y, φ 0 ζ y) - if j = 0 then Complex.log (1 - ζ) else 0 := by
    filter_upwards [isOpen_ball.mem_nhds h0U] with ζ hζ
    rw [iteratedDeriv_drift_cepsRootFreeL hc hδ hK hK₁ ht₁ hTc hdec hsep hslit hlog j hj hq
      (ball_half_re_lt hc hζ)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hφ, hH, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one, div_eq_mul_inv]
  rw [hev.iteratedDeriv_eq]
  have hfin : ∫ y, φ m 0 y = ∫ y : ℝ, (2 * Real.pi : ℂ)⁻¹ * ((m.factorial : ℂ) *
      (((c : ℂ) + y * I) ^ j * cepsJetLam j (c + y * I) (cexp (-q) * T (c + y * I))) *
        (((c : ℂ) + y * I) ^ (m + 1))⁻¹) := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hφ, hH, sub_zero]
  by_cases hj0 : j = 0
  · simp only [if_pos hj0]
    rw [iteratedDeriv_fun_sub hcd (contDiffAt_log_one_sub m), key, iteratedDeriv_log_one_sub_zero,
      hfin]
    rcases m with _ | m
    · simp
    · rw [if_neg (Nat.succ_ne_zero m), if_pos ⟨hj0, Nat.succ_ne_zero m⟩, sub_neg_eq_add]
  · simp only [if_neg hj0, sub_zero, if_neg (fun h : j = 0 ∧ m ≠ 0 => hj0 h.1), add_zero]
    rw [key, hfin]

/-- **The derivative formula.** The mixed derivatives of the root-free factor at the origin
(real drift, then `ζ`, then `q`) are the contour jets. -/
theorem iteratedDeriv_cepsRootFreeL (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hK₁ : 0 ≤ K₁) (ht₁ : 0 < t₁) (hq₁ : 0 < q₁)
    (hTc : Continuous fun y : ℝ => T (c + y * I))
    (hdec : ∀ y : ℝ, (1 + ‖(c : ℂ) + y * I‖) ^ N * ‖T (c + y * I)‖ ≤ K)
    (hsep : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      δ ≤ ‖1 - cexp (t * (c + y * I) - q) * T (c + y * I)‖)
    (hslit : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)) ∈ slitPlane)
    (hlog : ∀ y : ℝ, ∀ t : ℝ, |t| < t₁ → ∀ q : ℂ, ‖q‖ < q₁ →
      ‖Complex.log (cepsJetF (c + y * I) (cexp (t * (c + y * I) - q) * T (c + y * I)))‖ ≤
        K₁ * (‖T (c + y * I)‖ + ‖(c : ℂ) + y * I‖⁻¹))
    (j m n : ℕ) (hj : j + 2 ≤ N) :
    iteratedDeriv n (fun q : ℂ => iteratedDeriv m (fun ζ : ℂ =>
      iteratedDeriv j (fun t : ℝ => cepsRootFreeL c T t q ζ) 0) 0) 0 =
      cepsContourJetC c T j m n := by
  set U : Set ℂ := Metric.ball 0 q₁ with hU
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hq₁
  have hqU : ∀ q ∈ U, ‖q‖ < q₁ := fun q hq => by rwa [Metric.mem_ball, dist_zero_right] at hq
  have ht0 : |(0 : ℝ)| < t₁ := by simpa using ht₁
  set corr : ℂ := if j = 0 ∧ m ≠ 0 then (((m - 1).factorial : ℕ) : ℂ) else 0 with hcorr
  set ψ : ℕ → ℂ → ℝ → ℂ := fun k q y => (2 * Real.pi : ℂ)⁻¹ * ((m.factorial : ℂ) *
    (((c : ℂ) + y * I) ^ j * ((-1) ^ k * cepsJetLam (j + k) (c + y * I) (cexp (-q) * T (c + y * I)))) *
      (((c : ℂ) + y * I) ^ (m + 1))⁻¹) with hψ
  have hslitq : ∀ q ∈ U, ∀ y : ℝ, cepsJetF (c + y * I) (cexp (((0 : ℝ) : ℂ) * (c + y * I) - q) *
      T (c + y * I)) ∈ slitPlane := fun q hq y => hslit y 0 ht0 q (hqU q hq)
  have hmeas : ∀ k ≤ n, ∀ q ∈ U, AEStronglyMeasurable (ψ k q) := by
    intro k _ q hq
    have h1 := continuous_cepsJetLam_line hc hTc (j + k) (hslitq q hq)
    simp only [cexp_zero_drift] at h1
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.mul ((continuous_const.mul ((by fun_prop : Continuous fun y : ℝ =>
      ((c : ℂ) + y * I) ^ j).mul (continuous_const.mul h1))).mul
      ((by fun_prop : Continuous fun y : ℝ => ((c : ℂ) + y * I) ^ (m + 1)).inv₀
        fun y => pow_ne_zero _ (vline_ne_zero hc y)))
  have hnorm : ∀ k q y, ‖ψ k q y‖ = (2 * Real.pi)⁻¹ * ((m.factorial : ℝ) *
      (‖(c : ℂ) + y * I‖ ^ j * ‖cepsJetLam (j + k) (c + y * I) (cexp (-q) * T (c + y * I))‖) *
        (‖(c : ℂ) + y * I‖ ^ (m + 1))⁻¹) := by
    intro k q y
    simp only [hψ]
    rw [norm_mul, norm_two_pi_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_pow,
      norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  have hinvp : ∀ y : ℝ, (‖(c : ℂ) + y * I‖ ^ (m + 1))⁻¹ ≤ (c ^ (m + 1))⁻¹ := fun y =>
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le (norm_vline_ge_re c y) _)
  -- bounds
  have hb : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ∀ q ∈ U,
      ‖(c : ℂ) + y * I‖ ^ j * ‖cepsJetLam (j + k + 1) (c + y * I) (cexp (-q) * T (c + y * I))‖ ≤
        B * (1 + y ^ 2)⁻¹ := by
    intro k
    obtain ⟨B, hB0, hB⟩ := lam_pow_bound (t₁ := t₁) (q₁ := q₁) hc hδ hK hdec hsep (j + k) j hj
    refine ⟨B, hB0, fun y q hq => ?_⟩
    have := hB y 0 ht0 q (hqU q hq)
    simpa only [cexp_zero_drift] using this
  choose B hBnn hB using hb
  obtain ⟨BH, hBH, hbH⟩ := lam_pow_bound_inv (t₁ := t₁) (q₁ := q₁) hc hδ hK hK₁ hdec hsep hlog j hj
  have hint : ∀ q ∈ U, Integrable (ψ 0 q) := by
    intro q hq
    refine ((integrable_inv_one_add_sq.const_mul ((2 * Real.pi)⁻¹ * m.factorial * BH *
      (c ^ m)⁻¹ * (1 + 1 / c ^ 2)))).mono' (hmeas 0 (Nat.zero_le _) q hq)
      (ae_of_all _ fun y => ?_)
    rw [hnorm]
    have h1 := hbH y 0 ht0 q (hqU q hq)
    simp only [cexp_zero_drift] at h1
    simp only [add_zero]
    have hr : c ≤ ‖(c : ℂ) + y * I‖ := norm_vline_ge_re c y
    have hr0 : 0 < ‖(c : ℂ) + y * I‖ := lt_of_lt_of_le hc hr
    have h2 : (‖(c : ℂ) + y * I‖ ^ m)⁻¹ ≤ (c ^ m)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hr _)
    have h3 := inv_norm_vline_sq_le hc y
    calc (2 * Real.pi)⁻¹ * ((m.factorial : ℝ) * (‖(c : ℂ) + y * I‖ ^ j *
          ‖cepsJetLam j (c + y * I) (cexp (-q) * T (c + y * I))‖) *
          (‖(c : ℂ) + y * I‖ ^ (m + 1))⁻¹)
        ≤ (2 * Real.pi)⁻¹ * ((m.factorial : ℝ) * (BH * ‖(c : ℂ) + y * I‖⁻¹) *
          (‖(c : ℂ) + y * I‖ ^ (m + 1))⁻¹) := by gcongr
      _ = (2 * Real.pi)⁻¹ * m.factorial * BH * (‖(c : ℂ) + y * I‖ ^ m)⁻¹ *
          (‖(c : ℂ) + y * I‖ ^ 2)⁻¹ := by field_simp; ring
      _ ≤ (2 * Real.pi)⁻¹ * m.factorial * BH * (c ^ m)⁻¹ *
          ((1 + 1 / c ^ 2) * (1 + y ^ 2)⁻¹) := by gcongr
      _ = _ := by ring
  have hderiv : ∀ k < n, ∀ y, ∀ q ∈ U, HasDerivAt (fun q => ψ k q y) (ψ (k + 1) q y) q := by
    intro k _ y q hq
    have h := hasDerivAt_cepsJetLam_disc (j + k) (c + y * I) (T (c + y * I)) q 0 (hslitq q hq y)
    simp only [cexp_zero_drift] at h
    have h2 := (((h.const_mul ((-1 : ℂ) ^ k)).const_mul (((c : ℂ) + y * I) ^ j)).const_mul
      (m.factorial : ℂ)).mul_const ((((c : ℂ) + y * I) ^ (m + 1))⁻¹) |>.const_mul
      (2 * Real.pi : ℂ)⁻¹
    refine h2.congr_deriv ?_
    simp only [hψ, pow_succ, ← add_assoc]
    ring
  have hbound : ∀ k < n, ∀ y, ∀ q ∈ U, ‖ψ (k + 1) q y‖ ≤
      (2 * Real.pi)⁻¹ * m.factorial * B k * (c ^ (m + 1))⁻¹ * (1 + y ^ 2)⁻¹ := by
    intro k _ y q hq
    rw [hnorm, ← add_assoc]
    have := hB k y q hq
    calc (2 * Real.pi)⁻¹ * ((m.factorial : ℝ) * (‖(c : ℂ) + y * I‖ ^ j *
          ‖cepsJetLam (j + k + 1) (c + y * I) (cexp (-q) * T (c + y * I))‖) *
          (‖(c : ℂ) + y * I‖ ^ (m + 1))⁻¹)
        ≤ (2 * Real.pi)⁻¹ * ((m.factorial : ℝ) * (B k * (1 + y ^ 2)⁻¹) * (c ^ (m + 1))⁻¹) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left this
            (by positivity)) (hinvp y) (by positivity) ?_) (by positivity)
          have := hBnn k; positivity
      _ = _ := by ring
  have key := iteratedDeriv_integral_of_dominated (𝕜 := ℂ) (μ := volume) (φ := ψ)
    (B := fun k y => (2 * Real.pi)⁻¹ * m.factorial * B k * (c ^ (m + 1))⁻¹ * (1 + y ^ 2)⁻¹)
    (N := n) isOpen_ball hmeas hint hderiv hbound
    (fun k _ => integrable_inv_one_add_sq.const_mul _) 0 h0U
  -- the function near `0`
  have hev : (fun q : ℂ => iteratedDeriv m (fun ζ : ℂ =>
      iteratedDeriv j (fun t : ℝ => cepsRootFreeL c T t q ζ) 0) 0) =ᶠ[𝓝 0]
      fun q => (∫ y, ψ 0 q y) + corr := by
    filter_upwards [isOpen_ball.mem_nhds h0U] with q hq
    rw [iteratedDeriv_spatial_cepsRootFreeL hc hδ hK hK₁ ht₁ hTc hdec hsep hslit hlog j m hj
      (hqU q hq)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hψ, pow_zero, one_mul, add_zero]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_add_const_fun, key, cepsContourJetC, cepsJetCorr]
  have hI : ∫ y, ψ n 0 y = (m.factorial : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      ∫ y : ℝ, cepsJetIntegrand j m n (c + y * I) (T (c + y * I)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hψ, neg_zero, Complex.exp_zero, one_mul, cepsJetIntegrand_eq_lam, div_eq_mul_inv]
    ring
  rw [hI]
  congr 1
  rcases n with _ | n
  · simp [hcorr]
  · simp only [if_neg (Nat.succ_ne_zero n)]
    rw [if_neg (by omega)]

end Steps

end PGM
