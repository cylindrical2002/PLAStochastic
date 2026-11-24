import PLAStochastic.Index.CEPS.Canonical.MuJet

/-!
# CEPS WP3, lemma C-3(c): drift regularity of the canonical factor

Let `f_W ∈ CepsSobolevClass m η` with `2 c₀ ≤ η`. On the line `Re s = c ∈ [c₀, 2 c₀]`, put

  `∂_μ^{n+1} L(ζ; t, q) := (2π)⁻¹ ∫ ∂_μ^{n+1} log F(c + i y; t, q) / (c + i y - ζ) dy`
  (`cepsCanonLJet`).

For real `|t| < μ₀/4`, `‖q‖ ≤ q₀/2`, `Re ζ < c`:

* `iteratedDeriv_cepsCanonL_mu`: for `n + 2 ≤ m`, the `(n+1)`-st real-drift derivative of
  `t ↦ L(ζ; t, q)` is `cepsCanonLJet … n t q ζ`;
* `contDiffOn_cepsCanonL_mu`: `t ↦ L(ζ; t, q)` is `C^{m-2}` on `(-μ₀/4, μ₀/4)` (blueprint:
  `‖f_W‖_{N+3} ≤ M ⇒ L ∈ C^{N+1}`);
* `norm_cepsCanonLJet_le`: `‖∂_μ^{n+1} L‖ ≤ (2π)⁻¹ C_n (‖f_W‖_{m,η} + 1) (π/c + π/(c - Re ζ))`,
  uniform in the step class, `t`, `q` and `ζ` with `Re ζ ≤ c₀/2`
  (`norm_cepsCanonLJet_le_uniform`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `∂_μ^{n+1} L(ζ; t, q)` as a line integral. -/
def cepsCanonLJet (D θ : ℝ) (ρW : Measure ℝ) (c : ℝ) (n : ℕ) (t : ℝ) (q ζ : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ y : ℝ, cepsLogFJet D θ ρW n t q (c + y * I) / ((c : ℂ) + y * I - ζ)

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- Integrable majorant of the jet integrands. -/
theorem norm_jet_div_le {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    {n : ℕ} (hn : n + 2 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {t : ℝ}
    (ht : |t| ≤ dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {ζ : ℂ} (hζ : ζ.re < c) (y : ℝ) :
    ‖cepsLogFJet D θ ρW n t q (c + y * I) / ((c : ℂ) + y * I - ζ)‖ ≤
      dom.jetC n * (cepsSobolev m η fW + 1) * ‖(((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹‖ := by
  set s : ℂ := (c : ℂ) + y * I with hsdef
  have hc0 := dom.c₀_pos
  have hsre : s.re = c := by simp [hsdef]
  have h2 : dom.c₀ ≤ |s.re| := by rw [hsre, abs_of_pos (by linarith)]; exact hc1
  have h3 : |s.re| ≤ 2 * dom.c₀ := by rw [hsre, abs_of_pos (by linarith)]; exact hc2
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 (h2.trans (abs_re_le_norm s))
  have hsζ : 0 < ‖s - ζ‖ := by
    have := re_le_norm (s - ζ); rw [sub_re, hsre] at this; linarith
  have hJ := dom.norm_cepsLogFJet_le hW hθ hD n ht hq h2 h3
  have hdec := norm_pow_mul_stepTransform_le hW hf (s := s) (by linarith) hn
  have hX : ‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ ≤ cepsSobolev m η fW / ‖s‖ := by
    rw [le_div_iff₀ hs0]
    calc ‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ * ‖s‖ = ‖s‖ ^ (n + 2) * ‖stepTransform ρW s‖ := by
          ring
      _ ≤ _ := hdec
  have hC := dom.jetC_nonneg hD n
  have hJ' : ‖cepsLogFJet D θ ρW n t q s‖ ≤
      dom.jetC n * (cepsSobolev m η fW / ‖s‖ + 1 / ‖s‖) :=
    hJ.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  rw [norm_div, norm_inv, norm_mul, div_le_iff₀ hsζ]
  calc ‖cepsLogFJet D θ ρW n t q s‖ ≤ dom.jetC n * (cepsSobolev m η fW / ‖s‖ + 1 / ‖s‖) := hJ'
    _ = dom.jetC n * (cepsSobolev m η fW + 1) * (‖s‖ * ‖s - ζ‖)⁻¹ * ‖s - ζ‖ := by
        field_simp

theorem aestronglyMeasurable_jet_div {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {q : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (n : ℕ) {t : ℝ} (ht : |t| < dom.μ₀ / 4) {ζ : ℂ} (hζ : ζ.re < c) :
    AEStronglyMeasurable
      (fun y : ℝ => cepsLogFJet D θ ρW n t q (c + y * I) / ((c : ℂ) + y * I - ζ)) volume := by
  have hinv : Continuous fun y : ℝ => ((c : ℂ) + y * I - ζ)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun y h0 => ?_
    have := congrArg re h0; simp at this; linarith
  have := (dom.aestronglyMeasurable_cepsLogFJet hW hθ hD hc1 hc2 hq n ht).mul
    hinv.aestronglyMeasurable
  convert this using 1
  funext y
  simp only [Pi.mul_apply, div_eq_mul_inv]

theorem integrable_jet_div {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re < c) :
    Integrable (fun y : ℝ => cepsLogFJet D θ ρW n t q (c + y * I) / ((c : ℂ) + y * I - ζ)) := by
  have hc0 := dom.c₀_pos
  exact (((integrable_inv_mul_line (by linarith) hζ).norm.const_mul
    (dom.jetC n * (cepsSobolev m η fW + 1)))).mono'
    (dom.aestronglyMeasurable_jet_div hW hθ hD hc1 hc2 hq n ht hζ)
    (Eventually.of_forall fun y => dom.norm_jet_div_le hW hθ hD hf hη hn hc1 hc2 ht.le hq hζ y)

/-- **Differentiation of the jets under the line integral.** -/
theorem hasDerivAt_cepsCanonLJet {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 3 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re < c) :
    HasDerivAt (fun t' : ℝ => cepsCanonLJet D θ ρW c n t' q ζ)
      (cepsCanonLJet D θ ρW c (n + 1) t q ζ) t := by
  have hc0 := dom.c₀_pos
  set δ : ℝ := (dom.μ₀ / 4 - |t|) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hball : ∀ t' ∈ Metric.ball t δ, |t'| < dom.μ₀ / 4 := by
    intro t' ht'
    rw [Metric.mem_ball, Real.dist_eq] at ht'
    have := abs_sub_abs_le_abs_sub t' t
    rw [hδ] at ht'; linarith
  have hn1 : n + 1 + 2 ≤ m := by omega
  have hn0 : n + 2 ≤ m := by omega
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (t' : ℝ) (y : ℝ) => cepsLogFJet D θ ρW n t' q (c + y * I) / ((c : ℂ) + y * I - ζ))
    (F' := fun (t' : ℝ) (y : ℝ) =>
      cepsLogFJet D θ ρW (n + 1) t' q (c + y * I) / ((c : ℂ) + y * I - ζ))
    (bound := fun y : ℝ => dom.jetC (n + 1) * (cepsSobolev m η fW + 1) *
      ‖(((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹‖)
    (x₀ := t) (s := Metric.ball t δ) (Metric.ball_mem_nhds t hδ0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds t hδ0) fun t' ht' =>
      dom.aestronglyMeasurable_jet_div hW hθ hD hc1 hc2 hq n (hball t' ht') hζ)
    (dom.integrable_jet_div hW hθ hD hf hη hn0 hc1 hc2 ht hq hζ)
    (dom.aestronglyMeasurable_jet_div hW hθ hD hc1 hc2 hq (n + 1) ht hζ)
    (Eventually.of_forall fun y t' ht' =>
      dom.norm_jet_div_le hW hθ hD hf hη hn1 hc1 hc2 (hball t' ht').le hq hζ y)
    ((integrable_inv_mul_line (by linarith) hζ).norm.const_mul _)
    (Eventually.of_forall fun y t' ht' => by
      have hsre : ((c : ℂ) + y * I).re = c := by simp
      exact (dom.hasDerivAt_cepsLogFJet hW hθ hD n (hball t' ht').le hq
        (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
        (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)).div_const _)
  unfold cepsCanonLJet
  exact hmain.2.const_mul _

/-- **First drift derivative of `L`** (Sobolev class, `m ≥ 2`). -/
theorem hasDerivAt_cepsCanonL_mu_jet {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η) {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 2) {q : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) {ζ : ℂ} (hζ : ζ.re < c) :
    HasDerivAt (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ)
      (cepsCanonLJet D θ ρW c 0 t q ζ) t := by
  have h := (dom.hasDerivAt_cepsCanonL_mu hW hθ hD hγ1 hγ2 hc1 hc2
    (dom.line_decay_of_sobolev hW hf hm hη hc1 hc2) ht hq hζ).2
  unfold cepsCanonLJet
  simp only [cepsLogFJet_zero]
  exact h

/-- **Higher drift derivatives of `L`.** For `n + 2 ≤ m` and `|t| < μ₀/4`,
`∂_μ^{n+1} L(ζ; t, q) = cepsCanonLJet … n t q ζ`. -/
theorem iteratedDeriv_cepsCanonL_mu {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {ζ : ℂ}
    (hζ : ζ.re < c) : ∀ n : ℕ, n + 2 ≤ m → ∀ t : ℝ, |t| < dom.μ₀ / 4 →
      iteratedDeriv (n + 1) (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) t =
        cepsCanonLJet D θ ρW c n t q ζ := by
  have hμ0 := dom.μ₀_pos
  have hopen : IsOpen {t : ℝ | |t| < dom.μ₀ / 4} := isOpen_lt continuous_abs continuous_const
  intro n
  induction n with
  | zero =>
    intro hm t ht
    rw [iteratedDeriv_one]
    exact (dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf (by omega) hη hγ1 hγ2 hc1 hc2
      (by linarith) hq hζ).deriv
  | succ n ih =>
    intro hm t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv (n + 1) (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) =ᶠ[𝓝 t]
        fun t' => cepsCanonLJet D θ ρW c n t' q ζ :=
      Filter.eventually_of_mem (hopen.mem_nhds ht) fun t' ht' => ih (by omega) t' ht'
    rw [hev.deriv_eq]
    exact (dom.hasDerivAt_cepsCanonLJet hW hθ hD hf hη (by omega) hc1 hc2 ht hq hζ).deriv

/-- **C-3(c), regularity.** `t ↦ L(ζ; t, q)` is `C^{m-2}` on `(-μ₀/4, μ₀/4)`. -/
theorem contDiffOn_cepsCanonL_mu {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m)
    (hη : 2 * dom.c₀ ≤ η) {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {ζ : ℂ}
    (hζ : ζ.re < c) :
    ContDiffOn ℝ (m - 2 : ℕ) (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ)
      (Ioo (-(dom.μ₀ / 4)) (dom.μ₀ / 4)) := by
  have hμ0 := dom.μ₀_pos
  have hI : IsOpen (Ioo (-(dom.μ₀ / 4)) (dom.μ₀ / 4)) := isOpen_Ioo
  have habs : ∀ t ∈ Ioo (-(dom.μ₀ / 4)) (dom.μ₀ / 4), |t| < dom.μ₀ / 4 := by
    intro t ht; rw [abs_lt]; exact ⟨ht.1, ht.2⟩
  have key : ∀ k : ℕ, k ≤ m - 2 → DifferentiableOn ℝ
      (iteratedDeriv k (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ))
      (Ioo (-(dom.μ₀ / 4)) (dom.μ₀ / 4)) := by
    intro k hk t ht
    have htt := habs t ht
    rcases k with _ | j
    · rw [iteratedDeriv_zero]
      exact (dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf hm hη hγ1 hγ2 hc1 hc2 (by linarith) hq
        hζ).differentiableAt.differentiableWithinAt
    · have hev : iteratedDeriv (j + 1) (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) =ᶠ[𝓝 t]
          fun t' => cepsCanonLJet D θ ρW c j t' q ζ :=
        Filter.eventually_of_mem (hI.mem_nhds ht) fun t' ht' =>
          dom.iteratedDeriv_cepsCanonL_mu hW hθ hD hf hη hγ1 hγ2 hc1 hc2 hq hζ j (by omega) t'
            (habs t' ht')
      exact ((dom.hasDerivAt_cepsCanonLJet hW hθ hD hf hη (by omega) hc1 hc2 htt hq
        hζ).differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt
  refine contDiffOn_of_differentiableOn_deriv fun k hk => ?_
  have hk' : k ≤ m - 2 := by exact_mod_cast hk
  exact (key k hk').congr fun t ht => iteratedDerivWithin_of_isOpen hI ht

/-- **C-3(c), bounds.** -/
theorem norm_cepsCanonLJet_le {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re < c) :
    ‖cepsCanonLJet D θ ρW c n t q ζ‖ ≤
      (2 * Real.pi)⁻¹ * (dom.jetC n * (cepsSobolev m η fW + 1)) *
        (Real.pi / c + Real.pi / (c - ζ.re)) := by
  have hc0 := dom.c₀_pos
  have hc : 0 < c := by linarith
  set K := dom.jetC n * (cepsSobolev m η fW + 1) with hK
  have hK0 : 0 ≤ K := mul_nonneg (dom.jetC_nonneg hD n)
    (by have := cepsSobolev_nonneg m η fW; linarith)
  obtain ⟨h1, e1⟩ := integral_inv_sq_add_sq (d := c) hc 0
  obtain ⟨h2, e2⟩ := integral_inv_sq_add_sq (d := c - ζ.re) (by linarith) ζ.im
  have hg : Integrable (fun y : ℝ => K * (((y - 0) ^ 2 + c ^ 2)⁻¹ +
      ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹)) := (h1.add h2).const_mul K
  have hint := norm_integral_le_of_norm_le hg (Eventually.of_forall fun y =>
    (dom.norm_jet_div_le hW hθ hD hf hη hn hc1 hc2 ht hq hζ y).trans
      (mul_le_mul_of_nonneg_left (norm_inv_mul_line_le hc hζ y) hK0))
  have hval : ∫ y : ℝ, K * (((y - 0) ^ 2 + c ^ 2)⁻¹ + ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹) =
      K * (Real.pi / c + Real.pi / (c - ζ.re)) := by
    rw [integral_const_mul, integral_add h1 h2, e1, e2]
  rw [hval] at hint
  unfold cepsCanonLJet
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_assoc]
  have h2pi : (2 * Real.pi)⁻¹ = (2 * |Real.pi|)⁻¹ := by rw [abs_of_pos Real.pi_pos]
  calc (2 * Real.pi)⁻¹ * ‖∫ y : ℝ, cepsLogFJet D θ ρW n t q (c + y * I) / ((c : ℂ) + y * I - ζ)‖
      ≤ (2 * Real.pi)⁻¹ * (K * (Real.pi / c + Real.pi / (c - ζ.re))) := by
        gcongr
    _ = _ := by ring

/-- **C-3(c), uniform bounds.** For `Re ζ ≤ c₀/2`:
`‖∂_μ^{n+1} L‖ ≤ 3 C_n (‖f_W‖_{m,η} + 1)/(2 c₀)`. -/
theorem norm_cepsCanonLJet_le_uniform {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re ≤ dom.c₀ / 2) :
    ‖cepsCanonLJet D θ ρW c n t q ζ‖ ≤
      3 * (dom.jetC n * (cepsSobolev m η fW + 1)) / (2 * dom.c₀) := by
  have hc0 := dom.c₀_pos
  have hK0 : 0 ≤ dom.jetC n * (cepsSobolev m η fW + 1) := mul_nonneg (dom.jetC_nonneg hD n)
    (by have := cepsSobolev_nonneg m η fW; linarith)
  have h := dom.norm_cepsCanonLJet_le hW hθ hD hf hη hn hc1 hc2 ht hq (by linarith)
  refine h.trans ?_
  have hb : Real.pi / c + Real.pi / (c - ζ.re) ≤ Real.pi / dom.c₀ + 2 * Real.pi / dom.c₀ := by
    have hp := Real.pi_pos
    have a1 : Real.pi / c ≤ Real.pi / dom.c₀ := div_le_div_of_nonneg_left hp.le hc0 hc1
    have a2 : Real.pi / (c - ζ.re) ≤ 2 * Real.pi / dom.c₀ := by
      rw [div_le_div_iff₀ (by linarith) hc0]; nlinarith
    linarith
  calc (2 * Real.pi)⁻¹ * (dom.jetC n * (cepsSobolev m η fW + 1)) *
        (Real.pi / c + Real.pi / (c - ζ.re))
      ≤ (2 * Real.pi)⁻¹ * (dom.jetC n * (cepsSobolev m η fW + 1)) *
          (Real.pi / dom.c₀ + 2 * Real.pi / dom.c₀) := by gcongr
    _ = 3 * (dom.jetC n * (cepsSobolev m η fW + 1)) / (2 * dom.c₀) := by
        field_simp; ring

end

end CepsCanonDomain

end PGM
