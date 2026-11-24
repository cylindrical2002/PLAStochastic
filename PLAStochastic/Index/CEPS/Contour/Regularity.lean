import PLAStochastic.Index.CEPS.Contour.Shift
import PLAStochastic.Index.CEPS.Canonical.TransportSobolev
import PLAStochastic.Index.CEPS.Canonical.MixedBounds

/-!
# X9: C-3(c) and C-4 for `dom.canonL` on a smaller line

WP3 proves drift regularity (C-3(c)) and the transport identity (C-4) for the line integral on
`Re s = c ∈ [c₀, 2c₀]` under `f_W ∈ CepsSobolevClass m η` with `2 c₀ ≤ η`. Here the line is moved
to any `σ ∈ (0, c₀]` with `2 σ ≤ η`: WP3 applies to `dom.shrink σ` (whose line scale is `σ`),
and by abscissa independence (`Contour.Shift`) its line integral is `dom.canonL` on the open
range `|t| < μ₀'`, `‖q‖ < q₀'`, `Re ζ < σ` of the shrunk domain. Derivatives only depend on germs,
so every statement transfers to `dom.canonL` itself:

* `iteratedDeriv_canonL_mu_shrink`, `contDiffOn_canonL_mu_shrink` (`C^{m-2}` in the real drift);
* `norm_iteratedDeriv_canonL_mu_le_shrink`, `norm_iteratedDeriv_canonL_mu_le_uniform_shrink`
  (jet bounds), `norm_mixed_canonL_le_shrink` (mixed `μ, ζ, q` bounds);
* `canonL_transport_shrink` (C-4) and `hasDerivAt_canonR_mu_shrink` (remainder form).

`μ₀'`, `q₀'` stand for `(dom.shrink σ hσ hσc).μ₀`, `.q₀` and are written out in the statements.
-/

noncomputable section

open MeasureTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

namespace CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

/-! ### Germs of `dom.canonL` near the range of the shrunk domain -/

/-- On the range of `dom.shrink σ`, `dom.canonL` is the line integral on `Re s = σ`. -/
theorem canonL_eq_line_of_shrink {t : ℝ} (ht : |t| ≤ (dom.shrink σ hσ hσc).μ₀) {q : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) {ζ : ℂ} (hζ : ζ.re < σ) :
    dom.canonL ρW t q ζ = cepsCanonL D θ ρW 1 σ t q ζ :=
  (dom.shrink_canonL_eq hW hθ hD hσ hσc ht hq hζ).symm

theorem canonL_mu_eventuallyEq_shrink {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) {ζ : ℂ}
    (hζ : ζ.re < σ) {t : ℝ} (ht : |t| < (dom.shrink σ hσ hσc).μ₀) :
    (fun t' : ℝ => dom.canonL ρW t' q ζ) =ᶠ[𝓝 t]
      fun t' : ℝ => cepsCanonL D θ ρW 1 σ t' q ζ :=
  Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds ht)
    fun _ ht' => dom.canonL_eq_line_of_shrink hW hθ hD hσ hσc (le_of_lt ht') hq hζ

theorem canonL_q_eventuallyEq_shrink {t : ℝ} (ht : |t| ≤ (dom.shrink σ hσ hσc).μ₀) {ζ : ℂ}
    (hζ : ζ.re < σ) {q : ℂ} (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀) :
    (fun q' : ℂ => dom.canonL ρW t q' ζ) =ᶠ[𝓝 q]
      fun q' : ℂ => cepsCanonL D θ ρW 1 σ t q' ζ :=
  Filter.eventually_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hq)
    fun _ hq' => dom.canonL_eq_line_of_shrink hW hθ hD hσ hσc ht (le_of_lt hq') hζ

theorem canonL_zeta_eventuallyEq_shrink {t : ℝ} (ht : |t| ≤ (dom.shrink σ hσ hσc).μ₀) {q : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) {ζ : ℂ} (hζ : ζ.re < σ) :
    (fun ζ' : ℂ => dom.canonL ρW t q ζ') =ᶠ[𝓝 ζ]
      fun ζ' : ℂ => cepsCanonL D θ ρW 1 σ t q ζ' :=
  Filter.eventually_of_mem ((isOpen_lt continuous_re continuous_const).mem_nhds hζ)
    fun _ hζ' => dom.canonL_eq_line_of_shrink hW hθ hD hσ hσc ht hq hζ'

/-! ### C-3(c) -/

/-- **Higher drift derivatives on the line `σ`.** -/
theorem iteratedDeriv_canonL_mu_shrink {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hση : 2 * σ ≤ η) {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀ / 2) {ζ : ℂ}
    (hζ : ζ.re < σ) {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.shrink σ hσ hσc).μ₀ / 4) :
    iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t =
      cepsCanonLJet D θ ρW σ n t q ζ := by
  have hq0 := (dom.shrink σ hσ hσc).q₀_pos
  have hμ0 := (dom.shrink σ hσ hσc).μ₀_pos
  rw [(dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc (by linarith) hζ
    (by linarith)).iteratedDeriv_eq]
  exact (dom.shrink σ hσ hσc).iteratedDeriv_cepsCanonL_mu hW hθ hD hf hση (γ := 1)
    (by norm_num) le_rfl (c := σ) le_rfl (by rw [shrink_c₀]; linarith) hq hζ n hn t ht

/-- **C-3(c), regularity on the line `σ`.** `t ↦ dom.canonL ρW t q ζ` is `C^{m-2}` on
`(-μ₀'/4, μ₀'/4)`. -/
theorem contDiffOn_canonL_mu_shrink {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hση : 2 * σ ≤ η) {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀ / 2) {ζ : ℂ}
    (hζ : ζ.re < σ) :
    ContDiffOn ℝ (m - 2 : ℕ) (fun t' : ℝ => dom.canonL ρW t' q ζ)
      (Ioo (-((dom.shrink σ hσ hσc).μ₀ / 4)) ((dom.shrink σ hσ hσc).μ₀ / 4)) := by
  have hq0 := (dom.shrink σ hσ hσc).q₀_pos
  have hμ0 := (dom.shrink σ hσ hσc).μ₀_pos
  refine ((dom.shrink σ hσ hσc).contDiffOn_cepsCanonL_mu hW hθ hD hf hm hση (γ := 1)
    (by norm_num) le_rfl (c := σ) le_rfl (by rw [shrink_c₀]; linarith) hq hζ).congr ?_
  intro t ht
  exact dom.canonL_eq_line_of_shrink hW hθ hD hσ hσc
    (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]) (by linarith) hζ

/-- **C-3(c), jet bound on the line `σ`.** -/
theorem norm_iteratedDeriv_canonL_mu_le_shrink {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hση : 2 * σ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.shrink σ hσ hσc).μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re < σ) :
    ‖iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t‖ ≤
      (2 * Real.pi)⁻¹ * ((dom.shrink σ hσ hσc).jetC n * (cepsSobolev m η fW + 1)) *
        (Real.pi / σ + Real.pi / (σ - ζ.re)) := by
  rw [dom.iteratedDeriv_canonL_mu_shrink hW hθ hD hσ hσc hf hση hq hζ hn ht]
  exact (dom.shrink σ hσ hσc).norm_cepsCanonLJet_le hW hθ hD hf hση hn (c := σ) le_rfl
    (by rw [shrink_c₀]; linarith) ht.le hq hζ

/-- **C-3(c), uniform jet bound on the line `σ`.** For `Re ζ ≤ σ/2`:
`‖∂_μ^{n+1} L‖ ≤ 3 C_n (‖f_W‖_{m,η} + 1)/(2σ)`, `C_n` the jet constant of `dom.shrink σ`. -/
theorem norm_iteratedDeriv_canonL_mu_le_uniform_shrink {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hση : 2 * σ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.shrink σ hσ hσc).μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re ≤ σ / 2) :
    ‖iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t‖ ≤
      3 * ((dom.shrink σ hσ hσc).jetC n * (cepsSobolev m η fW + 1)) / (2 * σ) := by
  rw [dom.iteratedDeriv_canonL_mu_shrink hW hθ hD hσ hσc hf hση hq (by linarith) hn ht]
  exact (dom.shrink σ hσ hσc).norm_cepsCanonLJet_le_uniform hW hθ hD hf hση hn (c := σ) le_rfl
    (by rw [shrink_c₀]; linarith) ht.le hq hζ

/-- **C-3(c), mixed bounds on the line `σ`.** For `‖ζ₀‖ ≤ σ/4`, `‖q₁‖ ≤ q₀'/4`:
`‖∂_q^k ∂_ζ^l ∂_μ^{n+1} L(ζ₀; t, q₁)‖ ≤ k! (l! C/(σ/8)^l)/(q₀'/8)^k`,
`C = 3 C_n (‖f_W‖_{m,η} + 1)/(2σ)`. -/
theorem norm_mixed_canonL_le_shrink {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hση : 2 * σ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.shrink σ hσ hσc).μ₀ / 4) {ζ₀ q₁ : ℂ} (hζ₀ : ‖ζ₀‖ ≤ σ / 4)
    (hq₁ : ‖q₁‖ ≤ (dom.shrink σ hσ hσc).q₀ / 4) (l k : ℕ) :
    ‖iteratedDeriv k (fun q => iteratedDeriv l (fun ζ =>
        iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t) ζ₀) q₁‖ ≤
      k.factorial * (l.factorial * (3 * ((dom.shrink σ hσ hσc).jetC n *
        (cepsSobolev m η fW + 1)) / (2 * σ)) / (σ / 8) ^ l) /
          ((dom.shrink σ hσ hσc).q₀ / 8) ^ k := by
  have hq0 := (dom.shrink σ hσ hσc).q₀_pos
  have hμ0 := (dom.shrink σ hσ hσc).μ₀_pos
  have hζre : ζ₀.re < σ := by have := re_le_norm ζ₀; linarith
  have hopenζ : IsOpen {ζ : ℂ | ζ.re < σ} := isOpen_lt continuous_re continuous_const
  have hinner : ∀ q : ℂ, ‖q‖ < (dom.shrink σ hσ hσc).q₀ →
      iteratedDeriv l (fun ζ => iteratedDeriv (n + 1)
          (fun t' : ℝ => dom.canonL ρW t' q ζ) t) ζ₀ =
        iteratedDeriv l (fun ζ => iteratedDeriv (n + 1)
          (fun t' : ℝ => cepsCanonL D θ ρW 1 σ t' q ζ) t) ζ₀ := by
    intro q hq
    refine Filter.EventuallyEq.iteratedDeriv_eq l ?_
    exact Filter.eventually_of_mem (hopenζ.mem_nhds hζre) fun ζ hζ =>
      (dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc hq.le hζ
        (by linarith)).iteratedDeriv_eq (n + 1)
  have houter : (fun q => iteratedDeriv l (fun ζ => iteratedDeriv (n + 1)
      (fun t' : ℝ => dom.canonL ρW t' q ζ) t) ζ₀) =ᶠ[𝓝 q₁]
      fun q => iteratedDeriv l (fun ζ => iteratedDeriv (n + 1)
        (fun t' : ℝ => cepsCanonL D θ ρW 1 σ t' q ζ) t) ζ₀ := by
    refine Filter.eventually_of_mem
      (ball_mem_nhds q₁ (show (0 : ℝ) < (dom.shrink σ hσ hσc).q₀ / 4 by positivity))
      fun q hq => hinner q ?_
    rw [mem_ball, dist_eq_norm] at hq
    have := norm_sub_norm_le q q₁
    linarith
  rw [houter.iteratedDeriv_eq k]
  exact (dom.shrink σ hσ hσc).norm_mixed_cepsCanonL_le hW hθ hD hf hση (γ := 1) (by norm_num)
    le_rfl hn (c := σ) le_rfl (by rw [shrink_c₀]; linarith) ht hζ₀ hq₁ l k

/-! ### C-4 -/

/-- **C-4 on the line `σ`.** `∂_μ L(ζ) + ζ ∂_q L(ζ) = ∂_μ ℓ` for `dom.canonL`. -/
theorem canonL_transport_shrink {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m)
    (hση : 2 * σ ≤ η) {t : ℝ} (ht : |t| < (dom.shrink σ hσ hσc).μ₀ / 2) {q : ℂ}
    (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀ / 4) {ζ : ℂ} (hζ : ζ.re < σ) :
    deriv (fun t' : ℝ => dom.canonL ρW t' q ζ) t +
        ζ * deriv (fun q' : ℂ => dom.canonL ρW t q' ζ) q =
      deriv (fun t' : ℝ => dom.canonL ρW t' q 0) t := by
  have hq0 := (dom.shrink σ hσ hσc).q₀_pos
  have hμ0 := (dom.shrink σ hσ hσc).μ₀_pos
  have hn0 : (0 : ℂ).re < σ := by rw [zero_re]; exact hσ
  rw [(dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc (by linarith [norm_nonneg q]) hζ
      (by linarith)).deriv_eq,
    (dom.canonL_q_eventuallyEq_shrink hW hθ hD hσ hσc (by linarith) hζ
      (by linarith [norm_nonneg q])).deriv_eq,
    (dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc (by linarith [norm_nonneg q]) hn0
      (by linarith)).deriv_eq]
  exact (dom.shrink σ hσ hσc).cepsCanonL_transport_of_sobolev hW hθ hD hf hm hση (γ := 1)
    (by norm_num) le_rfl (c := σ) le_rfl (by rw [shrink_c₀]; linarith) ht hq hζ

/-- **C-4, remainder form on the line `σ`.** `∂_μ (L(ζ) - ℓ) = -ζ ∂_q L(ζ)` for `dom.canonL`. -/
theorem hasDerivAt_canonR_mu_shrink {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hση : 2 * σ ≤ η) {t : ℝ} (ht : |t| < (dom.shrink σ hσ hσc).μ₀ / 2) {q : ℂ}
    (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀ / 4) {ζ : ℂ} (hζ : ζ.re < σ) :
    HasDerivAt (fun t' : ℝ => dom.canonL ρW t' q ζ - dom.canonL ρW t' q 0)
      (-(ζ * deriv (fun q' : ℂ => dom.canonL ρW t q' ζ) q)) t := by
  have hq0 := (dom.shrink σ hσ hσc).q₀_pos
  have hμ0 := (dom.shrink σ hσ hσc).μ₀_pos
  have hn0 : (0 : ℂ).re < σ := by rw [zero_re]; exact hσ
  rw [(dom.canonL_q_eventuallyEq_shrink hW hθ hD hσ hσc (by linarith) hζ
      (by linarith [norm_nonneg q])).deriv_eq]
  refine ((dom.shrink σ hσ hσc).hasDerivAt_cepsCanonR_mu_of_sobolev hW hθ hD hf hm hση (γ := 1)
    (by norm_num) le_rfl (c := σ) le_rfl (by rw [shrink_c₀]; linarith) ht hq
    hζ).congr_of_eventuallyEq ?_
  have h1 := dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc (q := q)
    (by linarith [norm_nonneg q]) hζ (t := t) (by linarith)
  have h2 := dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc (q := q)
    (by linarith [norm_nonneg q]) hn0 (t := t) (by linarith)
  filter_upwards [h1, h2] with t' e1 e2
  rw [e1, e2]

end

end CepsCanonDomain

end PGM
