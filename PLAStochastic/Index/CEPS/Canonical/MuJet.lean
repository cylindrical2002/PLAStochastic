import PLAStochastic.Index.CEPS.Canonical.TransportSobolev

/-!
# CEPS WP3, lemma C-3(c): drift jets of `log F` on the lines

On a line `Re s = c`, `∂_μ log F = g₁ + g₂` (`cepsDmuLogF_eq_G`) with

* `g₁ = ∂_μ log d = -s A/d` (`cepsG1`), holomorphic and bounded by `3/dd₀ · |s| |M₀(s)|` on the
  admissible drift disc `|μ - t| < ε/|s|` (`G1_disc`, `ε = epsL`);
* `g₂ = -∂_μ log D₀ = (S_μ s - P_μ)/D₀` (`cepsG2`), holomorphic and bounded by
  `4 c₀/μ₀ · |s|⁻¹` on the fixed disc `|μ - t| < μ₀/4` (`G2_disc`).

The jets `∂_μ^{n+1} log F(s; t, q) = ∂_μ^n g₁ + ∂_μ^n g₂` at real drift `t` (`cepsLogFJet`)
satisfy, by Cauchy estimates,

  `‖∂_μ^{n+1} log F(s)‖ ≤ C_n (|s|^{n+1} |M₀(s)| + |s|⁻¹)`   (`norm_cepsLogFJet_le`),

they differentiate in the real drift (`hasDerivAt_cepsLogFJet`), and they are measurable along
the line (`aestronglyMeasurable_cepsLogFJet`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `g₁ = ∂_μ log d = -s A/d`. -/
def cepsG1 (ρW : Measure ℝ) (μ q s : ℂ) : ℂ := -(s * cepsA ρW μ q s) / cepsD ρW μ q s

/-- `g₂ = -∂_μ log D₀ = (S_μ s - P_μ)/D₀`. -/
def cepsG2 (D θ : ℝ) (ρW : Measure ℝ) (μ q s : ℂ) : ℂ :=
  (cepsSmu D θ ρW μ q * s - cepsPmu D θ ρW μ q) / cepsQuad D θ ρW μ q s

theorem cepsDmuLogF_eq_G (D θ : ℝ) (ρW : Measure ℝ) (μ q s : ℂ) :
    cepsDmuLogF D θ ρW μ q s = cepsG1 ρW μ q s + cepsG2 D θ ρW μ q s := rfl

/-- The drift jets `∂_μ^{n+1} log F(s; t, q)` at real drift `t`, as `∂_μ^n g₁ + ∂_μ^n g₂`. -/
def cepsLogFJet (D θ : ℝ) (ρW : Measure ℝ) (n : ℕ) (t : ℝ) (q s : ℂ) : ℂ :=
  iteratedDeriv n (fun μ => cepsG1 ρW μ q s) (t : ℂ) +
    iteratedDeriv n (fun μ => cepsG2 D θ ρW μ q s) (t : ℂ)

theorem cepsLogFJet_zero (D θ : ℝ) (ρW : Measure ℝ) (t : ℝ) (q s : ℂ) :
    cepsLogFJet D θ ρW 0 t q s = cepsDmuLogF D θ ρW t q s := by
  simp only [cepsLogFJet, iteratedDeriv_zero, cepsDmuLogF_eq_G]

/-- Iterated derivatives of a function holomorphic on an open set are holomorphic there. -/
theorem differentiableOn_iteratedDeriv_of_isOpen {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
  rw [iteratedDeriv_eq_iterate]
  exact ((hf.analyticOnNhd hU).iterated_deriv n).differentiableOn

/-- Real-variable derivative of a complex jet at a real point. -/
theorem hasDerivAt_iteratedDeriv_ofReal {f : ℂ → ℂ} {t r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (t : ℂ) r)) (n : ℕ) :
    HasDerivAt (fun t' : ℝ => iteratedDeriv n f (t' : ℂ)) (iteratedDeriv (n + 1) f (t : ℂ)) t := by
  have h := (differentiableOn_iteratedDeriv_of_isOpen hf isOpen_ball n) t (mem_ball_self hr)
  have h2 := (h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  rw [← iteratedDeriv_succ] at h2
  exact h2.comp_ofReal

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

/-- `ε = min η (μ₀ c₀/4)`: the admissible drift discs are `|μ - t| < ε/|s|`. -/
def epsL : ℝ := min dom.η (dom.μ₀ * dom.c₀ / 4)

theorem epsL_pos : 0 < dom.epsL :=
  lt_min dom.η_pos (by have := dom.μ₀_pos; have := dom.c₀_pos; positivity)

/-- The jet constant `C_n = n! (3/dd₀ (2/ε)ⁿ + 4 c₀/μ₀ (8/μ₀)ⁿ)`. -/
def jetC (n : ℕ) : ℝ :=
  n.factorial * (3 / dom.dd₀ * (2 / dom.epsL) ^ n + 4 * dom.c₀ / dom.μ₀ * (8 / dom.μ₀) ^ n)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

omit hW hθ in
theorem jetC_nonneg (n : ℕ) : 0 ≤ dom.jetC n := by
  have := dom.dd₀_pos hD
  have := dom.epsL_pos
  have := dom.μ₀_pos
  have := dom.c₀_pos
  unfold jetC
  positivity

/-- `g₁` on the admissible disc `|μ - t| < ε/|s|`. -/
theorem G1_disc {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q s : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    DifferentiableOn ℂ (fun μ => cepsG1 ρW μ q s) (ball (t : ℂ) (dom.epsL / ‖s‖)) ∧
      ∀ μ ∈ ball (t : ℂ) (dom.epsL / ‖s‖),
        ‖cepsG1 ρW μ q s‖ ≤ 3 / dom.dd₀ * (‖s‖ * ‖stepTransform ρW s‖) := by
  have hc0 := dom.c₀_pos
  have hμ0 := dom.μ₀_pos
  have hs : dom.c₀ ≤ ‖s‖ := h2.trans (abs_re_le_norm s)
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 hs
  have hdd := dom.dd₀_pos hD
  have hfacts : ∀ μ ∈ ball (t : ℂ) (dom.epsL / ‖s‖),
      ‖μ‖ ≤ dom.μ₀ / 2 ∧ |μ.im| * |s.im| ≤ dom.η := by
    intro μ hμ
    rw [mem_ball, dist_eq_norm] at hμ
    have he1 : dom.epsL ≤ dom.η := min_le_left _ _
    have he2 : dom.epsL ≤ dom.μ₀ * dom.c₀ / 4 := min_le_right _ _
    have hr : dom.epsL / ‖s‖ ≤ dom.μ₀ / 4 := by
      rw [div_le_iff₀ hs0]
      calc dom.epsL ≤ dom.μ₀ * dom.c₀ / 4 := he2
        _ ≤ dom.μ₀ * ‖s‖ / 4 := by gcongr
        _ = dom.μ₀ / 4 * ‖s‖ := by ring
    constructor
    · have := norm_sub_norm_le μ (t : ℂ)
      rw [norm_real, Real.norm_eq_abs] at this
      linarith
    · have him : |μ.im| ≤ dom.epsL / ‖s‖ := by
        have e : μ.im = (μ - t).im := by simp
        rw [e]
        exact (abs_im_le_norm _).trans hμ.le
      calc |μ.im| * |s.im| ≤ dom.epsL / ‖s‖ * ‖s‖ :=
            mul_le_mul him (abs_im_le_norm s) (abs_nonneg _)
              (div_nonneg dom.epsL_pos.le (norm_nonneg _))
        _ = dom.epsL := by field_simp
        _ ≤ dom.η := he1
  have hq' : ‖q‖ ≤ dom.q₀ := by have := dom.q₀_pos; linarith
  have hdne : ∀ μ ∈ ball (t : ℂ) (dom.epsL / ‖s‖), dom.dd₀ ≤ ‖cepsD ρW μ q s‖ := by
    intro μ hμ
    obtain ⟨h1, h2'⟩ := hfacts μ hμ
    exact dom.norm_cepsD_ge hW hθ hD (by linarith) h2' hq' h2 h3
  constructor
  · intro μ hμ
    have hd0 : cepsD ρW μ q s ≠ 0 := by
      intro h0; have := hdne μ hμ; rw [h0, norm_zero] at this; linarith
    have hA : DifferentiableAt ℂ (fun μ => cepsA ρW μ q s) μ := by unfold cepsA; fun_prop
    have hd : DifferentiableAt ℂ (fun μ => cepsD ρW μ q s) μ := by
      simp only [cepsD_eq_one_sub_cepsA]; exact (differentiableAt_const _).sub hA
    unfold cepsG1
    exact ((hA.const_mul s).neg.div hd hd0).differentiableWithinAt
  · intro μ hμ
    obtain ⟨h1, h2'⟩ := hfacts μ hμ
    have hA := dom.norm_cepsA_le_three_mul (ρW := ρW) (by linarith) h2' hq' h3
    have hd := hdne μ hμ
    have hd0 : 0 < ‖cepsD ρW μ q s‖ := lt_of_lt_of_le hdd hd
    rw [cepsG1, norm_div, norm_neg, norm_mul, div_le_iff₀ hd0]
    calc ‖s‖ * ‖cepsA ρW μ q s‖ ≤ ‖s‖ * (3 * ‖stepTransform ρW s‖) := by gcongr
      _ = 3 / dom.dd₀ * (‖s‖ * ‖stepTransform ρW s‖) * dom.dd₀ := by field_simp
      _ ≤ 3 / dom.dd₀ * (‖s‖ * ‖stepTransform ρW s‖) * ‖cepsD ρW μ q s‖ := by gcongr

/-- Pointwise bound for `g₂`. -/
theorem norm_cepsG2_le {μ q s : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 2) (hq : ‖q‖ ≤ dom.q₀ / 2)
    (h2 : dom.c₀ ≤ |s.re|) :
    ‖cepsG2 D θ ρW μ q s‖ ≤ 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) := by
  have hμ0 := dom.μ₀_pos
  have hc0 := dom.c₀_pos
  have hμ' : ‖μ‖ ≤ dom.μ₀ := by linarith
  have hq' : ‖q‖ ≤ dom.q₀ := by have := dom.q₀_pos; linarith
  obtain ⟨b1, b2, -, -⟩ := dom.norm_SP_derivs_le hW hθ hD hμ hq
  have hs : dom.c₀ ≤ ‖s‖ := h2.trans (abs_re_le_norm s)
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 hs
  have hp := dom.norm_rootPlus_le hW hθ hD hμ' hq'
  have hm := dom.norm_rootMinus_le hW hθ hD hμ' hq'
  have hQ : 9 * ‖s‖ ^ 2 / 16 ≤ ‖cepsQuad D θ ρW μ q s‖ := by
    rw [cepsQuad, norm_mul]
    have e1 : 3 * ‖s‖ / 4 ≤ ‖s - cepsRootPlus D θ ρW μ q‖ := by
      have := norm_sub_norm_le s (cepsRootPlus D θ ρW μ q); linarith
    have e2 : 3 * ‖s‖ / 4 ≤ ‖s - cepsRootMinus D θ ρW μ q‖ := by
      have := norm_sub_norm_le s (cepsRootMinus D θ ρW μ q); linarith
    calc 9 * ‖s‖ ^ 2 / 16 = (3 * ‖s‖ / 4) * (3 * ‖s‖ / 4) := by ring
      _ ≤ _ := mul_le_mul e1 e2 (by positivity) (norm_nonneg _)
  have hQ0 : 0 < ‖cepsQuad D θ ρW μ q s‖ := lt_of_lt_of_le (by positivity) hQ
  rw [cepsG2, norm_div, div_le_iff₀ hQ0]
  set CX := 2 * dom.c₀ / dom.μ₀
  set CY := dom.c₀ ^ 2 / (4 * dom.μ₀)
  have hCY : 0 ≤ CY := by positivity
  calc ‖cepsSmu D θ ρW μ q * s - cepsPmu D θ ρW μ q‖ ≤ CX * ‖s‖ + CY := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]; gcongr
    _ ≤ 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) * (9 * ‖s‖ ^ 2 / 16) := by
        have : CY ≤ CY / dom.c₀ * ‖s‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
          exact mul_le_mul_of_nonneg_left hs hCY
        have e : 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) * (9 * ‖s‖ ^ 2 / 16) =
            16 / 9 * (CX + CY / dom.c₀) * (9 / 16) * ‖s‖ := by
          simp only [CX, CY]; field_simp; ring
        have e2 : 16 / 9 * (CX + CY / dom.c₀) * (9 / 16) * ‖s‖ = CX * ‖s‖ + CY / dom.c₀ * ‖s‖ := by
          ring
        rw [e, e2]; linarith
    _ ≤ 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) * ‖cepsQuad D θ ρW μ q s‖ := by gcongr

/-- `g₂` on the fixed disc `|μ - t| < μ₀/4`. -/
theorem G2_disc {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q s : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    (h2 : dom.c₀ ≤ |s.re|) :
    DifferentiableOn ℂ (fun μ => cepsG2 D θ ρW μ q s) (ball (t : ℂ) (dom.μ₀ / 4)) ∧
      ∀ μ ∈ ball (t : ℂ) (dom.μ₀ / 4), ‖cepsG2 D θ ρW μ q s‖ ≤ 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) := by
  have hμ0 := dom.μ₀_pos
  have hc0 := dom.c₀_pos
  have hq' : ‖q‖ ≤ dom.q₀ := by have := dom.q₀_pos; linarith
  have hs : dom.c₀ ≤ ‖s‖ := h2.trans (abs_re_le_norm s)
  have hball : ∀ μ ∈ ball (t : ℂ) (dom.μ₀ / 4), ‖μ‖ < dom.μ₀ / 2 := by
    intro μ hμ
    rw [mem_ball, dist_eq_norm] at hμ
    have := norm_sub_norm_le μ (t : ℂ)
    rw [norm_real, Real.norm_eq_abs] at this
    linarith
  -- the slice of `V` at `q` contains `B(0, μ₀)`
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨hSd, hPd⟩ := differentiableOn_cepsRootSum_joint hW hθ hD
  have slice : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableOn ℂ g (cepsSPRegion D θ ρW) →
      DifferentiableOn ℂ (fun μ' => g (μ', q)) (ball (0 : ℂ) dom.μ₀) := by
    intro g hg μ' hμ'
    rw [mem_ball, dist_zero_right] at hμ'
    have hmem := dom.mem_SPRegion hW hθ hD (q := q) hμ'.le hq'
    have := (hg _ hmem).differentiableAt (hV.mem_nhds hmem)
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun μ' : ℂ => ((μ', q) : ℂ × ℂ)) μ' this
      (differentiableAt_id.prodMk (differentiableAt_const _))).differentiableWithinAt
  have hS := slice (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSd
  have hP := slice (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPd
  have hSmu : DifferentiableOn ℂ (fun μ => cepsSmu D θ ρW μ q) (ball (0 : ℂ) dom.μ₀) :=
    hS.deriv isOpen_ball
  have hPmu : DifferentiableOn ℂ (fun μ => cepsPmu D θ ρW μ q) (ball (0 : ℂ) dom.μ₀) :=
    hP.deriv isOpen_ball
  constructor
  · intro μ hμ
    have hμ1 := hball μ hμ
    have hmem : μ ∈ ball (0 : ℂ) dom.μ₀ := by rw [mem_ball, dist_zero_right]; linarith
    have hn := isOpen_ball.mem_nhds hmem
    have hQne : cepsQuad D θ ρW μ q s ≠ 0 :=
      dom.cepsQuad_ne_zero hW hθ hD (by linarith) hq' (by linarith)
    have hQd : DifferentiableAt ℂ (fun μ => cepsQuad D θ ρW μ q s) μ := by
      have e : (fun μ => cepsQuad D θ ρW μ q s) = fun μ =>
          s ^ 2 - cepsRootSum D θ ρW μ q * s + cepsRootProd D θ ρW μ q := by
        funext μ; exact cepsQuad_eq_SP D θ ρW μ q s
      rw [e]
      exact ((differentiableAt_const _).sub (((hS μ hmem).differentiableAt hn).mul_const s)).add
        ((hP μ hmem).differentiableAt hn)
    unfold cepsG2
    exact (((((hSmu μ hmem).differentiableAt hn).mul_const s).sub
      ((hPmu μ hmem).differentiableAt hn)).div hQd hQne).differentiableWithinAt
  · intro μ hμ
    exact dom.norm_cepsG2_le hW hθ hD (hball μ hμ).le hq h2

/-- **Cauchy bound for the drift jets of `log F`.** -/
theorem norm_cepsLogFJet_le (n : ℕ) {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q s : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    ‖cepsLogFJet D θ ρW n t q s‖ ≤
      dom.jetC n * (‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ + 1 / ‖s‖) := by
  have hμ0 := dom.μ₀_pos
  have hc0 := dom.c₀_pos
  have he := dom.epsL_pos
  have hdd := dom.dd₀_pos hD
  have hs : dom.c₀ ≤ ‖s‖ := h2.trans (abs_re_le_norm s)
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 hs
  obtain ⟨d1, b1⟩ := dom.G1_disc hW hθ hD ht hq h2 h3
  obtain ⟨d2, b2⟩ := dom.G2_disc hW hθ hD ht hq h2
  have c1 := norm_iteratedDeriv_le_of_ball n (by positivity) d1 b1
  have c2 := norm_iteratedDeriv_le_of_ball n (by positivity) d2 b2
  have e1 : (n.factorial : ℝ) * (3 / dom.dd₀ * (‖s‖ * ‖stepTransform ρW s‖)) /
      (dom.epsL / ‖s‖ / 2) ^ n =
      n.factorial * (3 / dom.dd₀ * (2 / dom.epsL) ^ n) *
        (‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖) := by
    have h : dom.epsL / ‖s‖ / 2 = (2 / dom.epsL * ‖s‖)⁻¹ := by field_simp
    rw [h, inv_pow, div_inv_eq_mul, mul_pow, pow_succ]; ring
  have e2 : (n.factorial : ℝ) * (4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖)) / (dom.μ₀ / 4 / 2) ^ n =
      n.factorial * (4 * dom.c₀ / dom.μ₀ * (8 / dom.μ₀) ^ n) * (1 / ‖s‖) := by
    have h : dom.μ₀ / 4 / 2 = (8 / dom.μ₀)⁻¹ := by rw [inv_div]; ring
    rw [h, inv_pow, div_inv_eq_mul]; ring
  rw [e1] at c1
  rw [e2] at c2
  have hX : 0 ≤ ‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ := by positivity
  have hY : 0 ≤ 1 / ‖s‖ := by positivity
  have k1 : 0 ≤ (n.factorial : ℝ) * (3 / dom.dd₀ * (2 / dom.epsL) ^ n) := by positivity
  have k2 : 0 ≤ (n.factorial : ℝ) * (4 * dom.c₀ / dom.μ₀ * (8 / dom.μ₀) ^ n) := by positivity
  calc ‖cepsLogFJet D θ ρW n t q s‖
      ≤ ‖iteratedDeriv n (fun μ => cepsG1 ρW μ q s) (t : ℂ)‖ +
          ‖iteratedDeriv n (fun μ => cepsG2 D θ ρW μ q s) (t : ℂ)‖ := norm_add_le _ _
    _ ≤ n.factorial * (3 / dom.dd₀ * (2 / dom.epsL) ^ n) *
            (‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖) +
          n.factorial * (4 * dom.c₀ / dom.μ₀ * (8 / dom.μ₀) ^ n) * (1 / ‖s‖) := add_le_add c1 c2
    _ ≤ dom.jetC n * (‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ + 1 / ‖s‖) := by
        unfold jetC
        nlinarith [mul_nonneg k1 hY, mul_nonneg k2 hX]

/-- **Real-drift derivative of the jets.** -/
theorem hasDerivAt_cepsLogFJet (n : ℕ) {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q s : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    HasDerivAt (fun t' : ℝ => cepsLogFJet D θ ρW n t' q s) (cepsLogFJet D θ ρW (n + 1) t q s) t := by
  have hμ0 := dom.μ₀_pos
  have hc0 := dom.c₀_pos
  have he := dom.epsL_pos
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 (h2.trans (abs_re_le_norm s))
  obtain ⟨d1, -⟩ := dom.G1_disc hW hθ hD ht hq h2 h3
  obtain ⟨d2, -⟩ := dom.G2_disc hW hθ hD ht hq h2
  exact (hasDerivAt_iteratedDeriv_ofReal (by positivity) d1 n).add
    (hasDerivAt_iteratedDeriv_ofReal (by positivity) d2 n)

/-- **Measurability of the jets along a line.** -/
theorem aestronglyMeasurable_cepsLogFJet {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) (n : ℕ) {t : ℝ} (ht : |t| < dom.μ₀ / 4) :
    AEStronglyMeasurable (fun y : ℝ => cepsLogFJet D θ ρW n t q (c + y * I)) volume := by
  have hμ0 := dom.μ₀_pos
  have hc0 := dom.c₀_pos
  have he := dom.epsL_pos
  have hline : ∀ y : ℝ, dom.c₀ ≤ |((c : ℂ) + y * I).re| ∧ |((c : ℂ) + y * I).re| ≤ 2 * dom.c₀ := by
    intro y; simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
    rw [show c + (y * 0 - 0 * 1) = c by ring, abs_of_pos (by linarith)]
    exact ⟨hc1, hc2⟩
  have hq' : ‖q‖ ≤ dom.q₀ := by have := dom.q₀_pos; linarith
  -- base case: continuity of `g₂` and of `g₁ = ∂_μ log F - g₂`
  have base : ∀ t : ℝ, |t| < dom.μ₀ / 4 →
      Continuous (fun y : ℝ => cepsG1 ρW t q (c + y * I)) ∧
        Continuous (fun y : ℝ => cepsG2 D θ ρW t q (c + y * I)) := by
    intro t ht
    have htμ : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rw [norm_real, Real.norm_eq_abs]; linarith
    have hF := (dom.continuous_dLogF_line hW hθ hD hc1 hc2 htμ (by simp) hq').1
    have hs : Continuous fun y : ℝ => (c : ℂ) + y * I := by fun_prop
    have hQne : ∀ y : ℝ, cepsQuad D θ ρW t q (c + y * I) ≠ 0 := by
      intro y
      refine dom.cepsQuad_ne_zero hW hθ hD htμ hq' ?_
      have := (hline y).1.trans (abs_re_le_norm _); linarith
    have hQ : Continuous fun y : ℝ => cepsQuad D θ ρW t q (c + y * I) := by
      unfold cepsQuad
      exact (hs.sub continuous_const).mul (hs.sub continuous_const)
    have h2c : Continuous (fun y : ℝ => cepsG2 D θ ρW t q (c + y * I)) := by
      unfold cepsG2
      exact ((continuous_const.mul hs).sub continuous_const).div hQ hQne
    refine ⟨?_, h2c⟩
    have e : (fun y : ℝ => cepsG1 ρW t q (c + y * I)) = fun y : ℝ =>
        cepsDmuLogF D θ ρW t q (c + y * I) - cepsG2 D θ ρW t q (c + y * I) := by
      funext y; rw [cepsDmuLogF_eq_G]; ring
    rw [e]; exact hF.sub h2c
  -- induction on the order
  have key : ∀ n : ℕ, ∀ t : ℝ, |t| < dom.μ₀ / 4 →
      AEStronglyMeasurable (fun y : ℝ => iteratedDeriv n (fun μ => cepsG1 ρW μ q (c + y * I)) (t : ℂ))
          volume ∧
        AEStronglyMeasurable
          (fun y : ℝ => iteratedDeriv n (fun μ => cepsG2 D θ ρW μ q (c + y * I)) (t : ℂ)) volume := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simp only [iteratedDeriv_zero]
      exact ⟨(base t ht).1.aestronglyMeasurable, (base t ht).2.aestronglyMeasurable⟩
    | succ n ih =>
      intro t ht
      set ρ : ℝ := (dom.μ₀ / 4 - |t|) / 2 with hρ
      have hρ0 : 0 < ρ := by rw [hρ]; linarith
      obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ hρ0
      have hpt : ∀ k : ℕ, |t + ρ / (k + 1)| < dom.μ₀ / 4 := by
        intro k
        have h1 : ρ / (k + 1) ≤ ρ := div_le_self hρ0.le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
        have h0 : 0 ≤ ρ / (k + 1) := by positivity
        calc |t + ρ / (k + 1)| ≤ |t| + |ρ / (k + 1)| := abs_add_le _ _
          _ = |t| + ρ / (k + 1) := by rw [abs_of_nonneg h0]
          _ < dom.μ₀ / 4 := by rw [hρ] at h1 ⊢; linarith
      have hcast : ∀ k : ℕ, (t : ℂ) + ((ρ / (k + 1) : ℝ) : ℂ) = ((t + ρ / (k + 1) : ℝ) : ℂ) := by
        intro k; push_cast; ring
      have htle : |t| ≤ dom.μ₀ / 4 := ht.le
      constructor
      · simp only [iteratedDeriv_succ]
        refine aestronglyMeasurable_deriv_param (G := fun (y : ℝ) (μ : ℂ) =>
          iteratedDeriv n (fun μ => cepsG1 ρW μ q (c + y * I)) μ) hne hlim (fun k => ?_)
          (ih t ht).1 (fun y => ?_)
        · simp only [hcast]; exact (ih _ (hpt k)).1
        · obtain ⟨h2, h3⟩ := hline y
          have hs0 : 0 < ‖(c : ℂ) + y * I‖ := lt_of_lt_of_le hc0 (h2.trans (abs_re_le_norm _))
          obtain ⟨d1, -⟩ := dom.G1_disc hW hθ hD htle hq h2 h3
          exact (differentiableOn_iteratedDeriv_of_isOpen d1 isOpen_ball n _
            (mem_ball_self (by positivity))).differentiableAt
            (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
      · simp only [iteratedDeriv_succ]
        refine aestronglyMeasurable_deriv_param (G := fun (y : ℝ) (μ : ℂ) =>
          iteratedDeriv n (fun μ => cepsG2 D θ ρW μ q (c + y * I)) μ) hne hlim (fun k => ?_)
          (ih t ht).2 (fun y => ?_)
        · simp only [hcast]; exact (ih _ (hpt k)).2
        · obtain ⟨h2, -⟩ := hline y
          obtain ⟨d2, -⟩ := dom.G2_disc hW hθ hD htle hq h2
          exact (differentiableOn_iteratedDeriv_of_isOpen d2 isOpen_ball n _
            (mem_ball_self (by positivity))).differentiableAt
            (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  exact (key n t ht).1.add (key n t ht).2

end

end CepsCanonDomain

end PGM
