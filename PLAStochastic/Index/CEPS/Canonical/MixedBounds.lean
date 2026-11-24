import PLAStochastic.Index.CEPS.Canonical.MuRegularity
import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.LineIntegralHolo

/-!
# CEPS WP3, lemma C-3(c): mixed derivative bounds of the canonical factor

* `differentiableOn_G1_joint`, `differentiableOn_G2_joint`: `g₁, g₂` are jointly holomorphic in
  `(μ, q)` (for `g₂` through `differentiableOn_deriv_fst` applied to `S, P`);
* `differentiableOn_cepsLogFJet_q`: the drift jets of `log F` are holomorphic in `q`;
* `differentiableOn_cepsCanonLJet`: `(ζ, q) ↦ ∂_μ^{n+1} L(ζ; t, q)` is jointly holomorphic on
  `{Re ζ < c} × B(0, q₀/2)`;
* `norm_mixed_cepsCanonL_le` (**C-3(c), mixed bounds**): for `f_W ∈ CepsSobolevClass m η`,
  `n + 2 ≤ m`, `|t| < μ₀/4`, `‖ζ₀‖ ≤ c₀/4`, `‖q₁‖ ≤ q₀/4` and all `l, k`,
  `‖∂_q^k ∂_ζ^l ∂_μ^{n+1} L(ζ₀; t, q₁)‖ ≤ k! (l! C/(c₀/8)^l)/(q₀/8)^k`,
  `C = 3 C_n (‖f_W‖_{m,η} + 1)/(2 c₀)`;
* `norm_mixed_cepsCanonL_zero_le`: the same for `∂_q^k ∂_ζ^l L` (no drift derivative, no Sobolev
  hypothesis).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

theorem disc_facts {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {s : ℂ} (h2 : dom.c₀ ≤ |s.re|) {μ : ℂ}
    (hμ : μ ∈ ball (t : ℂ) (dom.epsL / ‖s‖)) : ‖μ‖ ≤ dom.μ₀ / 2 ∧ |μ.im| * |s.im| ≤ dom.η := by
  have hc0 := dom.c₀_pos
  have hμ0 := dom.μ₀_pos
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 (h2.trans (abs_re_le_norm s))
  rw [mem_ball, dist_eq_norm] at hμ
  have he1 : dom.epsL ≤ dom.η := min_le_left _ _
  have he2 : dom.epsL ≤ dom.μ₀ * dom.c₀ / 4 := min_le_right _ _
  have hs : dom.c₀ ≤ ‖s‖ := h2.trans (abs_re_le_norm s)
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

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `g₁` is jointly holomorphic in `(μ, q)` on `B(t, ε/|s|) × B(0, q₀/2)`. -/
theorem differentiableOn_G1_joint {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {s : ℂ}
    (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsG1 ρW x.1 x.2 s)
      (ball (t : ℂ) (dom.epsL / ‖s‖) ×ˢ ball (0 : ℂ) (dom.q₀ / 2)) := by
  rintro ⟨μ, q⟩ ⟨hμ, hq⟩
  obtain ⟨h1, h2'⟩ := dom.disc_facts ht h2 hμ
  rw [mem_ball, dist_zero_right] at hq
  have hq' : ‖q‖ ≤ dom.q₀ := by linarith [dom.q₀_pos]
  have hdd := dom.dd₀_pos hD
  have hd := dom.norm_cepsD_ge hW hθ hD (μ := μ) (q := q) (ζ := s)
    (by linarith [dom.μ₀_pos]) h2' hq' h2 h3
  have hd0 : cepsD ρW μ q s ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hd; unfold dd₀ at hdd; linarith
  have hA : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsA ρW x.1 x.2 s) (μ, q) := by
    unfold cepsA; fun_prop
  have hdA : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsD ρW x.1 x.2 s) (μ, q) := by
    simp only [cepsD_eq_one_sub_cepsA]; exact (differentiableAt_const _).sub hA
  have e : (fun x : ℂ × ℂ => cepsG1 ρW x.1 x.2 s) = fun x : ℂ × ℂ =>
      -(s * cepsA ρW x.1 x.2 s) * (cepsD ρW x.1 x.2 s)⁻¹ := by
    funext x; simp only [cepsG1, div_eq_mul_inv]
  rw [e]
  exact ((hA.const_mul s).neg.mul (hdA.inv hd0)).differentiableWithinAt

/-- `g₂` is jointly holomorphic in `(μ, q)` on `B(0, μ₀/2) × B(0, q₀/2)`. -/
theorem differentiableOn_G2_joint {s : ℂ} (h2 : dom.c₀ ≤ |s.re|) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsG2 D θ ρW x.1 x.2 s)
      (ball (0 : ℂ) (dom.μ₀ / 2) ×ˢ ball (0 : ℂ) (dom.q₀ / 2)) := by
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨hSd, hPd⟩ := differentiableOn_cepsRootSum_joint hW hθ hD
  have hSmu := differentiableOn_deriv_fst hV hSd
  have hPmu := differentiableOn_deriv_fst hV hPd
  rintro ⟨μ, q⟩ ⟨hμ, hq⟩
  rw [mem_ball, dist_zero_right] at hμ hq
  have hμ' : ‖μ‖ ≤ dom.μ₀ := by linarith [dom.μ₀_pos]
  have hq' : ‖q‖ ≤ dom.q₀ := by linarith [dom.q₀_pos]
  have hmem := dom.mem_SPRegion hW hθ hD hμ' hq'
  have hn := hV.mem_nhds hmem
  have hS : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsRootSum D θ ρW x.1 x.2) (μ, q) :=
    (hSd _ hmem).differentiableAt hn
  have hP : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsRootProd D θ ρW x.1 x.2) (μ, q) :=
    (hPd _ hmem).differentiableAt hn
  have hSm : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsSmu D θ ρW x.1 x.2) (μ, q) :=
    (hSmu _ hmem).differentiableAt hn
  have hPm : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsPmu D θ ρW x.1 x.2) (μ, q) :=
    (hPmu _ hmem).differentiableAt hn
  have hs : dom.c₀ ≤ ‖s‖ := h2.trans (abs_re_le_norm s)
  have hQne : cepsQuad D θ ρW μ q s ≠ 0 :=
    dom.cepsQuad_ne_zero hW hθ hD hμ' hq' (by linarith [dom.c₀_pos])
  have hQ : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsQuad D θ ρW x.1 x.2 s) (μ, q) := by
    have e : (fun x : ℂ × ℂ => cepsQuad D θ ρW x.1 x.2 s) = fun x =>
        s ^ 2 - cepsRootSum D θ ρW x.1 x.2 * s + cepsRootProd D θ ρW x.1 x.2 := by
      funext x; exact cepsQuad_eq_SP D θ ρW x.1 x.2 s
    rw [e]; exact ((differentiableAt_const _).sub (hS.mul_const s)).add hP
  have e : (fun x : ℂ × ℂ => cepsG2 D θ ρW x.1 x.2 s) = fun x : ℂ × ℂ =>
      (cepsSmu D θ ρW x.1 x.2 * s - cepsPmu D θ ρW x.1 x.2) * (cepsQuad D θ ρW x.1 x.2 s)⁻¹ := by
    funext x; simp only [cepsG2, div_eq_mul_inv]
  rw [e]
  exact (((hSm.mul_const s).sub hPm).mul (hQ.inv hQne)).differentiableWithinAt

/-- The drift jets of `log F` are holomorphic in `q`. -/
theorem differentiableOn_cepsLogFJet_q (n : ℕ) {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {s : ℂ}
    (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    DifferentiableOn ℂ (fun q => cepsLogFJet D θ ρW n t q s) (ball (0 : ℂ) (dom.q₀ / 2)) := by
  have hc0 := dom.c₀_pos
  have hμ0 := dom.μ₀_pos
  have he := dom.epsL_pos
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 (h2.trans (abs_re_le_norm s))
  have hU₁ : IsOpen (ball (t : ℂ) (dom.epsL / ‖s‖) ×ˢ ball (0 : ℂ) (dom.q₀ / 2)) :=
    isOpen_ball.prod isOpen_ball
  have hU₂ : IsOpen (ball (t : ℂ) (dom.μ₀ / 4) ×ˢ ball (0 : ℂ) (dom.q₀ / 2)) :=
    isOpen_ball.prod isOpen_ball
  have hsub₂ : ball (t : ℂ) (dom.μ₀ / 4) ×ˢ ball (0 : ℂ) (dom.q₀ / 2) ⊆
      ball (0 : ℂ) (dom.μ₀ / 2) ×ˢ ball (0 : ℂ) (dom.q₀ / 2) := by
    rintro ⟨μ, q⟩ ⟨hμ, hq⟩
    refine ⟨?_, hq⟩
    rw [mem_ball, dist_eq_norm] at hμ
    rw [mem_ball, dist_zero_right]
    have := norm_sub_norm_le μ (t : ℂ)
    rw [norm_real, Real.norm_eq_abs] at this
    linarith
  have hJ1 := differentiableOn_iteratedDeriv_fst hU₁
    (dom.differentiableOn_G1_joint hW hθ hD ht h2 h3) n
  have hJ2 := differentiableOn_iteratedDeriv_fst hU₂
    ((dom.differentiableOn_G2_joint hW hθ hD h2).mono hsub₂) n
  intro q hq
  have m1 : (((t : ℂ), q) : ℂ × ℂ) ∈ ball (t : ℂ) (dom.epsL / ‖s‖) ×ˢ ball (0 : ℂ) (dom.q₀ / 2) :=
    ⟨mem_ball_self (by positivity), hq⟩
  have m2 : (((t : ℂ), q) : ℂ × ℂ) ∈ ball (t : ℂ) (dom.μ₀ / 4) ×ˢ ball (0 : ℂ) (dom.q₀ / 2) :=
    ⟨mem_ball_self (by positivity), hq⟩
  exact ((differentiableAt_slice_snd hU₁ hJ1 m1).add
    (differentiableAt_slice_snd hU₂ hJ2 m2)).differentiableWithinAt

/-- Jet bound in the Sobolev class: `‖∂_μ^{n+1} log F(s)‖ ≤ C_n (‖f_W‖ + 1)/|s|`. -/
theorem norm_cepsLogFJet_le_sob {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ} (ht : |t| ≤ dom.μ₀ / 4) {q s : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 2) (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    ‖cepsLogFJet D θ ρW n t q s‖ ≤ dom.jetC n * (cepsSobolev m η fW + 1) / ‖s‖ := by
  have hc0 := dom.c₀_pos
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hc0 (h2.trans (abs_re_le_norm s))
  have hJ := dom.norm_cepsLogFJet_le hW hθ hD n ht hq h2 h3
  have hdec := norm_pow_mul_stepTransform_le hW hf (s := s) (by linarith) hn
  have hX : ‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ ≤ cepsSobolev m η fW / ‖s‖ := by
    rw [le_div_iff₀ hs0]
    calc ‖s‖ ^ (n + 1) * ‖stepTransform ρW s‖ * ‖s‖ = ‖s‖ ^ (n + 2) * ‖stepTransform ρW s‖ := by
          ring
      _ ≤ _ := hdec
  have hC := dom.jetC_nonneg hD n
  calc ‖cepsLogFJet D θ ρW n t q s‖ ≤ dom.jetC n * (cepsSobolev m η fW / ‖s‖ + 1 / ‖s‖) :=
        hJ.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    _ = dom.jetC n * (cepsSobolev m η fW + 1) / ‖s‖ := by field_simp

/-- **Joint holomorphy of `∂_μ^{n+1} L` in `(ζ, q)`.** -/
theorem differentiableOn_cepsCanonLJet {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 4) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonLJet D θ ρW c n t x.2 x.1)
      {x : ℂ × ℂ | x.1.re < c ∧ ‖x.2‖ < dom.q₀ / 2} := by
  have hc0 := dom.c₀_pos
  have hline : ∀ y : ℝ, dom.c₀ ≤ |((c : ℂ) + y * I).re| ∧ |((c : ℂ) + y * I).re| ≤ 2 * dom.c₀ := by
    intro y
    have hsre : ((c : ℂ) + y * I).re = c := by simp
    rw [hsre, abs_of_pos (by linarith)]
    exact ⟨hc1, hc2⟩
  set K := dom.jetC n * (cepsSobolev m η fW + 1) with hK
  have hmain := differentiableOn_lineIntegral_param (c := c) (R := dom.q₀ / 2)
    (G := fun (y : ℝ) (q : ℂ) => cepsLogFJet D θ ρW n t q (c + y * I))
    (B := fun y : ℝ => K / ‖(c : ℂ) + y * I‖)
    (fun y => dom.differentiableOn_cepsLogFJet_q hW hθ hD n ht.le (hline y).1 (hline y).2)
    (fun y q hq => by
      rw [mem_ball, dist_zero_right] at hq
      exact dom.norm_cepsLogFJet_le_sob hW hθ hD hf hη hn ht.le hq.le (hline y).1 (hline y).2)
    (fun q hq => by
      rw [mem_ball, dist_zero_right] at hq
      exact dom.aestronglyMeasurable_cepsLogFJet hW hθ hD hc1 hc2 hq.le n ht)
    (fun ζ hζ => by
      refine ((integrable_inv_mul_line (by linarith) hζ).norm.const_mul K).congr
        (Eventually.of_forall fun y => ?_)
      simp only
      rw [norm_inv, norm_mul, div_div, div_eq_mul_inv])
  intro x hx
  exact (hmain x hx).const_mul ((2 * Real.pi : ℂ)⁻¹)

/-- **C-3(c), mixed bounds for the jets.**
`‖∂_q^k ∂_ζ^l (∂_μ^{n+1} L)(ζ₀; t, q₁)‖ ≤ k! (l! C/(c₀/8)^l)/(q₀/8)^k`. -/
theorem norm_mixed_cepsCanonLJet_le {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {n : ℕ} (hn : n + 2 ≤ m) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 4) {ζ₀ q₁ : ℂ}
    (hζ₀ : ‖ζ₀‖ ≤ dom.c₀ / 4) (hq₁ : ‖q₁‖ ≤ dom.q₀ / 4) (l k : ℕ) :
    ‖iteratedDeriv k (fun q => iteratedDeriv l (fun ζ => cepsCanonLJet D θ ρW c n t q ζ) ζ₀) q₁‖ ≤
      k.factorial * (l.factorial * (3 * (dom.jetC n * (cepsSobolev m η fW + 1)) / (2 * dom.c₀)) /
        (dom.c₀ / 8) ^ l) / (dom.q₀ / 8) ^ k := by
  have hc0 := dom.c₀_pos
  have hq0 := dom.q₀_pos
  have hsub : ∀ x ∈ ball ζ₀ (dom.c₀ / 4) ×ˢ ball q₁ (dom.q₀ / 4),
      x.1.re ≤ dom.c₀ / 2 ∧ ‖x.2‖ < dom.q₀ / 2 := by
    rintro ⟨ζ, q⟩ ⟨hζ, hq⟩
    rw [mem_ball, dist_eq_norm] at hζ hq
    constructor
    · have := norm_sub_norm_le ζ ζ₀; have := re_le_norm ζ; simp only; linarith
    · have := norm_sub_norm_le q q₁; simp only; linarith
  have hG := (dom.differentiableOn_cepsCanonLJet hW hθ hD hf hη hn hc1 hc2 ht).mono
    (fun x hx => ⟨by have := (hsub x hx).1; linarith, (hsub x hx).2⟩)
  have h := norm_iteratedDeriv_iteratedDeriv_le
    (G := fun x : ℂ × ℂ => cepsCanonLJet D θ ρW c n t x.2 x.1) (by positivity) (by positivity) hG
    (fun x hx => dom.norm_cepsCanonLJet_le_uniform hW hθ hD hf hη hn hc1 hc2 ht.le
      (hsub x hx).2.le (hsub x hx).1) l k
  rw [show dom.c₀ / 4 / 2 = dom.c₀ / 8 by ring, show dom.q₀ / 4 / 2 = dom.q₀ / 8 by ring] at h
  exact h

/-- **C-3(c), mixed bounds.** For `f_W ∈ CepsSobolevClass m η`, `2 c₀ ≤ η`, `n + 2 ≤ m`,
real `|t| < μ₀/4`, `‖ζ₀‖ ≤ c₀/4`, `‖q₁‖ ≤ q₀/4`:
`‖∂_q^k ∂_ζ^l ∂_μ^{n+1} L(ζ₀; t, q₁)‖ ≤ k! (l! C/(c₀/8)^l)/(q₀/8)^k`,
`C = 3 C_n (‖f_W‖_{m,η} + 1)/(2 c₀)`. -/
theorem norm_mixed_cepsCanonL_le {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hη : 2 * dom.c₀ ≤ η) {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {n : ℕ} (hn : n + 2 ≤ m)
    {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 4)
    {ζ₀ q₁ : ℂ} (hζ₀ : ‖ζ₀‖ ≤ dom.c₀ / 4) (hq₁ : ‖q₁‖ ≤ dom.q₀ / 4) (l k : ℕ) :
    ‖iteratedDeriv k (fun q => iteratedDeriv l (fun ζ =>
        iteratedDeriv (n + 1) (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) t) ζ₀) q₁‖ ≤
      k.factorial * (l.factorial * (3 * (dom.jetC n * (cepsSobolev m η fW + 1)) / (2 * dom.c₀)) /
        (dom.c₀ / 8) ^ l) / (dom.q₀ / 8) ^ k := by
  have hc0 := dom.c₀_pos
  have hq0 := dom.q₀_pos
  have hζre : ζ₀.re < c := by have := re_le_norm ζ₀; linarith
  have hopenζ : IsOpen {ζ : ℂ | ζ.re < c} := isOpen_lt continuous_re continuous_const
  have hinner : ∀ q : ℂ, ‖q‖ ≤ dom.q₀ / 2 →
      iteratedDeriv l (fun ζ => iteratedDeriv (n + 1)
          (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) t) ζ₀ =
        iteratedDeriv l (fun ζ => cepsCanonLJet D θ ρW c n t q ζ) ζ₀ := by
    intro q hq
    refine Filter.EventuallyEq.iteratedDeriv_eq l ?_
    exact Filter.eventually_of_mem (hopenζ.mem_nhds hζre) fun ζ hζ =>
      dom.iteratedDeriv_cepsCanonL_mu hW hθ hD hf hη hγ1 hγ2 hc1 hc2 hq hζ n hn t ht
  have houter : (fun q => iteratedDeriv l (fun ζ => iteratedDeriv (n + 1)
      (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) t) ζ₀) =ᶠ[𝓝 q₁]
      fun q => iteratedDeriv l (fun ζ => cepsCanonLJet D θ ρW c n t q ζ) ζ₀ := by
    refine Filter.eventually_of_mem (ball_mem_nhds q₁ (show (0 : ℝ) < dom.q₀ / 4 by positivity))
      fun q hq => hinner q ?_
    rw [mem_ball, dist_eq_norm] at hq
    have := norm_sub_norm_le q q₁
    linarith
  rw [houter.iteratedDeriv_eq k]
  exact dom.norm_mixed_cepsCanonLJet_le hW hθ hD hf hη hn hc1 hc2 ht hζ₀ hq₁ l k

/-- **Mixed bounds for `L` itself.** For real `|t| ≤ μ₀`, `‖ζ₀‖ ≤ c₀/4`, `‖q₁‖ ≤ q₀/2`:
`‖∂_q^k ∂_ζ^l L(ζ₀; t, q₁)‖ ≤ k! (l! C₀/(c₀/8)^l)/(q₀/4)^k` with `C₀` the bound of
`norm_cepsCanonL_le`. -/
theorem norm_mixed_cepsCanonL_zero_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| ≤ dom.μ₀) {ζ₀ q₁ : ℂ}
    (hζ₀ : ‖ζ₀‖ ≤ dom.c₀ / 4) (hq₁ : ‖q₁‖ ≤ dom.q₀ / 2) (l k : ℕ) :
    ‖iteratedDeriv k (fun q => iteratedDeriv l (fun ζ => cepsCanonL D θ ρW γ c t q ζ) ζ₀) q₁‖ ≤
      k.factorial * (l.factorial * (dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)) +
        (|Real.log (1 / 4)| + |Real.log 2| + Real.pi)) / (dom.c₀ / 8) ^ l) /
          (dom.q₀ / 4) ^ k := by
  have hc0 := dom.c₀_pos
  have hq0 := dom.q₀_pos
  have htμ : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rw [norm_real, Real.norm_eq_abs]; exact ht
  have hsub : ∀ x ∈ ball ζ₀ (dom.c₀ / 4) ×ˢ ball q₁ (dom.q₀ / 2),
      ‖x.1‖ < dom.c₀ / 2 ∧ ‖x.2‖ < dom.q₀ := by
    rintro ⟨ζ, q⟩ ⟨hζ, hq⟩
    rw [mem_ball, dist_eq_norm] at hζ hq
    constructor
    · have := norm_sub_norm_le ζ ζ₀; simp only; linarith
    · have := norm_sub_norm_le q q₁; simp only; linarith
  have hG := (dom.differentiableOn_cepsCanonL hW hθ hD hγ1 hγ2 hc1 hc2 htμ (by simp)).mono
    (fun x hx => ⟨by have := re_le_norm x.1; have := (hsub x hx).1; linarith, (hsub x hx).2⟩)
  have h := norm_iteratedDeriv_iteratedDeriv_le
    (G := fun x : ℂ × ℂ => cepsCanonL D θ ρW γ c (t : ℂ) x.2 x.1) (by positivity) (by positivity) hG
    (fun x hx => dom.norm_cepsCanonL_le hW hθ hD hγ1 hγ2 hc1 hc2 htμ (by simp)
      (hsub x hx).2.le (hsub x hx).1.le) l k
  rw [show dom.c₀ / 4 / 2 = dom.c₀ / 8 by ring, show dom.q₀ / 2 / 2 = dom.q₀ / 4 by ring] at h
  exact h

end

end CepsCanonDomain

end PGM
