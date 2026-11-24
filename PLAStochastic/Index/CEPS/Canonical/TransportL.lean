import PLAStochastic.Index.CEPS.Canonical.TransportLog
import PLAStochastic.Index.CEPS.Canonical.LineKernel

/-!
# CEPS WP3, lemma C-4: the transport identity for the canonical factor

Under a line decay hypothesis `‖M₀(c + i y)‖ ≤ K/(1 + y²)` (supplied by the Sobolev class), the
canonical factor `L(ζ; μ, q)` (`cepsCanonL`, abscissa `c`, real drift `t`) is differentiable in
the real drift and in the discount, with

  `∂_μ L(ζ) + ζ ∂_q L(ζ) = ∂_μ L(0) = ∂_μ ℓ`   (`CepsCanonDomain.cepsCanonL_transport`).

Proof: differentiate under the line integral (explicit derivatives `cepsDmuLogF`, `cepsDqLogF`,
bounded through Cauchy estimates for `S, P` and the line separation of C-1), use the pointwise
identity `∂_μ log F + s ∂_q log F = S_q`, which reduces the left side minus the right side to
`(2π)⁻¹ S_q ζ ∫ ds/(s (s - ζ)) = 0` (`integral_inv_mul_line_eq_zero`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

/-- `dd₀ = min g (v₋ c₀²/32)`, the lower bound of `‖d‖` on the lines. -/
def dd₀ : ℝ := min dom.g (cepsVarLo D * dom.c₀ ^ 2 / 32)

theorem dd₀_pos (hD : 0 < D) : 0 < dom.dd₀ :=
  lt_min dom.g_pos (by have := cepsVarLo_pos hD; have := dom.c₀_pos; positivity)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem mem_SPRegion {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    (μ, q) ∈ cepsSPRegion D θ ρW :=
  ⟨dom.μ_lt_chart hμ, dom.sub_min_lt hW hθ hD hμ hq⟩

/-- Cauchy bounds for the first derivatives of `S` and `P`. -/
theorem norm_SP_derivs_le {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 2) (hq : ‖q‖ ≤ dom.q₀ / 2) :
    ‖cepsSmu D θ ρW μ q‖ ≤ 2 * dom.c₀ / dom.μ₀ ∧ ‖cepsPmu D θ ρW μ q‖ ≤ dom.c₀ ^ 2 / (4 * dom.μ₀) ∧
      ‖cepsSq D θ ρW μ q‖ ≤ 2 * dom.c₀ / dom.q₀ ∧
      ‖cepsPq D θ ρW μ q‖ ≤ dom.c₀ ^ 2 / (4 * dom.q₀) := by
  have hμ0 := dom.μ₀_pos
  have hq0 := dom.q₀_pos
  have hc0 := dom.c₀_pos
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨hSd, hPd⟩ := differentiableOn_cepsRootSum_joint hW hθ hD
  have hSbd : ∀ μ' q' : ℂ, ‖μ'‖ ≤ dom.μ₀ → ‖q'‖ ≤ dom.q₀ →
      ‖cepsRootSum D θ ρW μ' q'‖ ≤ dom.c₀ / 2 ∧ ‖cepsRootProd D θ ρW μ' q'‖ ≤ dom.c₀ ^ 2 / 16 := by
    intro μ' q' h1 h2
    have hp := dom.norm_rootPlus_le hW hθ hD h1 h2
    have hm := dom.norm_rootMinus_le hW hθ hD h1 h2
    constructor
    · calc ‖cepsRootSum D θ ρW μ' q'‖ ≤ ‖cepsRootPlus D θ ρW μ' q'‖ + ‖cepsRootMinus D θ ρW μ' q'‖ :=
            norm_add_le _ _
        _ ≤ dom.c₀ / 2 := by linarith
    · rw [cepsRootProd, norm_mul]
      calc ‖cepsRootPlus D θ ρW μ' q'‖ * ‖cepsRootMinus D θ ρW μ' q'‖ ≤ (dom.c₀ / 4) * (dom.c₀ / 4) :=
            mul_le_mul hp hm (norm_nonneg _) (by positivity)
        _ = dom.c₀ ^ 2 / 16 := by ring
  -- slices
  have sliceμ : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableOn ℂ g (cepsSPRegion D θ ρW) →
      DifferentiableOn ℂ (fun μ' => g (μ', q)) (ball μ (dom.μ₀ / 2)) := by
    intro g hg μ' hμ'
    rw [mem_ball, dist_eq_norm] at hμ'
    have h1 : ‖μ'‖ ≤ dom.μ₀ := by
      have := norm_sub_norm_le μ' μ; linarith
    have hmem := dom.mem_SPRegion hW hθ hD (q := q) h1 (by linarith)
    have := (hg _ hmem).differentiableAt (hV.mem_nhds hmem)
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun μ' : ℂ => ((μ', q) : ℂ × ℂ)) μ' this
      (differentiableAt_id.prodMk (differentiableAt_const _))).differentiableWithinAt
  have sliceq : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableOn ℂ g (cepsSPRegion D θ ρW) →
      DifferentiableOn ℂ (fun q' => g (μ, q')) (ball q (dom.q₀ / 2)) := by
    intro g hg q' hq'
    rw [mem_ball, dist_eq_norm] at hq'
    have h1 : ‖q'‖ ≤ dom.q₀ := by
      have := norm_sub_norm_le q' q; linarith
    have hmem := dom.mem_SPRegion hW hθ hD (μ := μ) (by linarith) h1
    have := (hg _ hmem).differentiableAt (hV.mem_nhds hmem)
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun q' : ℂ => ((μ, q') : ℂ × ℂ)) q' this
      ((differentiableAt_const _).prodMk differentiableAt_id)).differentiableWithinAt
  have cauchy : ∀ {f : ℂ → ℂ} {z : ℂ} {r M : ℝ}, 0 < r → DifferentiableOn ℂ f (ball z r) →
      (∀ w ∈ ball z r, ‖f w‖ ≤ M) → ‖deriv f z‖ ≤ 2 * M / r := by
    intro f z r M hr hf hb
    have := norm_iteratedDeriv_le_of_ball 1 hr hf hb
    rw [iteratedDeriv_one] at this
    calc ‖deriv f z‖ ≤ (Nat.factorial 1) * M / (r / 2) ^ 1 := this
      _ = 2 * M / r := by simp; field_simp
  have bμ : ∀ μ' ∈ ball μ (dom.μ₀ / 2), ‖μ'‖ ≤ dom.μ₀ := by
    intro μ' hμ'; rw [mem_ball, dist_eq_norm] at hμ'
    have := norm_sub_norm_le μ' μ; linarith
  have bq : ∀ q' ∈ ball q (dom.q₀ / 2), ‖q'‖ ≤ dom.q₀ := by
    intro q' hq'; rw [mem_ball, dist_eq_norm] at hq'
    have := norm_sub_norm_le q' q; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := cauchy (f := fun μ' => cepsRootSum D θ ρW μ' q) (by positivity)
      (sliceμ (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSd)
      (fun μ' hμ' => (hSbd μ' q (bμ μ' hμ') (by linarith)).1)
    calc _ ≤ 2 * (dom.c₀ / 2) / (dom.μ₀ / 2) := this
      _ = 2 * dom.c₀ / dom.μ₀ := by field_simp
  · have := cauchy (f := fun μ' => cepsRootProd D θ ρW μ' q) (by positivity)
      (sliceμ (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPd)
      (fun μ' hμ' => (hSbd μ' q (bμ μ' hμ') (by linarith)).2)
    calc _ ≤ 2 * (dom.c₀ ^ 2 / 16) / (dom.μ₀ / 2) := this
      _ = dom.c₀ ^ 2 / (4 * dom.μ₀) := by field_simp; ring
  · have := cauchy (f := fun q' => cepsRootSum D θ ρW μ q') (by positivity)
      (sliceq (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSd)
      (fun q' hq' => (hSbd μ q' (by linarith) (bq q' hq')).1)
    calc _ ≤ 2 * (dom.c₀ / 2) / (dom.q₀ / 2) := this
      _ = 2 * dom.c₀ / dom.q₀ := by field_simp
  · have := cauchy (f := fun q' => cepsRootProd D θ ρW μ q') (by positivity)
      (sliceq (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPd)
      (fun q' hq' => (hSbd μ q' (by linarith) (bq q' hq')).2)
    calc _ ≤ 2 * (dom.c₀ ^ 2 / 16) / (dom.q₀ / 2) := this
      _ = dom.c₀ ^ 2 / (4 * dom.q₀) := by field_simp; ring

/-- Pointwise bounds for the logarithmic derivatives on the lines. -/
theorem norm_dLogF_le {μ q s : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 2) (hμη : |μ.im| * |s.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀ / 2) (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    ‖cepsDmuLogF D θ ρW μ q s‖ ≤
        3 / dom.dd₀ * (‖s‖ * ‖stepTransform ρW s‖) + 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) ∧
      ‖cepsDqLogF D θ ρW μ q s‖ ≤
        3 / dom.dd₀ * ‖stepTransform ρW s‖ + 4 * dom.c₀ / dom.q₀ * (1 / ‖s‖) := by
  have hμ0 := dom.μ₀_pos
  have hq0 := dom.q₀_pos
  have hc0 := dom.c₀_pos
  have hμ' : ‖μ‖ ≤ dom.μ₀ := by linarith
  have hq' : ‖q‖ ≤ dom.q₀ := by linarith
  have hdd := dom.dd₀_pos hD
  have hdn := dom.norm_cepsD_ge hW hθ hD hμ' hμη hq' h2 h3
  have hA := dom.norm_cepsA_le_three_mul (ρW := ρW) hμ' hμη hq' h3
  obtain ⟨b1, b2, b3, b4⟩ := dom.norm_SP_derivs_le hW hθ hD hμ hq
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
  have hdd' : dom.dd₀ ≤ ‖cepsD ρW μ q s‖ := hdn
  have hd0 : 0 < ‖cepsD ρW μ q s‖ := lt_of_lt_of_le hdd hdd'
  have hAd : ‖cepsA ρW μ q s‖ / ‖cepsD ρW μ q s‖ ≤ 3 / dom.dd₀ * ‖stepTransform ρW s‖ := by
    rw [div_le_iff₀ hd0]
    calc ‖cepsA ρW μ q s‖ ≤ 3 * ‖stepTransform ρW s‖ := hA
      _ = 3 / dom.dd₀ * ‖stepTransform ρW s‖ * dom.dd₀ := by field_simp
      _ ≤ 3 / dom.dd₀ * ‖stepTransform ρW s‖ * ‖cepsD ρW μ q s‖ := by gcongr
  have hrat : ∀ {X Y : ℂ} {CX CY : ℝ}, ‖X‖ ≤ CX → ‖Y‖ ≤ CY →
      ‖(X * s - Y) / cepsQuad D θ ρW μ q s‖ ≤ 16 / 9 * (CX + CY / dom.c₀) * (1 / ‖s‖) := by
    intro X Y CX CY hX hY
    have hCX : 0 ≤ CX := (norm_nonneg _).trans hX
    have hCY : 0 ≤ CY := (norm_nonneg _).trans hY
    rw [norm_div, div_le_iff₀ hQ0]
    calc ‖X * s - Y‖ ≤ CX * ‖s‖ + CY := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]; gcongr
      _ ≤ 16 / 9 * (CX + CY / dom.c₀) * (1 / ‖s‖) * (9 * ‖s‖ ^ 2 / 16) := by
          have : CY ≤ CY / dom.c₀ * ‖s‖ := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
            exact mul_le_mul_of_nonneg_left hs hCY
          have e : 16 / 9 * (CX + CY / dom.c₀) * (1 / ‖s‖) * (9 * ‖s‖ ^ 2 / 16) =
              CX * ‖s‖ + CY / dom.c₀ * ‖s‖ := by field_simp
          rw [e]; linarith
      _ ≤ 16 / 9 * (CX + CY / dom.c₀) * (1 / ‖s‖) * ‖cepsQuad D θ ρW μ q s‖ := by
          gcongr
  constructor
  · unfold cepsDmuLogF
    have h1 := hrat (X := cepsSmu D θ ρW μ q) (Y := cepsPmu D θ ρW μ q) b1 b2
    have e : 16 / 9 * (2 * dom.c₀ / dom.μ₀ + dom.c₀ ^ 2 / (4 * dom.μ₀) / dom.c₀) =
        4 * dom.c₀ / dom.μ₀ := by field_simp; ring
    rw [e] at h1
    calc _ ≤ ‖-(s * cepsA ρW μ q s) / cepsD ρW μ q s‖ +
          ‖(cepsSmu D θ ρW μ q * s - cepsPmu D θ ρW μ q) / cepsQuad D θ ρW μ q s‖ := norm_add_le _ _
      _ ≤ ‖s‖ * (3 / dom.dd₀ * ‖stepTransform ρW s‖) + 4 * dom.c₀ / dom.μ₀ * (1 / ‖s‖) := by
          refine add_le_add ?_ h1
          rw [norm_div, norm_neg, norm_mul, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hAd (norm_nonneg _)
      _ = _ := by ring
  · unfold cepsDqLogF
    have h1 := hrat (X := cepsSq D θ ρW μ q) (Y := cepsPq D θ ρW μ q) b3 b4
    have e : 16 / 9 * (2 * dom.c₀ / dom.q₀ + dom.c₀ ^ 2 / (4 * dom.q₀) / dom.c₀) =
        4 * dom.c₀ / dom.q₀ := by field_simp; ring
    rw [e] at h1
    calc _ ≤ ‖cepsA ρW μ q s / cepsD ρW μ q s‖ +
          ‖(cepsSq D θ ρW μ q * s - cepsPq D θ ρW μ q) / cepsQuad D θ ρW μ q s‖ := norm_add_le _ _
      _ ≤ 3 / dom.dd₀ * ‖stepTransform ρW s‖ + 4 * dom.c₀ / dom.q₀ * (1 / ‖s‖) := by
          refine add_le_add ?_ h1
          rw [norm_div]; exact hAd


/-- Continuity in `y` of the logarithmic derivatives on a line (real drift). -/
theorem continuous_dLogF_line {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) :
    Continuous (fun y : ℝ => cepsDmuLogF D θ ρW μ q (c + y * I)) ∧
      Continuous (fun y : ℝ => cepsDqLogF D θ ρW μ q (c + y * I)) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hM := continuous_stepTransform_line hW hθ hD (c := c) (by rw [abs_of_pos (by linarith)]; linarith)
  have hs : Continuous fun y : ℝ => (c : ℂ) + y * I := by fun_prop
  have hA : Continuous fun y : ℝ => cepsA ρW μ q (c + y * I) := by
    unfold cepsA
    exact (continuous_const.mul ((continuous_const.mul hs).cexp)).mul hM
  have hdne : ∀ y : ℝ, cepsD ρW μ q (c + y * I) ≠ 0 := by
    intro y h0
    have := dom.norm_cepsD_ge hW hθ hD (ζ := (c : ℂ) + y * I) hμ
      (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq
      (by simp; rw [abs_of_pos (by linarith)]; exact hc1)
      (by simp; rw [abs_of_pos (by linarith)]; exact hc2)
    rw [h0, norm_zero] at this
    have := dom.dd₀_pos hD
    unfold dd₀ at this
    linarith
  have hQne : ∀ y : ℝ, cepsQuad D θ ρW μ q (c + y * I) ≠ 0 := by
    intro y
    refine dom.cepsQuad_ne_zero hW hθ hD hμ hq ?_
    have := re_le_norm ((c : ℂ) + y * I); simp at this; linarith
  have hd : Continuous fun y : ℝ => cepsD ρW μ q (c + y * I) := by
    have : (fun y : ℝ => cepsD ρW μ q (c + y * I)) = fun y : ℝ => 1 - cepsA ρW μ q (c + y * I) := by
      funext y; rfl
    rw [this]; exact continuous_const.sub hA
  have hQ : Continuous fun y : ℝ => cepsQuad D θ ρW μ q (c + y * I) := by
    unfold cepsQuad
    exact (hs.sub continuous_const).mul (hs.sub continuous_const)
  constructor
  · unfold cepsDmuLogF
    exact ((hs.mul hA).neg.div hd hdne).add
      (((continuous_const.mul hs).sub continuous_const).div hQ hQne)
  · unfold cepsDqLogF
    exact (hA.div hd hdne).add (((continuous_const.mul hs).sub continuous_const).div hQ hQne)

/-- Common facts at a point of a line (real drift). -/
theorem line_point_facts {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ} (hc1 : dom.c₀ ≤ c)
    (hc2 : c ≤ 2 * dom.c₀) {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀)
    (y : ℝ) :
    (μ, q) ∈ cepsSPRegion D θ ρW ∧ cepsD ρW μ q (c + y * I) ≠ 0 ∧
      cepsQuad D θ ρW μ q (c + y * I) ≠ 0 ∧ ((c : ℂ) + y * I) ^ 2 - (γ : ℂ) ^ 2 ≠ 0 ∧
      cepsF D θ ρW γ μ q (c + y * I) ∈ slitPlane := by
  have hc0 := dom.c₀_pos
  set s : ℂ := (c : ℂ) + y * I with hsdef
  have hsre : s.re = c := by simp [hsdef]
  have hadm : |μ.im| * |s.im| ≤ dom.η := by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le
  have h2 : dom.c₀ ≤ |s.re| := by rw [hsre, abs_of_pos (by linarith)]; exact hc1
  have h3 : |s.re| ≤ 2 * dom.c₀ := by rw [hsre, abs_of_pos (by linarith)]; exact hc2
  refine ⟨dom.mem_SPRegion hW hθ hD hμ hq, ?_, ?_, ?_, ?_⟩
  · intro h0
    have := dom.norm_cepsD_ge hW hθ hD hμ hadm hq h2 h3
    rw [h0, norm_zero] at this
    have := dom.dd₀_pos hD
    unfold dd₀ at this
    linarith
  · exact dom.cepsQuad_ne_zero hW hθ hD hμ hq (by have := re_le_norm s; linarith)
  · intro h0
    have h := congrArg re h0
    have hγc : 2 * dom.c₀ < γ := by
      have := dom.c₀_le; have := dom.ρA_one; linarith
    rw [sub_re, zero_re, ← ofReal_pow, ofReal_re, sq s, mul_re, hsre] at h
    have hy : 0 ≤ s.im * s.im := mul_self_nonneg _
    nlinarith
  · obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 hμ hadm hq h2 h3
    exact Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre)

set_option maxHeartbeats 1000000 in
/-- **C-3(c)/C-4: first drift derivative of `L`** under line decay of `M₀`. -/
theorem hasDerivAt_cepsCanonL_mu {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {K : ℝ}
    (hdec : ∀ y : ℝ, ‖stepTransform ρW (c + y * I)‖ ≤ K / (1 + y ^ 2)) {t : ℝ}
    (ht : |t| < dom.μ₀ / 2) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {ζ : ℂ} (hζ : ζ.re < c) :
    Integrable (fun y : ℝ => cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ)) ∧
      HasDerivAt (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ)
        ((2 * Real.pi : ℂ)⁻¹ *
          ∫ y : ℝ, cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ)) t := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμ0 := dom.μ₀_pos
  have hq' : ‖q‖ ≤ dom.q₀ := by have := dom.q₀_pos; linarith
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hdec 0); simpa using this
  set δ : ℝ := dom.μ₀ / 2 - |t| with hδ
  have hδ0 : 0 < δ := by linarith
  have hball : ∀ t' ∈ Metric.ball t δ, ‖(t' : ℂ)‖ ≤ dom.μ₀ / 2 := by
    intro t' ht'
    rw [Metric.mem_ball, Real.dist_eq] at ht'
    rw [norm_real, Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub t' t
    linarith
  set Cμ : ℝ := 3 / dom.dd₀ + 4 * dom.c₀ / dom.μ₀ with hCμ
  have hdd := dom.dd₀_pos hD
  have hCμ0 : 0 ≤ Cμ := by positivity
  set bound : ℝ → ℝ := fun y => Cμ * ((1 + c ^ 2) * K ^ 2 * (1 + y ^ 2)⁻¹ +
    ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ + ((y - 0) ^ 2 + c ^ 2)⁻¹) with hbound
  obtain ⟨hi1, -⟩ := integral_inv_sq_add_sq (d := c - ζ.re) (by linarith) ζ.im
  obtain ⟨hi2, -⟩ := integral_inv_sq_add_sq (d := c) (by linarith) 0
  have hBint : Integrable bound :=
    ((((integrable_inv_one_add_sq).const_mul ((1 + c ^ 2) * K ^ 2)).add hi1).add hi2).const_mul Cμ
  -- pointwise bound
  have hpt : ∀ y : ℝ, ∀ t' ∈ Metric.ball t δ,
      ‖cepsDmuLogF D θ ρW t' q (c + y * I) / ((c : ℂ) + y * I - ζ)‖ ≤ bound y := by
    intro y t' ht'
    set s : ℂ := (c : ℂ) + y * I with hsdef
    have hsre : s.re = c := by simp [hsdef]
    obtain ⟨hdμ, -⟩ := dom.norm_dLogF_le hW hθ hD (μ := (t' : ℂ)) (q := q) (s := s) (hball t' ht')
      (by simp; exact dom.η_pos.le) hq (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
      (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
    have hs0 : 0 < ‖s‖ := by have := re_le_norm s; rw [hsre] at this; linarith
    have hsζ : 0 < ‖s - ζ‖ := by
      have := re_le_norm (s - ζ); rw [sub_re, hsre] at this; linarith
    set a := ‖s‖ * ‖stepTransform ρW s‖ with ha
    set b := 1 / ‖s - ζ‖ with hb
    set e := 1 / ‖s‖ with he
    have ha0 : 0 ≤ a := by positivity
    have hb0 : 0 ≤ b := by positivity
    have he0 : 0 ≤ e := by positivity
    have ha2 : a ^ 2 ≤ (1 + c ^ 2) * K ^ 2 * (1 + y ^ 2)⁻¹ := by
      have h1 : ‖stepTransform ρW s‖ ≤ K / (1 + y ^ 2) := hdec y
      have h2 : ‖s‖ ^ 2 = y ^ 2 + c ^ 2 := by rw [hsdef, norm_line_sq']; ring
      have hy : 0 < 1 + y ^ 2 := by positivity
      have hM0 : 0 ≤ ‖stepTransform ρW s‖ := norm_nonneg _
      rw [ha, mul_pow, h2]
      have h3 : ‖stepTransform ρW s‖ ^ 2 ≤ (K / (1 + y ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hM0 h1 2
      calc (y ^ 2 + c ^ 2) * ‖stepTransform ρW s‖ ^ 2 ≤ (y ^ 2 + c ^ 2) * (K / (1 + y ^ 2)) ^ 2 :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ (1 + c ^ 2) * K ^ 2 * (1 + y ^ 2)⁻¹ := by
            rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
            have : (1 + c ^ 2) * K ^ 2 * (1 + y ^ 2)⁻¹ * (1 + y ^ 2) ^ 2 =
                (1 + c ^ 2) * K ^ 2 * (1 + y ^ 2) := by field_simp
            rw [this]
            nlinarith [sq_nonneg y, sq_nonneg c, sq_nonneg K, mul_nonneg (sq_nonneg y) (sq_nonneg c)]
    have hb2 : b ^ 2 = ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ := by
      rw [hb, one_div, inv_pow, hsdef, norm_line_sub_sq']
    have he2 : e ^ 2 = ((y - 0) ^ 2 + c ^ 2)⁻¹ := by
      rw [he, one_div, inv_pow, hsdef, norm_line_sq']
    rw [norm_div, div_eq_mul_one_div]
    calc ‖cepsDmuLogF D θ ρW t' q s‖ * (1 / ‖s - ζ‖)
        ≤ (3 / dom.dd₀ * a + 4 * dom.c₀ / dom.μ₀ * e) * b := by
          exact mul_le_mul_of_nonneg_right hdμ hb0
      _ ≤ Cμ * (a ^ 2 + b ^ 2 + e ^ 2) := by
          have h1 : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
          have h2 : e * b ≤ e ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (e - b)]
          have h3 : 0 ≤ 3 / dom.dd₀ := by positivity
          have h4 : 0 ≤ 4 * dom.c₀ / dom.μ₀ := by positivity
          calc (3 / dom.dd₀ * a + 4 * dom.c₀ / dom.μ₀ * e) * b
              = 3 / dom.dd₀ * (a * b) + 4 * dom.c₀ / dom.μ₀ * (e * b) := by ring
            _ ≤ 3 / dom.dd₀ * (a ^ 2 + b ^ 2 + e ^ 2) + 4 * dom.c₀ / dom.μ₀ * (a ^ 2 + b ^ 2 + e ^ 2) := by
                gcongr
                · nlinarith [sq_nonneg e]
                · nlinarith [sq_nonneg a]
            _ = Cμ * (a ^ 2 + b ^ 2 + e ^ 2) := by rw [hCμ]; ring
      _ ≤ bound y := by
          simp only [hbound]
          gcongr
          · rw [hb2]
          · rw [he2]
  -- differentiability of the integrand
  have hdiff : ∀ y : ℝ, ∀ t' ∈ Metric.ball t δ,
      HasDerivAt (fun t'' : ℝ => cepsLineIntegrand D θ ρW γ c t'' q ζ y)
        (cepsDmuLogF D θ ρW t' q (c + y * I) / ((c : ℂ) + y * I - ζ)) t' := by
    intro y t' ht'
    have hμ' : ‖(t' : ℂ)‖ ≤ dom.μ₀ := by have := hball t' ht'; linarith
    obtain ⟨hx, hd, hQ, hγs, hslit⟩ := dom.line_point_facts hW hθ hD hγ1 hγ2 hc1 hc2 hμ'
      (by simp) hq' y
    have h := (hasDerivAt_logF_mu hW hθ hD hx hd hQ hγs hslit).comp_ofReal
    exact h.div_const _
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t' : ℝ => cepsLineIntegrand D θ ρW γ c t' q ζ)
    (F' := fun t' y => cepsDmuLogF D θ ρW t' q (c + y * I) / ((c : ℂ) + y * I - ζ))
    (bound := bound) (x₀ := t) (Metric.ball_mem_nhds t hδ0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds t hδ0) fun t' ht' =>
      (dom.continuous_lineIntegrand hW hθ hD hγ1 hγ2 hc1 hc2
        (by have := hball t' ht'; linarith) (by simp) hq' hζ).aestronglyMeasurable)
    (dom.integrable_cepsCanonL_integrand hW hθ hD hγ1 hγ2 hc1 hc2
      (by have := hball t (Metric.mem_ball_self hδ0); linarith) (by simp) hq' hζ)
    (((dom.continuous_dLogF_line hW hθ hD hc1 hc2
      (by have := hball t (Metric.mem_ball_self hδ0); linarith) (by simp) hq').1.div
      (by fun_prop) (fun y h0 => by
        have := congrArg re h0; simp at this; linarith)).aestronglyMeasurable)
    (Eventually.of_forall fun y t' ht' => hpt y t' ht') hBint
    (Eventually.of_forall fun y t' ht' => hdiff y t' ht')
  refine ⟨hmain.1, ?_⟩
  have e : (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) = fun t' : ℝ =>
      (2 * Real.pi : ℂ)⁻¹ * (∫ y, cepsLineIntegrand D θ ρW γ c t' q ζ y) - Complex.log (γ - ζ) := by
    funext t'; rfl
  rw [e]
  exact (hmain.2.const_mul _).sub_const _

end

end CepsCanonDomain

end PGM
