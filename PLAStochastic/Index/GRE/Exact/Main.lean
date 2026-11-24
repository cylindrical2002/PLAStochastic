import PLAStochastic.Index.GRE.PreciseHeightDefs
import PLAStochastic.Index.GRE.Exact.WindowArithmetic

/-!
# G-RE exact: the ALG-RE height is a deterministic integer off windows

`thm:GRE` of `research/2026-09-24-height-precision-ceiling/tex/main.tex`, for the actual ALG-RE
run on the Model G keys `x0 + g 0 + ⋯ + g (s-1)` (any `GapLaw`, any measurable offset `x0`).
For `c > 0` put `y = greY c n ε = log₂ (log n / log (c ε²) + 1)` and
`w = greW K n ε = K (1 / log ε + log log n / log n)`.  Along `n → ∞`, `ε → ∞`,
`log ε = o(log n)`:

* `G_RE_exact`: eventually an event of probability at least `1 - n⁻² - log⁻² n` carries
  `y - w < H ≤ y + 1 + w`, and `H = ⌈y⌉` whenever `dist (y, ℤ) ≥ w`;
* `G_RE_exact_integral`: the same bounds for `E H`, up to `K / log n`;
* `G_RE_exact_limit`: `E H - log₂ (log n / log ε) ∈ [-1, 0] + o(1)`.

The constant is explicit, `K = greK μ₀ σ₀ c`.  The TeX base `A = κ_opt G₀` is replaced by `c ε²`
for an arbitrary `c > 0`: the proof uses only the constant-factor count bracket of
`PLAStochastic.Index.GRE.FixedParameter`, and every fixed `c` changes `log (c ε²) - 2 log ε` by `O(1)`.  The event is the
count-bracket good event at level `tRE (n²)` intersected with a Kolmogorov event (`greGood`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

-- `hx0` is part of the fixed statement; the pathwise result does not need it.
set_option linter.unusedVariables false in
/-- **G-RE exact** (`thm:GRE` (a), (b)).  Eventually along HEIGHT, an event of probability at least
`1 - n⁻² - log⁻² n` carries `y - w < H ≤ y + 1 + w`, and `H = ⌈y⌉` when `y` is at distance at
least `w` from `ℤ`. -/
theorem G_RE_exact [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, ∀ {n : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (n k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∃ E : Set Ω, MeasurableSet E ∧
        P.real Eᶜ ≤ 1 / (n k : ℝ) ^ 2 + 1 / Real.log (n k) ^ 2 ∧
        ∀ ω ∈ E,
          (greY c (n k) (ε k) - greW K (n k) (ε k) <
              (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∧
            (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ≤
              greY c (n k) (ε k) + 1 + greW K (n k) (ε k)) ∧
          ((∀ m : ℤ, greW K (n k) (ε k) ≤ |greY c (n k) (ε k) - m|) →
            ((reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℕ) : ℤ) =
              ⌈greY c (n k) (ε k)⌉) := by
  refine ⟨greK μ₀ σ₀ c, fun {n} {ε} hn hε hεn => ?_⟩
  filter_upwards [eventually_GREParams (κ₀ := κ₀) le_rfl hn hε hεn] with k hp
  exact ⟨greGood (ε k) g μ₀ σ₀ (n k), measurableSet_greGood hg.iid.measurable _ _ _ _,
    measureReal_greGood_compl_le hg hp.eps0 hp.n3,
    fun ω hω => hp.window hg.mu_pos hg.sigma_pos hc (x0 ω) hω⟩

/-- **G-RE exact, expectation.**  Eventually along HEIGHT,
`y - w - K / log n ≤ E H ≤ y + 1 + w + K / log n`, and `|E H - ⌈y⌉| ≤ K / log n` when `y` is at
distance at least `w` from `ℤ`. -/
theorem G_RE_exact_integral [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, ∀ {n : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (n k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop,
        greY c (n k) (ε k) - greW K (n k) (ε k) - K / Real.log (n k) ≤
            ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P ∧
          ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P ≤
            greY c (n k) (ε k) + 1 + greW K (n k) (ε k) + K / Real.log (n k) ∧
          ((∀ m : ℤ, greW K (n k) (ε k) ≤ |greY c (n k) (ε k) - m|) →
            |∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P -
              ⌈greY c (n k) (ε k)⌉| ≤ K / Real.log (n k)) := by
  refine ⟨greK μ₀ σ₀ c, fun {n} {ε} hn hε hεn => ?_⟩
  filter_upwards [eventually_GREParams (κ₀ := κ₀) le_rfl hn hε hεn] with k hp
  exact hp.integral hg hx0 hc

/-- **G-RE exact, limit form.**  Along HEIGHT, `E H - log₂ (log n / log ε)` eventually lies in
`[-1 - η, η]` for every `η > 0`. -/
theorem G_RE_exact_limit [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    ∀ η > 0, ∀ᶠ k in atTop,
      -1 - η ≤ ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P -
          Real.logb 2 (Real.log (n k) / Real.log (ε k)) ∧
        ∫ ω, (reHeight (ε k) (fun s => x0 ω + ∑ i ∈ range s, g i ω) (n k) : ℝ) ∂P -
          Real.logb 2 (Real.log (n k) / Real.log (ε k)) ≤ η := by
  intro η hη
  obtain ⟨K, hK⟩ := G_RE_exact_integral hg hx0 (c := 1) one_pos
  have hint := hK hn hε hεn
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLε : Tendsto (fun k => Real.log (ε k)) atTop atTop := Real.tendsto_log_atTop.comp hε
  have hw := tendsto_greW K hn hε
  have hKL : Tendsto (fun k => K / Real.log (n k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  -- `y - log₂ (log n / log ε) = log₂ (1/2 + log ε / log n) → -1` for `c = 1`
  have hD : Tendsto (fun k => greY 1 (n k) (ε k) - Real.logb 2 (Real.log (n k) / Real.log (ε k)))
      atTop (𝓝 (-1)) := by
    have h1 : Tendsto (fun k => 1 / 2 + Real.log (ε k) / Real.log (n k)) atTop (𝓝 (1 / 2)) := by
      have := hεn.const_add (1 / 2)
      rwa [add_zero] at this
    have h2 : Tendsto (fun k => Real.logb 2 (1 / 2 + Real.log (ε k) / Real.log (n k))) atTop
        (𝓝 (Real.logb 2 (1 / 2))) := (h1.log (by norm_num)).div_const (Real.log 2)
    have h3 : Real.logb 2 (1 / 2) = -1 := by
      rw [one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
    rw [h3] at h2
    refine h2.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0, hLε.eventually_gt_atTop 0] with k h1 h2
    unfold greY
    rw [one_mul, Real.log_pow, ← Real.logb_div (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
  have hlo : Tendsto (fun k => greY 1 (n k) (ε k) - greW K (n k) (ε k) - K / Real.log (n k) -
      Real.logb 2 (Real.log (n k) / Real.log (ε k))) atTop (𝓝 (-1)) := by
    have := (hD.sub hw).sub hKL
    rw [sub_zero, sub_zero] at this
    refine this.congr fun k => ?_
    ring
  have hhi : Tendsto (fun k => greY 1 (n k) (ε k) + 1 + greW K (n k) (ε k) + K / Real.log (n k) -
      Real.logb 2 (Real.log (n k) / Real.log (ε k))) atTop (𝓝 0) := by
    have := ((hD.add_const 1).add hw).add hKL
    rw [add_zero, add_zero, neg_add_cancel] at this
    refine this.congr fun k => ?_
    ring
  filter_upwards [hint, hlo.eventually (eventually_ge_nhds (show -1 - η < -1 by linarith)),
    hhi.eventually (eventually_le_nhds hη)] with k hk h1 h2
  obtain ⟨hk1, hk2, -⟩ := hk
  constructor <;> linarith

end

end PGM
