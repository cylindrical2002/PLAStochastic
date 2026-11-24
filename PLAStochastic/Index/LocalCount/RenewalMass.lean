import PLAStochastic.ForMathlib.Probability.LatticeConcentration.RenewalOneTime
import PLAStochastic.Index.LocalCount.SummationEstimates
import PLAStochastic.Index.LocalCount.MaximalBernstein

/-!
# Local-count base estimates

Lean companion of the renewal, early-stop and kernel-sum parts of
`theory/proofs/proofK_local_count_core.tex`.  The proofs live in three helper modules; this
module assembles the renewal mass and collects the results.

* `KestenIID K` (`PLAStochastic.ForMathlib.Probability.LatticeConcentration.RenewalOneTime`): Kesten's iid lattice inequality with constant
  `K` (`klc:lem:kesten`), `sup_k P(S_n = k) · √(n (1 - p)) ≤ K p`, taken as a hypothesis.
* `renewal_one_time_le` (klc:eq:renewal-one-time): for a law `μ` on `ℤ` with mean `m > 0`,
  `E Q² ≤ B₂ m²` and largest atom `p = lconc μ 1 ≤ 1/2`, for `t ≥ 2`,
  `P(S_t = k) ≤ 8 K max(1, 4B₂) p / √t · min {1, t/(t - k/m)²}`
  (with `min {1, t/(t-a)²}` written `t / max t ((t - a)²)`, value `1` at `t = a`).
* `renewal_hits_le_one`: for increments `≥ 1`, `U(k) = ∑_{t ≥ 1} P(S_t = k) ≤ 1`.
* `renewal_mass_le`, `renewal_mass_toReal_le`, `renewal_mass_le_of_atoms`
  (klc:lem:renewal, klc:eq:renewal-mass): `U(k) ≤ C₂ p` uniformly in `k`,
  `C₂ = max 2 (1 + 240 K max(1, 4B₂))`.
* `maximal_bernstein`, `pairSegLen_le_prob`, `floor_two_eps_lt_pairSegLen`
  (`PLAStochastic.Index.LocalCount.MaximalBernstein`, klc:lem:maximal-bernstein, klc:eq:early-stop):
  `P(max_{j ≤ s} |∑_{i<j} (gᵢ/m₀ - 1)| > x) ≤ 2 exp(-c min(x²/s, x))`,
  `P(pairSegLen eps ≤ s) ≤ 2 exp(-c min(eps²/s, eps))` with `c = bernsteinRate θ B`, and
  `⌊2 eps⌋ < pairSegLen eps`.
* `lattice_min_sum`, `renewal_series_le`, `dyadic_min_sum_le`, `early_local_kernel_le`
  (`PLAStochastic.Index.LocalCount.SummationEstimates`, klc:eq:lattice-min-sum, klc:eq:dyadic-sum,
  klc:eq:early-local-kernel): `∑_t min(A, B/(t-x)²) ≤ 2A + 6√(AB)`;
  `∑_j min(C₁ a 2^j, C₂ e^{-c2^j}) ≤ (2 C₁ max(1, 1/c) + C₂) a log(e/a)`;
  `∑_{1 ≤ t ≤ E} t^{-3/2} min(e^{-cE/t}, 1, t/(t-x)²) ≤ (100/c + 16/c²)/E`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory LocalCountBase

/-- **Uniform pointwise renewal mass** (klc:lem:renewal, klc:eq:renewal-mass).  For iid
positive integer increments with law `μ`, mean `m`, `E Q² ≤ B₂ m²` and largest atom
`p = lconc μ 1`, `U(k) = ∑_{t ≥ 1} P(S_t = k) ≤ C₂ p` uniformly in `k`, with
`C₂ = max 2 (1 + 240 K max(1, 4 B₂))`. -/
theorem renewal_mass_le {K : ℝ} (hK : KestenIID K) (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (hpos : μ (Set.Iic 0) = 0) (hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ) {m B₂ : ℝ}
    (hm : ∫ q, (q : ℝ) ∂μ = m) (hm0 : 0 < m) (hB : ∫ q, (q : ℝ) ^ 2 ∂μ ≤ B₂ * m ^ 2) (k : ℤ) :
    ∑' t : ℕ, convFin (t + 1) (fun _ => μ) {k} ≤
      ENNReal.ofReal (max 2 (1 + 240 * K * max 1 (4 * B₂)) * lconc μ 1) := by
  set p := lconc μ 1 with hpdef
  have hp0 : 0 ≤ p := lconc_nonneg μ 1
  by_cases hp : p ≤ 1 / 2
  · have hKp := mul_lconc_nonneg hK hp
    set C₁ := 8 * K * max 1 (4 * B₂) with hC₁
    have hC₁p : 0 ≤ C₁ * p := by
      rw [hC₁, show 8 * K * max 1 (4 * B₂) * p = 8 * max 1 (4 * B₂) * (K * p) by ring]
      exact mul_nonneg (by positivity) hKp
    set a : ℝ := k / m with ha
    set f : ℕ → ℝ := fun t =>
      Real.sqrt ((t : ℝ) + 1) / max ((t : ℝ) + 1) (((t : ℝ) + 1 - a) ^ 2) with hf
    have hf0 : ∀ t, 0 ≤ f t := fun t => div_nonneg (Real.sqrt_nonneg _)
      (le_max_of_le_left (by positivity))
    set g : ℕ → ℝ := fun t => (if t = 0 then p else 0) + C₁ * p * f t with hg
    have hg0 : ∀ t, 0 ≤ g t := fun t => add_nonneg (by split_ifs <;> simp [hp0])
      (mul_nonneg hC₁p (hf0 t))
    have hterm : ∀ t : ℕ, convFin (t + 1) (fun _ => μ) {k} ≤ ENNReal.ofReal (g t) := by
      intro t
      rcases Nat.eq_zero_or_pos t with h0 | htpos
      · subst h0
        rw [zero_add, convFin_one]
        refine (atom_le_ofReal_lconc μ k).trans (ENNReal.ofReal_le_ofReal ?_)
        show p ≤ (if (0 : ℕ) = 0 then p else 0) + C₁ * p * f 0
        rw [if_pos rfl]
        linarith [mul_nonneg hC₁p (hf0 0)]
      · have := isProbabilityMeasure_convFin_const μ (t + 1)
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := renewal_one_time_le hK hint hm hm0 hB hp (t := t + 1) (by omega) k
        have hsq : ((t : ℝ) + 1) / Real.sqrt ((t : ℝ) + 1) = Real.sqrt ((t : ℝ) + 1) :=
          Real.div_sqrt
        calc (convFin (t + 1) (fun _ => μ) {k}).toReal
            ≤ C₁ * p / Real.sqrt ((t + 1 : ℕ) : ℝ) *
                (((t + 1 : ℕ) : ℝ) / max ((t + 1 : ℕ) : ℝ) ((((t + 1 : ℕ) : ℝ) - k / m) ^ 2)) := h1
          _ = C₁ * p * f t := by
              have e : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by push_cast; ring
              rw [e]
              set T : ℝ := (t : ℝ) + 1
              set M : ℝ := max T ((T - k / m) ^ 2)
              rw [show C₁ * p / Real.sqrt T * (T / M) = C₁ * p * (T / Real.sqrt T) / M by ring,
                hsq]
              simp only [hf, ha, mul_div_assoc]
              rfl
          _ ≤ g t := by
              simp only [hg, if_neg htpos.ne']
              linarith
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    calc ∑ t ∈ Finset.range n, convFin (t + 1) (fun _ => μ) {k}
        ≤ ∑ t ∈ Finset.range n, ENNReal.ofReal (g t) := Finset.sum_le_sum fun t _ => hterm t
      _ = ENNReal.ofReal (∑ t ∈ Finset.range n, g t) :=
          (ENNReal.ofReal_sum_of_nonneg fun t _ => hg0 t).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsum : ∑ t ∈ Finset.range n, g t =
              (∑ t ∈ Finset.range n, if t = 0 then p else 0) +
                C₁ * p * ∑ t ∈ Finset.range n, f t := by
            simp only [hg, Finset.sum_add_distrib, Finset.mul_sum]
          have hite : (∑ t ∈ Finset.range n, if t = 0 then p else 0) ≤ p := by
            rw [Finset.sum_ite_eq' (Finset.range n) 0 (fun _ => p)]
            split_ifs <;> simp [hp0]
          have hser := renewal_series_le a n
          have h30 : C₁ * p * ∑ t ∈ Finset.range n, f t ≤ C₁ * p * 30 :=
            mul_le_mul_of_nonneg_left hser hC₁p
          have hmax : (1 + 240 * K * max 1 (4 * B₂)) * p ≤
              max 2 (1 + 240 * K * max 1 (4 * B₂)) * p :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hp0
          have : C₁ * p * 30 = (240 * K * max 1 (4 * B₂)) * p := by rw [hC₁]; ring
          nlinarith
  · push Not at hp
    refine (renewal_hits_le_one μ hpos k).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * p ≤ max 2 (1 + 240 * K * max 1 (4 * B₂)) * p :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
    linarith

/-- Real-valued form of `renewal_mass_le`: the renewal series is summable and
`∑_{t ≥ 1} P(S_t = k) ≤ C₂ p`. -/
theorem renewal_mass_toReal_le {K : ℝ} (hK : KestenIID K) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] (hpos : μ (Set.Iic 0) = 0)
    (hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ) {m B₂ : ℝ}
    (hm : ∫ q, (q : ℝ) ∂μ = m) (hm0 : 0 < m) (hB : ∫ q, (q : ℝ) ^ 2 ∂μ ≤ B₂ * m ^ 2) (k : ℤ) :
    Summable (fun t : ℕ => (convFin (t + 1) (fun _ => μ) {k}).toReal) ∧
    ∑' t : ℕ, (convFin (t + 1) (fun _ => μ) {k}).toReal ≤
      max 2 (1 + 240 * K * max 1 (4 * B₂)) * lconc μ 1 := by
  have h := renewal_mass_le hK μ hpos hint hm hm0 hB k
  have hfin : ∑' t : ℕ, convFin (t + 1) (fun _ => μ) {k} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hne : ∀ t : ℕ, convFin (t + 1) (fun _ => μ) {k} ≠ ⊤ := fun t => by
    have := isProbabilityMeasure_convFin_const μ (t + 1)
    exact measure_ne_top _ _
  refine ⟨ENNReal.summable_toReal hfin, ?_⟩
  rw [← ENNReal.tsum_toReal_eq hne]
  have hC : 0 ≤ max 2 (1 + 240 * K * max 1 (4 * B₂)) * lconc μ 1 :=
    mul_nonneg (le_max_of_le_left (by norm_num)) (lconc_nonneg μ 1)
  exact ENNReal.toReal_le_of_le_ofReal hC h

/-- `renewal_mass_le` with the moment hypotheses written as series over the atoms,
`m = ∑_q q μ{q}` and `∑_q q² μ{q} ≤ B₂ m²`. -/
theorem renewal_mass_le_of_atoms {K : ℝ} (hK : KestenIID K) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] (hpos : μ (Set.Iic 0) = 0) {m B₂ : ℝ}
    (hsum : Summable (fun q : ℤ => (q : ℝ) ^ 2 * μ.real {q}))
    (hm : ∑' q : ℤ, (q : ℝ) * μ.real {q} = m) (hm0 : 0 < m)
    (hB : ∑' q : ℤ, (q : ℝ) ^ 2 * μ.real {q} ≤ B₂ * m ^ 2) (k : ℤ) :
    ∑' t : ℕ, convFin (t + 1) (fun _ => μ) {k} ≤
      ENNReal.ofReal (max 2 (1 + 240 * K * max 1 (4 * B₂)) * lconc μ 1) := by
  have hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ :=
    integrable_of_summable_atoms (by
      refine hsum.congr fun q => ?_
      rw [abs_of_nonneg (sq_nonneg (q : ℝ))])
  have hint1 : Integrable (fun q : ℤ => (q : ℝ)) μ :=
    ((memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).2 hint).integrable
      one_le_two
  refine renewal_mass_le hK μ hpos hint ?_ hm0 ?_ k
  · rw [integral_eq_tsum_atoms hint1, hm]
  · rw [integral_eq_tsum_atoms hint]; exact hB

end

end PGM
