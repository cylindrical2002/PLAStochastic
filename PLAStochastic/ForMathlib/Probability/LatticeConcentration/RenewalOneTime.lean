import PLAStochastic.ForMathlib.Probability.LatticeConcentration.Elementary
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Pointwise renewal mass: the one-time bound

Source: `theory/proofs/proofK_local_count_core.tex`, `klc:lem:kesten` and `klc:lem:renewal`.

* `KestenIID K`: Kesten's iid lattice inequality with constant `K` (a hypothesis here).
* `LocalCountBase.convFin_moments`: `convFin n μ`, the law of `X₀ + ⋯ + X_{n-1}` for iid
  `Xᵢ ∼ μ` (`map_sum_range_eq_convFin`), has mean `n m` and variance `n Var μ`.
* `LocalCountBase.conv_singleton_le_split`: `(ν₁ ∗ ν₂){k} ≤ sup ν₂ · ν₁(E) + sup ν₁ · ν₂(F)`
  whenever `u ∉ E → k - u ∈ F` (the half carrying the deviation gets Chebyshev, the other
  half Kesten).
* `renewal_one_time_le` (klc:eq:renewal-one-time): for `p = lconc μ 1 ≤ 1/2`, mean `m > 0` and
  `E Q² ≤ B₂ m²`, `P(S_t = k) ≤ 8 K max(1, 4 B₂) p / √t · min {1, t/(t - k/m)²}` for `t ≥ 2`,
  where `min {1, t/(t-a)²}` (value `1` at `t = a`) is written `t / max t ((t - a)²)`.
* `renewal_hits_le_one`: for increments `≥ 1`, `∑_{t ≥ 1} P(S_t = k) ≤ 1` (the walk is
  strictly increasing, so it hits `k` at most once).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

/-- Kesten's iid lattice inequality with constant `K` (`klc:lem:kesten`, in the form proved
in `PLAStochastic.ForMathlib.Probability.LatticeConcentration.Kesten`): `sup_k P(Q₁ + ⋯ + Qₙ = k) · √(n (1 - p)) ≤ K p` with `p = sup_q P(Q₁ = q)`. -/
def KestenIID (K : ℝ) : Prop :=
  ∀ (μ : Measure ℤ), IsProbabilityMeasure μ → ∀ n : ℕ, 1 ≤ n → lconc μ 1 < 1 →
    lconc (convFin n (fun _ => μ)) 1 * Real.sqrt (n * (1 - lconc μ 1)) ≤ K * lconc μ 1

namespace LocalCountBase

/-! ## Constant-family finite convolutions -/

theorem convFin_succ (μ : Measure ℤ) (n : ℕ) :
    convFin (n + 1) (fun _ => μ) = convFin n (fun _ => μ) ∗ μ := rfl

theorem convFin_one (μ : Measure ℤ) [SFinite μ] : convFin 1 (fun _ => μ) = μ := by
  rw [convFin_succ]
  exact Measure.dirac_zero_conv μ

theorem convFin_add (μ : Measure ℤ) [IsProbabilityMeasure μ] (r : ℕ) :
    ∀ s : ℕ, convFin (r + s) (fun _ => μ) = convFin r (fun _ => μ) ∗ convFin s (fun _ => μ)
  | 0 => by
    have := isProbabilityMeasure_convFin_const μ r
    simp only [Nat.add_zero, convFin]
    exact (Measure.conv_dirac_zero _).symm
  | s + 1 => by
    have := isProbabilityMeasure_convFin_const μ r
    have := isProbabilityMeasure_convFin_const μ s
    rw [← Nat.add_assoc, convFin_succ, convFin_succ, convFin_add μ r s, Measure.conv_assoc]

/-! ## Square-integrable increments -/

section RandomWalk

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℤ} {μ : Measure ℤ}

theorem memLp_cast_comp (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = μ)
    (hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ) (i : ℕ) :
    MemLp (fun ω => (X i ω : ℝ)) 2 P := by
  have h2 : MemLp (fun q : ℤ => (q : ℝ)) 2 μ :=
    (memLp_two_iff_integrable_sq (Measurable.of_discrete.aestronglyMeasurable)).2 hint
  rw [← hlaw i] at h2
  exact (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
    (hX i).aemeasurable).1 h2

end RandomWalk

/-! ## Mean and variance of `convFin` -/

section Moments

variable {μ : Measure ℤ} [IsProbabilityMeasure μ]

theorem convFin_moments (hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ) (n : ℕ) :
    MemLp (fun u : ℤ => (u : ℝ)) 2 (convFin n (fun _ => μ)) ∧
    ∫ u, (u : ℝ) ∂(convFin n (fun _ => μ)) = n * ∫ q, (q : ℝ) ∂μ ∧
    Var[fun u : ℤ => (u : ℝ); convFin n (fun _ => μ)] = n * Var[fun u : ℤ => (u : ℝ); μ] := by
  obtain ⟨Ω, _, P, X, hX, hlaw, hind, hP⟩ := exists_iid ℕ μ
  have hlaw' : ∀ i, P.map (X i) = μ := fun i => (hlaw i).map_eq
  have hS : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
    Finset.measurable_sum _ fun i _ => hX i
  have hmem := memLp_cast_comp hX hlaw' hint
  have hcomp : (fun u : ℤ => (u : ℝ)) ∘ (fun ω => ∑ i ∈ Finset.range n, X i ω) =
      ∑ i ∈ Finset.range n, fun ω => (X i ω : ℝ) := by
    funext ω; simp [Finset.sum_apply]
  rw [← map_sum_range_eq_convFin hX hind hlaw' n]
  refine ⟨?_, ?_, ?_⟩
  · rw [memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable hS.aemeasurable,
      hcomp]
    exact memLp_finsetSum' _ fun i _ => hmem i
  · rw [integral_map hS.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
    have := congrFun hcomp
    simp only [Function.comp_apply] at this
    simp_rw [this, Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ => (hmem i).integrable one_le_two]
    have hi : ∀ i, ∫ ω, (X i ω : ℝ) ∂P = ∫ q, (q : ℝ) ∂μ := fun i => by
      rw [← hlaw' i, integral_map (hX i).aemeasurable
        Measurable.of_discrete.aestronglyMeasurable]
    simp [hi]
  · rw [variance_map Measurable.of_discrete.aemeasurable hS.aemeasurable, hcomp,
      IndepFun.variance_sum (fun i _ => hmem i)]
    · have hi : ∀ i, Var[fun ω => (X i ω : ℝ); P] = Var[fun u : ℤ => (u : ℝ); μ] := fun i => by
        rw [← hlaw' i, variance_map Measurable.of_discrete.aemeasurable (hX i).aemeasurable]
        rfl
      simp [hi]
    · intro i _ j _ hij
      exact (hind.indepFun hij).comp Measurable.of_discrete Measurable.of_discrete

end Moments

/-! ## Chebyshev, the half-splitting and Kesten -/

section OneTime

variable {μ : Measure ℤ} [IsProbabilityMeasure μ]

/-- Chebyshev for `convFin`: `δ² · ν_n {u | δ ≤ |u - n m|} ≤ n Var(μ)`. -/
theorem convFin_tail_mul_sq_le (hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ) (n : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (convFin n (fun _ => μ) {u : ℤ | δ ≤ |(u : ℝ) - n * ∫ q, (q : ℝ) ∂μ|}).toReal * δ ^ 2 ≤
      n * Var[fun u : ℤ => (u : ℝ); μ] := by
  have hV : 0 ≤ (n : ℝ) * Var[fun u : ℤ => (u : ℝ); μ] :=
    mul_nonneg (Nat.cast_nonneg _) (variance_nonneg _ _)
  rcases hδ.eq_or_lt with h | h
  · rw [← h]; simpa using hV
  · have := isProbabilityMeasure_convFin_const μ n
    obtain ⟨hmem, hmean, hvar⟩ := convFin_moments hint n
    have hc := meas_ge_le_variance_div_sq hmem h
    rw [hmean, hvar] at hc
    have h2 := ENNReal.toReal_le_of_le_ofReal (div_nonneg hV (sq_nonneg δ)) hc
    rwa [le_div_iff₀ (by positivity)] at h2

/-- Splitting a two-block convolution according to which block carries a large deviation. -/
theorem conv_singleton_le_split (ν₁ ν₂ : Measure ℤ) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] {E F : Set ℤ} {k : ℤ} (hEF : ∀ u, u ∉ E → k - u ∈ F) :
    (ν₁ ∗ ν₂) {k} ≤
      ENNReal.ofReal (lconc ν₂ 1) * ν₁ E + ENNReal.ofReal (lconc ν₁ 1) * ν₂ F := by
  rw [conv_apply_singleton]
  calc ∫⁻ u, ν₂ {k - u} ∂ν₁
      ≤ ∫⁻ u, (E.indicator (fun _ => ENNReal.ofReal (lconc ν₂ 1)) u +
          (ν₂.restrict F) {k - u}) ∂ν₁ := by
        refine lintegral_mono fun u => ?_
        by_cases hu : u ∈ E
        · rw [Set.indicator_of_mem hu]
          exact le_add_right (atom_le_ofReal_lconc ν₂ _)
        · rw [Measure.restrict_apply MeasurableSet.of_discrete,
            Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (hEF u hu))]
          exact le_add_left le_rfl
    _ = ENNReal.ofReal (lconc ν₂ 1) * ν₁ E + (ν₁ ∗ ν₂.restrict F) {k} := by
        rw [lintegral_add_left Measurable.of_discrete,
          lintegral_indicator_const MeasurableSet.of_discrete, conv_apply_singleton]
    _ ≤ _ := by
        gcongr
        rw [Measure.conv_comm, conv_apply_singleton]
        calc ∫⁻ v, ν₁ {k - v} ∂(ν₂.restrict F)
            ≤ ∫⁻ _, ENNReal.ofReal (lconc ν₁ 1) ∂(ν₂.restrict F) :=
              lintegral_mono fun v => atom_le_ofReal_lconc ν₁ _
          _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

/-- Kesten for `p ≤ 1/2`: `sup_k ν_n{k} ≤ 2 K p / √n`. -/
theorem lconc_convFin_le {K : ℝ} (hK : KestenIID K) (hp : lconc μ 1 ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) :
    lconc (convFin n (fun _ => μ)) 1 ≤ 2 * K * lconc μ 1 / Real.sqrt n := by
  have h := hK μ inferInstance n hn (by linarith)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : Real.sqrt n / 2 ≤ Real.sqrt (n * (1 - lconc μ 1)) := by
    rw [Real.le_sqrt (by positivity) (by nlinarith), div_pow, Real.sq_sqrt hn'.le]
    nlinarith
  have hL := lconc_nonneg (convFin n (fun _ => μ)) 1
  rw [le_div_iff₀ (Real.sqrt_pos.2 hn')]
  nlinarith [mul_le_mul_of_nonneg_left hsq hL]

theorem mul_lconc_nonneg {K : ℝ} (hK : KestenIID K) (hp : lconc μ 1 ≤ 1 / 2) :
    0 ≤ K * lconc μ 1 := by
  have h := hK μ inferInstance 1 le_rfl (by linarith)
  exact le_trans (mul_nonneg (lconc_nonneg _ _) (Real.sqrt_nonneg _)) h

/-- **One-time renewal bound** (klc:eq:renewal-one-time).  With `a = k/m`,
`P(S_t = k) ≤ C₁ p / √t · min {1, t / (t - a)²}` for `t ≥ 2`, `C₁ = 8 K max(1, 4 B₂)`.
Here `t / max t ((t - a)²)` is `min {1, t/(t-a)²}` with the value `1` at `t = a`. -/
theorem _root_.PGM.renewal_one_time_le {K : ℝ} (hK : KestenIID K)
    (hint : Integrable (fun q : ℤ => (q : ℝ) ^ 2) μ) {m B₂ : ℝ} (hm : ∫ q, (q : ℝ) ∂μ = m)
    (hm0 : 0 < m) (hB : ∫ q, (q : ℝ) ^ 2 ∂μ ≤ B₂ * m ^ 2) (hp : lconc μ 1 ≤ 1 / 2)
    {t : ℕ} (ht : 2 ≤ t) (k : ℤ) :
    (convFin t (fun _ => μ) {k}).toReal ≤
      8 * K * max 1 (4 * B₂) * lconc μ 1 / Real.sqrt t *
        (t / max (t : ℝ) (((t : ℝ) - k / m) ^ 2)) := by
  set p := lconc μ 1 with hpdef
  set r := t / 2 with hr
  set s := t - r with hs
  have hr1 : 1 ≤ r := by omega
  have hs1 : 1 ≤ s := by omega
  have hrs : r + s = t := by omega
  have htr : (t : ℝ) ≤ 4 * r := by
    have : t ≤ 4 * r := by omega
    exact_mod_cast this
  have hts : (t : ℝ) ≤ 4 * s := by
    have : t ≤ 4 * s := by omega
    exact_mod_cast this
  have hrt : (r : ℝ) ≤ t := by exact_mod_cast (show r ≤ t by omega)
  have hst : (s : ℝ) ≤ t := by exact_mod_cast (show s ≤ t by omega)
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htrs : (t : ℝ) = r + s := by exact_mod_cast hrs.symm
  -- variance
  set V := Var[fun u : ℤ => (u : ℝ); μ] with hVdef
  have hV0 : 0 ≤ V := variance_nonneg _ _
  have hVB : V ≤ B₂ * m ^ 2 := by
    refine le_trans ?_ hB
    have := variance_le_expectation_sq (μ := μ) (X := fun u : ℤ => (u : ℝ))
      Measurable.of_discrete.aestronglyMeasurable
    simpa [Pi.pow_apply] using this
  have hVm : V / m ^ 2 ≤ B₂ := by rw [div_le_iff₀ (by positivity)]; exact hVB
  have hB0 : 0 ≤ B₂ := le_trans (div_nonneg hV0 (sq_nonneg m)) hVm
  -- the deviation
  set d : ℝ := (k : ℝ) - t * m with hd
  set δ : ℝ := |d| / 2 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set E : Set ℤ := {u : ℤ | δ ≤ |(u : ℝ) - r * m|} with hE
  set F : Set ℤ := {v : ℤ | δ ≤ |(v : ℝ) - s * m|} with hF
  have hEF : ∀ u, u ∉ E → k - u ∈ F := by
    intro u hu
    simp only [hE, Set.mem_ofPred_eq, not_le] at hu
    simp only [hF, Set.mem_ofPred_eq]
    push_cast
    have htri : |d| ≤ |(u : ℝ) - r * m| + |(k : ℝ) - u - s * m| := by
      have : d = ((u : ℝ) - r * m) + ((k : ℝ) - u - s * m) := by rw [hd, htrs]; ring
      rw [this]; exact abs_add_le _ _
    linarith
  have := isProbabilityMeasure_convFin_const μ r
  have := isProbabilityMeasure_convFin_const μ s
  have hsplit := conv_singleton_le_split (convFin r (fun _ => μ)) (convFin s (fun _ => μ)) hEF
  rw [← convFin_add, hrs] at hsplit
  have hreal : (convFin t (fun _ => μ) {k}).toReal ≤
      lconc (convFin s (fun _ => μ)) 1 * (convFin r (fun _ => μ) E).toReal +
      lconc (convFin r (fun _ => μ)) 1 * (convFin s (fun _ => μ) F).toReal := by
    have h := ENNReal.toReal_mono (by finiteness) hsplit
    rwa [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (lconc_nonneg _ _),
      ENNReal.toReal_ofReal (lconc_nonneg _ _)] at h
  -- the Chebyshev half
  set X : ℝ := max 1 (4 * B₂) * (t / max (t : ℝ) (((t : ℝ) - k / m) ^ 2)) with hX
  have hmaxpos : 0 < max (t : ℝ) (((t : ℝ) - k / m) ^ 2) := lt_max_of_lt_left htpos
  have hsqd : ((t : ℝ) - k / m) ^ 2 = 4 * δ ^ 2 / m ^ 2 := by
    rw [hδ, div_pow, sq_abs, hd]; field_simp; ring
  have hcheb : ∀ n : ℕ, (n : ℝ) ≤ t →
      (convFin n (fun _ => μ) {u : ℤ | δ ≤ |(u : ℝ) - n * m|}).toReal ≤ X := by
    intro n hn
    have := isProbabilityMeasure_convFin_const μ n
    set PE := (convFin n (fun _ => μ) {u : ℤ | δ ≤ |(u : ℝ) - n * m|}).toReal with hPE
    have hPE0 : 0 ≤ PE := ENNReal.toReal_nonneg
    have hPE1 : PE ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp [prob_le_one])
    have hc := convFin_tail_mul_sq_le hint n hδ0
    rw [hm] at hc
    have key : PE * max (t : ℝ) (((t : ℝ) - k / m) ^ 2) ≤ t * max 1 (4 * B₂) := by
      rw [mul_max_of_nonneg _ _ hPE0]
      refine max_le ?_ ?_
      · calc PE * t ≤ 1 * t := by gcongr
          _ ≤ t * max 1 (4 * B₂) := by rw [one_mul]; exact le_mul_of_one_le_right htpos.le (le_max_left _ _)
      · rw [hsqd]
        have h1 : PE * (4 * δ ^ 2 / m ^ 2) = 4 * (PE * δ ^ 2) / m ^ 2 := by ring
        rw [h1]
        calc 4 * (PE * δ ^ 2) / m ^ 2 ≤ 4 * (n * V) / m ^ 2 := by gcongr
          _ = 4 * n * (V / m ^ 2) := by ring
          _ ≤ 4 * t * B₂ := by gcongr
          _ ≤ t * max 1 (4 * B₂) := by
            rw [show 4 * (t : ℝ) * B₂ = t * (4 * B₂) by ring]
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) htpos.le
    rw [hX, ← mul_div_assoc, le_div_iff₀ hmaxpos]
    linarith
  have hPE := hcheb r hrt
  have hPF := hcheb s hst
  -- the Kesten halves
  have hKp := mul_lconc_nonneg hK hp
  have hLr : lconc (convFin r (fun _ => μ)) 1 ≤ 4 * K * p / Real.sqrt t := by
    refine (lconc_convFin_le hK hp hr1).trans ?_
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hr1)) (Real.sqrt_pos.2 htpos)]
    have : Real.sqrt t ≤ 2 * Real.sqrt r := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
        ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt htr
    nlinarith
  have hLs : lconc (convFin s (fun _ => μ)) 1 ≤ 4 * K * p / Real.sqrt t := by
    refine (lconc_convFin_le hK hp hs1).trans ?_
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hs1)) (Real.sqrt_pos.2 htpos)]
    have : Real.sqrt t ≤ 2 * Real.sqrt s := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
        ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hts
    nlinarith
  have hLr0 := lconc_nonneg (convFin r (fun _ => μ)) 1
  have hLs0 := lconc_nonneg (convFin s (fun _ => μ)) 1
  have hX0 : 0 ≤ X := le_trans ENNReal.toReal_nonneg hPE
  calc (convFin t (fun _ => μ) {k}).toReal
      ≤ lconc (convFin s (fun _ => μ)) 1 * X + lconc (convFin r (fun _ => μ)) 1 * X := by
        refine hreal.trans (add_le_add ?_ ?_)
        · exact mul_le_mul_of_nonneg_left hPE hLs0
        · exact mul_le_mul_of_nonneg_left hPF hLr0
    _ ≤ 4 * K * p / Real.sqrt t * X + 4 * K * p / Real.sqrt t * X := by gcongr
    _ = _ := by rw [hX]; ring

end OneTime

/-! ## Strictly increasing walks hit a level at most once -/

/-- For positive integer increments, `U(k) = ∑_{t ≥ 1} P(S_t = k) ≤ 1`: on the almost sure
event that all increments are `≥ 1` the partial sums are strictly increasing, so the events
`{S_t = k}` are disjoint. -/
theorem _root_.PGM.renewal_hits_le_one (μ : Measure ℤ) [IsProbabilityMeasure μ]
    (hpos : μ (Set.Iic 0) = 0) (k : ℤ) :
    ∑' t : ℕ, convFin (t + 1) (fun _ => μ) {k} ≤ 1 := by
  obtain ⟨Ω, _, P, X, hX, hlaw, hind, hP⟩ := exists_iid ℕ μ
  have hlaw' : ∀ i, P.map (X i) = μ := fun i => (hlaw i).map_eq
  set S : ℕ → Ω → ℤ := fun n ω => ∑ i ∈ Finset.range n, X i ω with hSdef
  have hSm : ∀ n, Measurable (S n) := fun n => Finset.measurable_sum _ fun i _ => hX i
  have hterm : ∀ t : ℕ, convFin (t + 1) (fun _ => μ) {k} = P (S (t + 1) ⁻¹' {k}) := fun t => by
    rw [← map_sum_range_eq_convFin hX hind hlaw' (t + 1),
      Measure.map_apply (hSm _) MeasurableSet.of_discrete]
  set G : Set Ω := ⋂ i, X i ⁻¹' Set.Ici 1 with hGdef
  have hGm : MeasurableSet G := MeasurableSet.iInter fun i => hX i measurableSet_Ici
  have hGc : P Gᶜ = 0 := by
    have : Gᶜ = ⋃ i, X i ⁻¹' Set.Iic 0 := by
      ext ω
      simp only [hGdef, Set.compl_iInter, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_Ici, Set.mem_Iic, not_le]
      exact exists_congr fun i => by omega
    rw [this]
    exact measure_iUnion_null fun i => by
      rw [← Measure.map_apply (hX i) measurableSet_Iic, hlaw' i, hpos]
  have hmono : ∀ ω ∈ G, StrictMono (fun n => S n ω) := fun ω hω =>
    strictMono_nat_of_lt_succ fun n => by
      have h1 : 1 ≤ X n ω := Set.mem_iInter.1 hω n
      simp only [hSdef, Finset.sum_range_succ]
      omega
  have hdisj : Pairwise (Function.onFun Disjoint fun t : ℕ => S (t + 1) ⁻¹' {k} ∩ G) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨ha, hωG⟩ ⟨hb, -⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    exact hab (Nat.succ_injective ((hmono ω hωG).injective (ha.trans hb.symm)))
  calc ∑' t : ℕ, convFin (t + 1) (fun _ => μ) {k}
      = ∑' t : ℕ, P (S (t + 1) ⁻¹' {k} ∩ G) := by
        congr 1; funext t; rw [hterm, measure_inter_conull hGc]
    _ = P (⋃ t : ℕ, S (t + 1) ⁻¹' {k} ∩ G) :=
        (measure_iUnion hdisj fun t => ((hSm _) MeasurableSet.of_discrete).inter hGm).symm
    _ ≤ 1 := prob_le_one

/-! ## Moments of a law on `ℤ` as series over atoms -/

theorem integrable_of_summable_atoms {μ : Measure ℤ} [IsFiniteMeasure μ] {f : ℤ → ℝ}
    (hf : Summable (fun q => |f q| * μ.real {q})) : Integrable f μ := by
  rw [← Measure.sum_smul_dirac μ]
  refine integrable_sum_dirac (fun q => measure_ne_top μ {q}) ?_
  simpa [measureReal_def, mul_comm] using hf

theorem integral_eq_tsum_atoms {μ : Measure ℤ} {f : ℤ → ℝ} (hf : Integrable f μ) :
    ∫ q, f q ∂μ = ∑' q, f q * μ.real {q} := by
  rw [integral_countable hf]
  simp [smul_eq_mul, mul_comm]

end LocalCountBase

end

end PGM
