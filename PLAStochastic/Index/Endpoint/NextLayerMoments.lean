import PLAStochastic.Index.Model.IIDPairs
import PLAStochastic.Index.Model.GapLaw
import PLAStochastic.ForMathlib.Probability.StoppedSum.StoppedMoments
import PLAStochastic.ForMathlib.Probability.StoppedSum.GeometricTailMoments

/-!
# Moments of the next-layer first pair

Let `Z` be an iid pair sequence (`IIDPairs P Z`) with gaps `X t = (Z t).1` satisfying
`GapLaw P X μ σ κ` and counts `N t = (Z t).2`.  Write `T = pairSegLen eps (seq Z ·)` for
the first segment length (definitionally `layerSegLen eps X`), `Tn = T.toNat` as a real,
`C = E Tn`, and `V = stoppedSumE (centred X μ) T` for the centred stopped gap sum.
The first pair of the next layer is `(g', N') = firstBlock eps (seq Z ·)`.

* `firstBlock_fst_eq`, `firstBlock_snd_eq`: pathwise, `g' = μ Tn + V` and
  `N' = m Tn + ∑_{t < T} (N t - m)`.
* `integral_stoppedGap_sq_le`, `integral_abs_stoppedGap_cube_le`: `E V² ≤ σ² C` and
  `E|V|³ ≤ 3σ³B + κC`.
* `memLp_nextGap`, `integral_nextGap`: `g' ∈ L³` and `E g' = μ C`.
* `integral_nextGap_sub_sq_eq`, `abs_integral_nextGap_sub_sq_sub_le`: the variance of `g'`
  is `μ² Var Tn + 2μ E[(Tn - C) V] + E V²`, with the resulting two-sided bound.
* `integral_abs_nextGap_sub_cube_le`, `integral_abs_toNat_sub_cube_le`: third moments.
* `integral_nextCount`, `memLp_nextCount`, `integral_nextCount_sq_le`: moments of `N'`.

The stopped-sum moment bounds of `PLAStochastic.ForMathlib.Probability.StoppedSum.StoppedMoments` are stated in `ℝ≥0∞`; the general
lemmas `stoppedSumE_sq_integral_le`, `stoppedSumE_cube_integral_le` and
`integral_stoppedSumE_eq_zero` turn them into real integrability and integral bounds.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## Real forms of the stopped-sum bounds -/

section Stopped

variable {F : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {T : Ω → ℕ∞}

theorem measurable_stoppedSumE (hY : ∀ t, Measurable (Y t)) (hT : Measurable T) :
    Measurable (stoppedSumE Y T) := by
  have hm : Measurable (fun p : Ω × ℕ => partialSum Y p.2 p.1) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun ω => ∑ t ∈ range n, Y t ω
      exact Finset.measurable_sum _ fun t _ => hY t
  exact hm.comp (measurable_id.prodMk ((Measurable.of_discrete (f := ENat.toNat)).comp hT))

/-- `E T = E Tn` in `ℝ≥0∞` when `T` is almost surely finite. -/
theorem lintegral_enat_eq_ofReal_integral (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤)
    (hint : Integrable (fun ω => ((T ω).toNat : ℝ)) P) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ∂P = ENNReal.ofReal (∫ ω, ((T ω).toNat : ℝ) ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => Nat.cast_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with ω hω
  have hn : T ω = ((T ω).toNat : ℕ∞) := (ENat.natCast_toNat hω).symm
  rw [ENNReal.ofReal_natCast]
  conv_lhs => rw [hn]
  simp

/-- `0 ≤ E Tn`. -/
theorem integral_toNat_nonneg (T : Ω → ℕ∞) : 0 ≤ ∫ ω, ((T ω).toNat : ℝ) ∂P :=
  integral_nonneg fun _ => Nat.cast_nonneg _

/-- A real function whose absolute cube is integrable is in `L³`. -/
theorem memLp_three_of_integrable_abs_cube {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (h3 : Integrable (fun ω => |f ω| ^ 3) P) : MemLp f 3 P := by
  rw [← integrable_norm_rpow_iff hf (by norm_num) (by norm_num)]
  refine h3.congr (Eventually.of_forall fun ω => ?_)
  simp [Real.norm_eq_abs]

/-- Real form of `lintegral_stoppedSumE_sq_le`: `S_T²` is integrable and
`E[S_T²] ≤ σsq E Tn`. -/
theorem stoppedSumE_sq_integral_le [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hY2 : ∀ t, MemLp (Y t) 2 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {σsq : ℝ}
    (hσ : ∀ t, ∫ ω, Y t ω ^ 2 ∂P ≤ σsq) (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤)
    (hint : Integrable (fun ω => ((T ω).toNat : ℝ)) P) :
    Integrable (fun ω => stoppedSumE Y T ω ^ 2) P ∧
      ∫ ω, stoppedSumE Y T ω ^ 2 ∂P ≤ σsq * ∫ ω, ((T ω).toNat : ℝ) ∂P := by
  have hσ0 : 0 ≤ σsq := le_trans (integral_nonneg fun _ => sq_nonneg _) (hσ 0)
  have hC0 := integral_toNat_nonneg (P := P) T
  have hbound : ∫⁻ ω, ENNReal.ofReal (stoppedSumE Y T ω ^ 2) ∂P ≤
      ENNReal.ofReal (σsq * ∫ ω, ((T ω).toNat : ℝ) ∂P) := by
    rw [ENNReal.ofReal_mul hσ0, ← lintegral_enat_eq_ofReal_integral hfin hint]
    exact lintegral_stoppedSumE_sq_le h hT hY2 hY0 hσ hfin
  have hmeas : Measurable fun ω => stoppedSumE Y T ω ^ 2 :=
    (measurable_stoppedSumE h.measurable' (measurable_T_of_stopping hT)).pow_const 2
  refine ⟨⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun _ => sq_nonneg _)).2 (hbound.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hσ0 hC0) hbound

/-- Real form of `lintegral_stoppedSumE_cube_le`: `|S_T|³` is integrable and
`E|S_T|³ ≤ 3σ³B + κ E Tn`. -/
theorem stoppedSumE_cube_integral_le [IsProbabilityMeasure P] (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hY3 : ∀ t, MemLp (Y t) 3 P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {σ κ B : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ t, ∫ ω, Y t ω ^ 2 ∂P ≤ σ ^ 2) (hκ : ∀ t, ∫ ω, |Y t ω| ^ 3 ∂P ≤ κ)
    (hB : ∀ n, ∑ t ∈ range n, Real.sqrt t * Real.sqrt (P.real {ω | (t : ℕ∞) < T ω}) ≤ B)
    (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤) (hint : Integrable (fun ω => ((T ω).toNat : ℝ)) P) :
    Integrable (fun ω => |stoppedSumE Y T ω| ^ 3) P ∧
      ∫ ω, |stoppedSumE Y T ω| ^ 3 ∂P ≤ 3 * σ ^ 3 * B + κ * ∫ ω, ((T ω).toNat : ℝ) ∂P := by
  have hκ0 : 0 ≤ κ := le_trans (integral_nonneg fun _ => by positivity) (hκ 0)
  have hB0 : 0 ≤ B := le_trans (by simp) (hB 0)
  have hC0 := integral_toNat_nonneg (P := P) T
  have hbound : ∫⁻ ω, ENNReal.ofReal (|stoppedSumE Y T ω| ^ 3) ∂P ≤
      ENNReal.ofReal (3 * σ ^ 3 * B + κ * ∫ ω, ((T ω).toNat : ℝ) ∂P) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hκ0,
      ← lintegral_enat_eq_ofReal_integral hfin hint]
    exact lintegral_stoppedSumE_cube_le h hT hY3 hY0 hσ0 hσ hκ hB hfin
  have hmeas : Measurable fun ω => |stoppedSumE Y T ω| ^ 3 :=
    (continuous_abs.measurable.comp
      (measurable_stoppedSumE h.measurable' (measurable_T_of_stopping hT))).pow_const 3
  refine ⟨⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun _ => by positivity)).2
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
    hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

/-- Wald's identity for centred increments: `E[S_T] = 0` when `E T < ∞`. -/
theorem integral_stoppedSumE_eq_zero (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hint : ∀ t, Integrable (Y t) P) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0) {c : ℝ}
    (habs : ∀ t, ∫ ω, |Y t ω| ∂P ≤ c) (hTfin : ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≠ ∞) :
    ∫ ω, stoppedSumE Y T ω ∂P = 0 := by
  have heq : (fun ω => stoppedSumE Y T ω) =ᵐ[P]
      fun ω => ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω := by
    filter_upwards [wald_ae_lt_top (measurable_T_of_stopping hT) hTfin] with ω hω
    have hn : T ω = ((T ω).toNat : ℕ∞) := (ENat.natCast_toNat hω.ne).symm
    exact ((wald_hasSum_indicator Y hn).tsum_eq).symm
  rw [integral_congr_ae heq, wald_integral h hT hint hY0 habs hTfin, zero_mul]

end Stopped

/-! ## Elementary inequalities -/

omit mΩ in
theorem abs_add_pow_three_le_four (a b : ℝ) : |a + b| ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have h1 : |a + b| ^ 3 ≤ (|a| + |b|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (abs_add_le a b) 3
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (|a| - |b|))]

/-- `E|Tn - C|³ ≤ 4 (M3 + C³)` for a nonnegative `C` and `E Tn³ ≤ M3`. -/
theorem integral_abs_toNat_sub_cube_le [IsProbabilityMeasure P] (T : Ω → ℕ∞)
    (hT3 : Integrable (fun ω => ((T ω).toNat : ℝ) ^ 3) P) {C M3 : ℝ} (hC0 : 0 ≤ C)
    (hM3 : ∫ ω, ((T ω).toNat : ℝ) ^ 3 ∂P ≤ M3) :
    ∫ ω, |((T ω).toNat : ℝ) - C| ^ 3 ∂P ≤ 4 * (M3 + C ^ 3) := by
  have hpt : ∀ ω, |((T ω).toNat : ℝ) - C| ^ 3 ≤ 4 * (((T ω).toNat : ℝ) ^ 3 + C ^ 3) := by
    intro ω
    have := abs_add_pow_three_le_four ((T ω).toNat : ℝ) (-C)
    rwa [← sub_eq_add_neg, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (T ω).toNat),
      abs_of_nonneg hC0] at this
  have hint : Integrable (fun ω => 4 * (((T ω).toNat : ℝ) ^ 3 + C ^ 3)) P :=
    (hT3.add (integrable_const _)).const_mul 4
  calc ∫ ω, |((T ω).toNat : ℝ) - C| ^ 3 ∂P
      ≤ ∫ ω, 4 * (((T ω).toNat : ℝ) ^ 3 + C ^ 3) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hint
          (Eventually.of_forall hpt)
    _ = 4 * (∫ ω, ((T ω).toNat : ℝ) ^ 3 ∂P + C ^ 3) := by
        rw [integral_const_mul, integral_add hT3 (integrable_const _), integral_const]
        simp
    _ ≤ 4 * (M3 + C ^ 3) := by linarith


/-! ## Moments of a decomposition `g = μ Tn + V` -/

section Decomp

variable {g Tn V : Ω → ℝ} {μ C : ℝ}

/-- Variance expansion for `g = μ Tn + V`. -/
theorem integral_sub_sq_eq_of_decomp (hg : ∀ ω, g ω = μ * Tn ω + V ω) (hTn : MemLp Tn 2 P)
    (hV : MemLp V 2 P) [IsFiniteMeasure P] :
    ∫ ω, (g ω - μ * C) ^ 2 ∂P = μ ^ 2 * ∫ ω, (Tn ω - C) ^ 2 ∂P +
      2 * μ * ∫ ω, (Tn ω - C) * V ω ∂P + ∫ ω, V ω ^ 2 ∂P := by
  have hTC : MemLp (fun ω => Tn ω - C) 2 P := hTn.sub (memLp_const C)
  have hpt : ∀ ω, (g ω - μ * C) ^ 2 =
      μ ^ 2 * (Tn ω - C) ^ 2 + (2 * μ * ((Tn ω - C) * V ω) + V ω ^ 2) := fun ω => by
    rw [hg]; ring
  have hTV : Integrable (fun ω => (Tn ω - C) * V ω) P := hTC.integrable_mul hV
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (f := fun ω => μ ^ 2 * (Tn ω - C) ^ 2)
      (g := fun ω => 2 * μ * ((Tn ω - C) * V ω) + V ω ^ 2)
      (hTC.integrable_sq.const_mul _) ((hTV.const_mul _).add hV.integrable_sq),
    integral_add (f := fun ω => 2 * μ * ((Tn ω - C) * V ω)) (g := fun ω => V ω ^ 2)
      (hTV.const_mul _) hV.integrable_sq, integral_const_mul, integral_const_mul]
  ring

/-- Two-sided variance bound for `g = μ Tn + V` with `E V² ≤ s`. -/
theorem abs_integral_sub_sq_sub_le_of_decomp [IsProbabilityMeasure P]
    (hg : ∀ ω, g ω = μ * Tn ω + V ω) (hTn : MemLp Tn 2 P) (hV : MemLp V 2 P) (hμ : 0 ≤ μ)
    {s : ℝ} (hs : ∫ ω, V ω ^ 2 ∂P ≤ s) :
    |∫ ω, (g ω - μ * C) ^ 2 ∂P - μ ^ 2 * ∫ ω, (Tn ω - C) ^ 2 ∂P| ≤
      2 * μ * Real.sqrt (∫ ω, (Tn ω - C) ^ 2 ∂P) * Real.sqrt s + s := by
  have hTC : MemLp (fun ω => Tn ω - C) 2 P := hTn.sub (memLp_const C)
  rw [integral_sub_sq_eq_of_decomp hg hTn hV, add_assoc, add_sub_cancel_left]
  set a := ∫ ω, (Tn ω - C) ^ 2 ∂P
  set b := ∫ ω, (Tn ω - C) * V ω ∂P
  set c := ∫ ω, V ω ^ 2 ∂P
  have ha : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ c := integral_nonneg fun _ => sq_nonneg _
  have hb : |b| ≤ Real.sqrt a * Real.sqrt s := by
    rw [← Real.sqrt_mul ha]
    exact Real.abs_le_sqrt ((sq_integral_mul_le hTC hV).trans
      (mul_le_mul_of_nonneg_left hs ha))
  calc |2 * μ * b + c| ≤ |2 * μ * b| + |c| := abs_add_le _ _
    _ = 2 * μ * |b| + c := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * μ), abs_of_nonneg hc]
    _ ≤ 2 * μ * (Real.sqrt a * Real.sqrt s) + s := by
        gcongr
    _ = 2 * μ * Real.sqrt a * Real.sqrt s + s := by ring

/-- Third absolute central moment for `g = μ Tn + V`. -/
theorem integral_abs_sub_cube_le_of_decomp [IsFiniteMeasure P]
    (hg : ∀ ω, g ω = μ * Tn ω + V ω) (hTn : MemLp Tn 3 P)
    (hV : Integrable (fun ω => |V ω| ^ 3) P) (hμ : 0 ≤ μ) :
    ∫ ω, |g ω - μ * C| ^ 3 ∂P ≤
      4 * μ ^ 3 * ∫ ω, |Tn ω - C| ^ 3 ∂P + 4 * ∫ ω, |V ω| ^ 3 ∂P := by
  have hTC : Integrable (fun ω => |Tn ω - C| ^ 3) P :=
    memLp_three_integrable_abs_cube (hTn.sub (memLp_const C))
  have hpt : ∀ ω, |g ω - μ * C| ^ 3 ≤ 4 * μ ^ 3 * |Tn ω - C| ^ 3 + 4 * |V ω| ^ 3 := by
    intro ω
    have h1 := abs_add_pow_three_le_four (μ * (Tn ω - C)) (V ω)
    rw [abs_mul, abs_of_nonneg hμ, mul_pow] at h1
    rw [hg, show μ * Tn ω + V ω - μ * C = μ * (Tn ω - C) + V ω by ring]
    linarith
  calc ∫ ω, |g ω - μ * C| ^ 3 ∂P
      ≤ ∫ ω, (4 * μ ^ 3 * |Tn ω - C| ^ 3 + 4 * |V ω| ^ 3) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
          ((hTC.const_mul _).add (hV.const_mul _)) (Eventually.of_forall hpt)
    _ = 4 * μ ^ 3 * ∫ ω, |Tn ω - C| ^ 3 ∂P + 4 * ∫ ω, |V ω| ^ 3 ∂P := by
        rw [integral_add (f := fun ω => 4 * μ ^ 3 * |Tn ω - C| ^ 3)
          (g := fun ω => 4 * |V ω| ^ 3) (hTC.const_mul _) (hV.const_mul _), integral_const_mul,
          integral_const_mul]

end Decomp

/-! ## The next-layer first pair -/

section LayerStep

variable {Z : ℕ → Ω → ℝ × ℕ} {eps μ σ κ C : ℝ}

omit mΩ in
/-- Pathwise decomposition of the next-layer first gap: `g' = μ Tn + V`. -/
theorem firstBlock_fst_eq (Z : ℕ → Ω → ℝ × ℕ) (eps μ : ℝ) (ω : Ω) :
    (firstBlock eps (seq Z ω)).1 = μ * ((pairSegLen eps (seq Z ω)).toNat : ℝ) +
      stoppedSumE (centred (fun t ω => (Z t ω).1) μ) (fun ω => pairSegLen eps (seq Z ω)) ω := by
  simp only [firstBlock, stoppedSumE, partialSum, centred, Prod.fst_sum, seq, sum_sub_distrib,
    sum_const, card_range, nsmul_eq_mul]
  ring

omit mΩ in
/-- Pathwise decomposition of the next-layer first count: `N' = m Tn + ∑_{t<T} (N t - m)`. -/
theorem firstBlock_snd_eq (Z : ℕ → Ω → ℝ × ℕ) (eps m : ℝ) (ω : Ω) :
    ((firstBlock eps (seq Z ω)).2 : ℝ) = m * ((pairSegLen eps (seq Z ω)).toNat : ℝ) +
      stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m) (fun ω => pairSegLen eps (seq Z ω)) ω := by
  simp only [firstBlock, stoppedSumE, partialSum, Prod.snd_sum, seq, Nat.cast_sum,
    sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  ring

theorem measurable_toNat_pairSegLen (h : IIDPairs P Z) (eps : ℝ) :
    Measurable fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) :=
  (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp
    ((measurable_pairSegLen eps).comp (measurable_seq h.measurable))

/-- `Tn ∈ L²` from `E Tn² < ∞`. -/
theorem memLp_toNat_pairSegLen_two (h : IIDPairs P Z)
    (hT2 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2) P) :
    MemLp (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) 2 P :=
  (memLp_two_iff_integrable_sq (measurable_toNat_pairSegLen h eps).aestronglyMeasurable).2 hT2

/-- `Tn ∈ L³` from `E Tn³ < ∞`. -/
theorem memLp_toNat_pairSegLen_three (h : IIDPairs P Z)
    (hT3 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 3) P) :
    MemLp (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) 3 P :=
  memLp_three_of_integrable_abs_cube (measurable_toNat_pairSegLen h eps).aestronglyMeasurable
    (hT3.congr (Eventually.of_forall fun ω => by simp))

/-- The centred gaps have independent increments for the pair filtration. -/
theorem IIDPairs.indepIncrements_centred (h : IIDPairs P Z) (μ : ℝ) :
    IndepIncrements P (pairFiltration Z h.measurable) (centred (fun t ω => (Z t ω).1) μ) :=
  h.indepIncrements Prod.fst measurable_fst μ

/-- (iii) `V` is square integrable and `E V² ≤ σ² C`. -/
theorem integral_stoppedGap_sq_le [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) :
    Integrable (fun ω => stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
        (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2) P ∧
      ∫ ω, stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
        (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2 ∂P ≤ σ ^ 2 * C := by
  subst hC
  exact stoppedSumE_sq_integral_le (h.indepIncrements_centred μ)
    (fun t => pairSegLen_lt_measurable h.measurable eps t)
    (fun t => (hX.memLp_centred t).mono_exponent (by norm_num)) hX.integral_centred
    (fun t => (hX.integral_centred_sq t).le) hfin hTn

/-- (iii) `|V|³` is integrable and `E|V|³ ≤ 3σ³B + κC`. -/
theorem integral_abs_stoppedGap_cube_le [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) {Bh : ℝ}
    (hB : ∀ n, ∑ t ∈ range n, Real.sqrt t *
      Real.sqrt (P.real {ω | (t : ℕ∞) < pairSegLen eps (seq Z ω)}) ≤ Bh) :
    Integrable (fun ω => |stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
        (fun ω => pairSegLen eps (seq Z ω)) ω| ^ 3) P ∧
      ∫ ω, |stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
        (fun ω => pairSegLen eps (seq Z ω)) ω| ^ 3 ∂P ≤ 3 * σ ^ 3 * Bh + κ * C := by
  subst hC
  exact stoppedSumE_cube_integral_le (h.indepIncrements_centred μ)
    (fun t => pairSegLen_lt_measurable h.measurable eps t) hX.memLp_centred
    hX.integral_centred hX.sigma_pos.le (fun t => (hX.integral_centred_sq t).le)
    hX.integral_centred_abs_cube hB hfin hTn

theorem measurable_stoppedSumE_pairSegLen (h : IIDPairs P Z) (eps : ℝ) {Y : ℕ → Ω → ℝ}
    (hY : ∀ t, Measurable (Y t)) :
    Measurable (stoppedSumE Y (fun ω => pairSegLen eps (seq Z ω))) :=
  measurable_stoppedSumE hY ((measurable_pairSegLen eps).comp (measurable_seq h.measurable))

/-- `V ∈ L²`. -/
theorem memLp_stoppedGap_two [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P) :
    MemLp (stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
      (fun ω => pairSegLen eps (seq Z ω))) 2 P :=
  (memLp_two_iff_integrable_sq (measurable_stoppedSumE_pairSegLen h eps
    (h.indepIncrements_centred μ).measurable').aestronglyMeasurable).2
    (integral_stoppedGap_sq_le h hX hfin hTn rfl).1

/-- Wald: `E V = 0`. -/
theorem integral_stoppedGap [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P) :
    ∫ ω, stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
      (fun ω => pairSegLen eps (seq Z ω)) ω ∂P = 0 := by
  have habs : ∀ t, ∫ ω, |centred (fun t ω => (Z t ω).1) μ t ω| ∂P ≤
      ∫ ω, |centred (fun t ω => (Z t ω).1) μ 0 ω| ∂P := fun t =>
    le_of_eq ((hX.iid.ident t).comp (u := fun x : ℝ => |x - μ|) (by fun_prop)).integral_eq
  exact integral_stoppedSumE_eq_zero (h.indepIncrements_centred μ)
    (fun t => pairSegLen_lt_measurable h.measurable eps t)
    (fun t => (hX.memLp_centred t).integrable (by norm_num)) hX.integral_centred habs
    ((lintegral_enat_eq_ofReal_integral hfin hTn).trans_ne ENNReal.ofReal_ne_top)

/-- (ii) The next-layer first gap is in `L³`. -/
theorem memLp_nextGap [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hT3 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 3) P) {Bh : ℝ}
    (hB : ∀ n, ∑ t ∈ range n, Real.sqrt t *
      Real.sqrt (P.real {ω | (t : ℕ∞) < pairSegLen eps (seq Z ω)}) ≤ Bh) :
    MemLp (fun ω => (firstBlock eps (seq Z ω)).1) 3 P := by
  have hTn3 := memLp_toNat_pairSegLen_three h hT3
  have hV3 : MemLp (stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
      (fun ω => pairSegLen eps (seq Z ω))) 3 P :=
    memLp_three_of_integrable_abs_cube (measurable_stoppedSumE_pairSegLen h eps
      (h.indepIncrements_centred μ).measurable').aestronglyMeasurable
      (integral_abs_stoppedGap_cube_le h hX hfin (hTn3.integrable (by norm_num)) rfl hB).1
  rw [funext (firstBlock_fst_eq Z eps μ)]
  exact (hTn3.const_mul μ).add hV3

/-- (ii) `E g' = μ C`. -/
theorem integral_nextGap [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) :
    ∫ ω, (firstBlock eps (seq Z ω)).1 ∂P = μ * C := by
  subst hC
  rw [integral_congr_ae (Eventually.of_forall (firstBlock_fst_eq Z eps μ)),
    integral_add (hTn.const_mul μ) ((memLp_stoppedGap_two h hX hfin hTn).integrable one_le_two),
    integral_const_mul, integral_stoppedGap h hX hfin hTn, add_zero]

/-- (iv) Variance expansion of the next-layer first gap (for any centring constant `C`). -/
theorem integral_nextGap_sub_sq_eq [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hT2 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2) P) (C : ℝ) :
    ∫ ω, ((firstBlock eps (seq Z ω)).1 - μ * C) ^ 2 ∂P =
      μ ^ 2 * ∫ ω, (((pairSegLen eps (seq Z ω)).toNat : ℝ) - C) ^ 2 ∂P +
      2 * μ * ∫ ω, (((pairSegLen eps (seq Z ω)).toNat : ℝ) - C) *
        stoppedSumE (centred (fun t ω => (Z t ω).1) μ) (fun ω => pairSegLen eps (seq Z ω)) ω ∂P +
      ∫ ω, stoppedSumE (centred (fun t ω => (Z t ω).1) μ)
        (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2 ∂P := by
  have hTn2 := memLp_toNat_pairSegLen_two h hT2
  exact integral_sub_sq_eq_of_decomp (firstBlock_fst_eq Z eps μ) hTn2
    (memLp_stoppedGap_two h hX hfin (hTn2.integrable one_le_two))

/-- (iv) Two-sided variance bound for the next-layer first gap. -/
theorem abs_integral_nextGap_sub_sq_sub_le [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hT2 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) :
    |∫ ω, ((firstBlock eps (seq Z ω)).1 - μ * C) ^ 2 ∂P -
        μ ^ 2 * ∫ ω, (((pairSegLen eps (seq Z ω)).toNat : ℝ) - C) ^ 2 ∂P| ≤
      2 * μ * Real.sqrt (∫ ω, (((pairSegLen eps (seq Z ω)).toNat : ℝ) - C) ^ 2 ∂P) *
        Real.sqrt (σ ^ 2 * C) + σ ^ 2 * C := by
  have hTn2 := memLp_toNat_pairSegLen_two h hT2
  have hTn := hTn2.integrable one_le_two
  exact abs_integral_sub_sq_sub_le_of_decomp (firstBlock_fst_eq Z eps μ) hTn2
    (memLp_stoppedGap_two h hX hfin hTn) hX.mu_pos.le (integral_stoppedGap_sq_le h hX hfin hTn hC).2

/-- (v) Third absolute central moment of the next-layer first gap. -/
theorem integral_abs_nextGap_sub_cube_le [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hX : GapLaw P (fun t ω => (Z t ω).1) μ σ κ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hT3 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 3) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) {Bh : ℝ}
    (hB : ∀ n, ∑ t ∈ range n, Real.sqrt t *
      Real.sqrt (P.real {ω | (t : ℕ∞) < pairSegLen eps (seq Z ω)}) ≤ Bh) :
    ∫ ω, |(firstBlock eps (seq Z ω)).1 - μ * C| ^ 3 ∂P ≤
      4 * μ ^ 3 * ∫ ω, |((pairSegLen eps (seq Z ω)).toNat : ℝ) - C| ^ 3 ∂P +
        4 * (3 * σ ^ 3 * Bh + κ * C) := by
  have hTn3 := memLp_toNat_pairSegLen_three h hT3
  have hV := integral_abs_stoppedGap_cube_le h hX hfin (hTn3.integrable (by norm_num)) hC hB
  have := integral_abs_sub_cube_le_of_decomp (C := C) (firstBlock_fst_eq Z eps μ) hTn3 hV.1
    hX.mu_pos.le
  linarith [hV.2]

/-! ### Counts -/

theorem measurable_natCast_snd : Measurable fun p : ℝ × ℕ => (p.2 : ℝ) :=
  (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp measurable_snd

/-- The count components of an iid pair sequence, as reals, are iid. -/
theorem IIDPairs.snd (h : IIDPairs P Z) : IIDSeq P (fun t ω => ((Z t ω).2 : ℝ)) where
  measurable t := measurable_natCast_snd.comp (h.measurable t)
  indep := h.indep.comp (fun _ p => (p.2 : ℝ)) (fun _ => measurable_natCast_snd)
  ident t := (h.ident t).comp measurable_natCast_snd

/-- The centred counts have independent increments for the pair filtration. -/
theorem IIDPairs.indepIncrements_count (h : IIDPairs P Z) (m : ℝ) :
    IndepIncrements P (pairFiltration Z h.measurable) (fun t ω => ((Z t ω).2 : ℝ) - m) :=
  h.indepIncrements (fun p => (p.2 : ℝ)) measurable_natCast_snd m

/-- The stopped centred count sum `W = ∑_{t<T} (N t - m)` is square integrable and
`E W² ≤ E N² · C`. -/
theorem integral_stoppedCount_sq_le [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hN2 : MemLp (fun ω => ((Z 0 ω).2 : ℝ)) 2 P) {m s2 : ℝ}
    (hm : m = ∫ ω, ((Z 0 ω).2 : ℝ) ∂P) (hs2 : s2 = ∫ ω, ((Z 0 ω).2 : ℝ) ^ 2 ∂P)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) :
    Integrable (fun ω => stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
        (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2) P ∧
      ∫ ω, stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
        (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2 ∂P ≤ s2 * C := by
  subst hC
  have hN := h.snd
  have hN1 : Integrable (fun ω => ((Z 0 ω).2 : ℝ)) P := hN2.integrable one_le_two
  have hvar : ∫ ω, (((Z 0 ω).2 : ℝ) - m) ^ 2 ∂P = s2 - m ^ 2 := by
    have e : ∀ ω, (((Z 0 ω).2 : ℝ) - m) ^ 2 =
        ((Z 0 ω).2 : ℝ) ^ 2 + (-(2 * m) * ((Z 0 ω).2 : ℝ) + m ^ 2) := fun ω => by ring
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_add (f := fun ω => ((Z 0 ω).2 : ℝ) ^ 2)
        (g := fun ω => -(2 * m) * ((Z 0 ω).2 : ℝ) + m ^ 2)
        hN2.integrable_sq ((hN1.const_mul _).add (integrable_const _)),
      integral_add (f := fun ω => -(2 * m) * ((Z 0 ω).2 : ℝ)) (g := fun _ => m ^ 2)
        (hN1.const_mul _) (integrable_const _), integral_const_mul, integral_const, ← hm, ← hs2]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  have hY2 : ∀ t, MemLp (fun ω => ((Z t ω).2 : ℝ) - m) 2 P := fun t =>
    ((hN.memLp_iff t).2 hN2).sub (memLp_const m)
  have hY0 : ∀ t, ∫ ω, (((Z t ω).2 : ℝ) - m) ∂P = 0 := fun t => by
    rw [integral_sub ((hN.memLp_iff t).2 hN2 |>.integrable one_le_two) (integrable_const m),
      hN.integral_eq t, ← hm]
    simp
  have hσ : ∀ t, ∫ ω, (((Z t ω).2 : ℝ) - m) ^ 2 ∂P ≤ s2 := fun t => by
    rw [hN.integral_sq_sub_eq t m, hvar]
    nlinarith [sq_nonneg m]
  exact stoppedSumE_sq_integral_le (h.indepIncrements_count m)
    (fun t => pairSegLen_lt_measurable h.measurable eps t) hY2 hY0 hσ hfin hTn

/-- `E N' = m C` (Wald). -/
theorem integral_nextCount [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hN2 : MemLp (fun ω => ((Z 0 ω).2 : ℝ)) 2 P) {m : ℝ}
    (hm : m = ∫ ω, ((Z 0 ω).2 : ℝ) ∂P)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hTn : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ)) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) :
    ∫ ω, ((firstBlock eps (seq Z ω)).2 : ℝ) ∂P = m * C := by
  have hN := h.snd
  have hW2 : MemLp (stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
      (fun ω => pairSegLen eps (seq Z ω))) 2 P :=
    (memLp_two_iff_integrable_sq (measurable_stoppedSumE_pairSegLen h eps
      (h.indepIncrements_count m).measurable').aestronglyMeasurable).2
      (integral_stoppedCount_sq_le h hN2 hm rfl hfin hTn rfl).1
  have habs : ∀ t, ∫ ω, |((Z t ω).2 : ℝ) - m| ∂P ≤ ∫ ω, |((Z 0 ω).2 : ℝ) - m| ∂P := fun t =>
    le_of_eq ((hN.ident t).comp (u := fun x : ℝ => |x - m|) (by fun_prop)).integral_eq
  have hW0 : ∫ ω, stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
      (fun ω => pairSegLen eps (seq Z ω)) ω ∂P = 0 := by
    refine integral_stoppedSumE_eq_zero (h.indepIncrements_count m)
      (fun t => pairSegLen_lt_measurable h.measurable eps t)
      (fun t => ((hN.memLp_iff t).2 hN2 |>.integrable one_le_two).sub (integrable_const m))
      (fun t => ?_) habs
      ((lintegral_enat_eq_ofReal_integral hfin hTn).trans_ne ENNReal.ofReal_ne_top)
    rw [integral_sub ((hN.memLp_iff t).2 hN2 |>.integrable one_le_two) (integrable_const m),
      hN.integral_eq t, ← hm]
    simp
  subst hC
  rw [integral_congr_ae (Eventually.of_forall (firstBlock_snd_eq Z eps m)),
    integral_add (hTn.const_mul m) (hW2.integrable one_le_two), integral_const_mul, hW0,
    add_zero]

/-- `N' ∈ L²`. -/
theorem memLp_nextCount [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hN2 : MemLp (fun ω => ((Z 0 ω).2 : ℝ)) 2 P)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hT2 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2) P) :
    MemLp (fun ω => ((firstBlock eps (seq Z ω)).2 : ℝ)) 2 P := by
  set m := ∫ ω, ((Z 0 ω).2 : ℝ) ∂P with hm
  have hTn2 := memLp_toNat_pairSegLen_two h hT2
  have hW2 : MemLp (stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
      (fun ω => pairSegLen eps (seq Z ω))) 2 P :=
    (memLp_two_iff_integrable_sq (measurable_stoppedSumE_pairSegLen h eps
      (h.indepIncrements_count m).measurable').aestronglyMeasurable).2
      (integral_stoppedCount_sq_le h hN2 hm rfl hfin (hTn2.integrable one_le_two) rfl).1
  rw [funext (firstBlock_snd_eq Z eps m)]
  exact (hTn2.const_mul m).add hW2

/-- (vi) `E N'² ≤ 2 s2 C + 2 m² M2`. -/
theorem integral_nextCount_sq_le [IsProbabilityMeasure P] (h : IIDPairs P Z)
    (hN2 : MemLp (fun ω => ((Z 0 ω).2 : ℝ)) 2 P) {m s2 : ℝ}
    (hm : m = ∫ ω, ((Z 0 ω).2 : ℝ) ∂P) (hs2 : s2 = ∫ ω, ((Z 0 ω).2 : ℝ) ^ 2 ∂P)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤)
    (hT2 : Integrable (fun ω => ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2) P)
    (hC : C = ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ∂P) {M2 : ℝ}
    (hM2 : ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2 ∂P ≤ M2) :
    ∫ ω, ((firstBlock eps (seq Z ω)).2 : ℝ) ^ 2 ∂P ≤ 2 * s2 * C + 2 * m ^ 2 * M2 := by
  have hTn := (memLp_toNat_pairSegLen_two h hT2).integrable one_le_two
  have hW := integral_stoppedCount_sq_le h hN2 hm hs2 hfin hTn hC
  have hpt : ∀ ω, ((firstBlock eps (seq Z ω)).2 : ℝ) ^ 2 ≤
      2 * m ^ 2 * ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2 +
        2 * stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
          (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2 := fun ω => by
    rw [firstBlock_snd_eq Z eps m ω]
    nlinarith [sq_nonneg (m * ((pairSegLen eps (seq Z ω)).toNat : ℝ) -
      stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m) (fun ω => pairSegLen eps (seq Z ω)) ω)]
  have hint : Integrable (fun ω => 2 * m ^ 2 * ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2 +
      2 * stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
        (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2) P :=
    (hT2.const_mul _).add (hW.1.const_mul _)
  calc ∫ ω, ((firstBlock eps (seq Z ω)).2 : ℝ) ^ 2 ∂P
      ≤ ∫ ω, (2 * m ^ 2 * ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2 +
          2 * stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
            (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = 2 * m ^ 2 * ∫ ω, ((pairSegLen eps (seq Z ω)).toNat : ℝ) ^ 2 ∂P +
          2 * ∫ ω, stoppedSumE (fun t ω => ((Z t ω).2 : ℝ) - m)
            (fun ω => pairSegLen eps (seq Z ω)) ω ^ 2 ∂P := by
        rw [integral_add (hT2.const_mul _) (hW.1.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * m ^ 2 * M2 + 2 * (s2 * C) := by
        gcongr
        exact hW.2
    _ = 2 * s2 * C + 2 * m ^ 2 * M2 := by ring

end LayerStep

end PGM
