import PLAStochastic.Index.CEPS.Output.Radial
import PLAStochastic.ForMathlib.MeasureTheory.Constructions.PiFactor

/-!
# Track O: grouping the insertions by their high part

`output-closure.md` (O4)–(O8). For an insertion sequence `c : Fin j → Fin n`, the
*high part* `outHigh c` keeps the counts different from one, and `outSingles c` is the set
of positions inserted exactly once. Since `mellinOp f = mellinScore f · f`
(`mellinScore_mul_self`), every monomial factors as
`outMon f (outCount c) x = (∏_l (mellinOp^[outHigh c l] f)(x_l)) · ∏_{l ∈ singles} ρ(x_l)`,
`ρ = mellinScore f` (`outMon_eq_high_mul`). Grouping the sequences by their high part `β`
keeps the signed sum of the single insertions,
`outCentred f j β x = ∑_{c : outHigh c = β} ∏_{l ∈ outSingles c} ρ(x_l)`
(`outMonSum_eq_sum_high`); absolute values are taken only after this grouping.

The high factors are absorbed into the product measure
`outMeasure f β = ⊗_l |mellinOp^[β l] f| dx` (`lintegral_mul_eq_outMeasure`), which gives
`lintegral_coneWeight_le`:
`∫ coneWeight ≤ ∑_{i ≤ r} |c_{r,i}| ∑_{β} ∫ 1_A |outCentred f i β| / (∑ x)^r d(outMeasure f β)`.
-/

noncomputable section

open Finset Set MeasureTheory Filter
open scoped ENNReal

namespace PGM

variable {n : ℕ}

/-- The high part of an insertion sequence: the counts different from one. -/
def outHigh {j : ℕ} (c : Fin j → Fin n) : Fin n → ℕ :=
  fun l => if outCount c l = 1 then 0 else outCount c l

/-- The positions inserted exactly once. -/
def outSingles {j : ℕ} (c : Fin j → Fin n) : Finset (Fin n) := {l | outCount c l = 1}

/-- The centred sum of single insertions attached to a high part `β`. -/
def outCentred (f : ℝ → ℝ) (j : ℕ) (β : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ c ∈ {c : Fin j → Fin n | outHigh c = β}, ∏ l ∈ outSingles c, mellinScore f (x l)

/-- The box containing all high parts of length-`j` insertion sequences. -/
def outBox (n j : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ => range (j + 1)

/-- The product of the finite measures `|mellinOp^[β l] f| dx`. -/
def outMeasure (f : ℝ → ℝ) (β : Fin n → ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun l => volume.withDensity fun x => ENNReal.ofReal |mellinOp^[β l] f x|

theorem outHigh_mem_outBox {j : ℕ} (c : Fin j → Fin n) : outHigh c ∈ outBox n j := by
  rw [outBox, Fintype.mem_piFinset]
  intro l
  rw [Finset.mem_range, outHigh]
  split_ifs
  · omega
  · exact Nat.lt_succ_of_le (outCount_le c l)

theorem outMon_eq_high_mul {f : ℝ → ℝ} (hpos : ∀ x, 0 ≤ f x) {j : ℕ} (c : Fin j → Fin n)
    (x : Fin n → ℝ) :
    outMon f (outCount c) x =
      (∏ l, mellinOp^[outHigh c l] f (x l)) * ∏ l ∈ outSingles c, mellinScore f (x l) := by
  classical
  rw [outSingles, Finset.prod_filter, outMon, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [outHigh]
  split_ifs with h
  · rw [h, Function.iterate_one, Function.iterate_zero, id, mul_comm,
      mellinScore_mul_self hpos]
  · rw [mul_one]

/-- **Grouping by the high part** (`output-closure.md` (O5)). -/
theorem outMonSum_eq_sum_high {f : ℝ → ℝ} (hpos : ∀ x, 0 ≤ f x) (j : ℕ) (x : Fin n → ℝ) :
    outMonSum f j x =
      ∑ β ∈ outBox n j, (∏ l, mellinOp^[β l] f (x l)) * outCentred f j β x := by
  classical
  rw [outMonSum, ← Finset.sum_fiberwise_of_maps_to (s := univ) (t := outBox n j)
    (g := outHigh) (fun c _ => outHigh_mem_outBox c)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [outCentred, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_filter] at hc
  rw [outMon_eq_high_mul hpos, hc.2]

theorem abs_outRadial_le_grouped {f : ℝ → ℝ} (hpos : ∀ x, 0 ≤ f x) (r : ℕ) (x : Fin n → ℝ) :
    |outRadial f r x| ≤ ∑ i ∈ range (r + 1), |outCoeff r i| *
      ∑ β ∈ outBox n i, (∏ l, |mellinOp^[β l] f (x l)|) * |outCentred f i β x| := by
  rw [outRadial]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, outMonSum_eq_sum_high hpos]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun β _ => ?_))
  rw [abs_mul, Finset.abs_prod]

/-- Lower integrals against the product of the high factors are integrals for `outMeasure`. -/
theorem lintegral_mul_eq_outMeasure {f : ℝ → ℝ} (hc : ∀ a, Measurable (mellinOp^[a] f))
    (β : Fin n → ℕ) {Y : (Fin n → ℝ) → ℝ≥0∞} (hY : Measurable Y) :
    ∫⁻ x, ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) * Y x =
      ∫⁻ x, Y x ∂(outMeasure f β) := by
  have hρ : ∀ l, Measurable fun x => ENNReal.ofReal |mellinOp^[β l] f x| :=
    fun l => (continuous_abs.measurable.comp (hc (β l))).ennreal_ofReal
  rw [outMeasure, pi_withDensity_fin volume _ hρ, ← volume_pi,
    lintegral_withDensity_eq_lintegral_mul _
      (Finset.measurable_fun_prod (f := fun l (x : Fin n → ℝ) =>
        ENNReal.ofReal |mellinOp^[β l] f (x l)|) _ fun l _ => (hρ l).comp (measurable_pi_apply l))
      hY]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_prod_of_nonneg fun l _ => abs_nonneg _]

theorem outCentred_measurable {f : ℝ → ℝ} (hfm : Measurable f) (hc : ∀ a, Measurable (mellinOp^[a] f))
    (j : ℕ) (β : Fin n → ℕ) : Measurable (outCentred f j β) := by
  have hρ : Measurable (mellinScore f) := by
    have h1 : Measurable (mellinOp f) := hc 1
    exact h1.div hfm
  exact Finset.measurable_sum _ fun c _ => Finset.measurable_prod _ fun l _ =>
    hρ.comp (measurable_pi_apply l)

/-- **The grouped bound on the radial weight.** -/
theorem lintegral_coneWeight_le {f : ℝ → ℝ} (hpos : ∀ x, 0 ≤ f x) (hf0 : ∀ x ≤ 0, f x = 0)
    (hfm : Measurable f) (hc : ∀ a, Measurable (mellinOp^[a] f)) (r : ℕ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    ∫⁻ x, coneWeight A f r x ≤ ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
      ∑ β ∈ outBox n i, ∫⁻ x, A.indicator
        (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x ∂(outMeasure f β) := by
  have hpt : ∀ x, coneWeight A f r x ≤ ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
      ∑ β ∈ outBox n i, ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) *
        A.indicator (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x := by
    intro x
    simp only [coneWeight]
    by_cases hxA : x ∈ A
    swap
    · rw [indicator_of_notMem hxA]; exact bot_le
    rw [indicator_of_mem hxA]
    simp_rw [indicator_of_mem hxA]
    by_cases hx : ∀ l, 0 < x l
    · have hsum : 0 ≤ ∑ l, x l := Finset.sum_nonneg fun l _ => (hx l).le
      have hden : 0 ≤ (∑ l, x l) ^ r := pow_nonneg hsum r
      have h1 := abs_outRadial_le_grouped hpos r x
      calc ENNReal.ofReal (|outRadial f r x| / (∑ l, x l) ^ r)
          ≤ ENNReal.ofReal ((∑ i ∈ range (r + 1), |outCoeff r i| *
              ∑ β ∈ outBox n i, (∏ l, |mellinOp^[β l] f (x l)|) * |outCentred f i β x|) /
                (∑ l, x l) ^ r) :=
            ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h1 hden)
        _ = ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
              ∑ β ∈ outBox n i, ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) *
                ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r) := by
            rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_div_assoc, ENNReal.ofReal_mul (abs_nonneg _), Finset.sum_div,
              ENNReal.ofReal_sum_of_nonneg (fun β _ => by positivity)]
            congr 1
            refine Finset.sum_congr rfl fun β _ => ?_
            rw [mul_div_assoc, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => abs_nonneg _)]
    · push Not at hx
      obtain ⟨l, hl⟩ := hx
      rw [outRadial_eq_zero hf0 r hl, abs_zero, zero_div, ENNReal.ofReal_zero]
      exact bot_le
  have hYm : ∀ i (β : Fin n → ℕ), Measurable fun x => A.indicator
      (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x := by
    intro i β
    refine Measurable.indicator ?_ hA
    exact ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (outCentred_measurable hfm hc i β)).div
        ((Finset.measurable_sum _ fun l _ => measurable_pi_apply l).pow_const r))
  have hPm : ∀ β : Fin n → ℕ, Measurable fun x : Fin n → ℝ =>
      ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) := by
    intro β
    exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun l _ =>
      (continuous_abs.measurable.comp (hc (β l))).comp (measurable_pi_apply l))
  calc ∫⁻ x, coneWeight A f r x
      ≤ ∫⁻ x, ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
          ∑ β ∈ outBox n i, ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) *
            A.indicator (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x :=
        lintegral_mono hpt
    _ = ∑ i ∈ range (r + 1), ENNReal.ofReal |outCoeff r i| *
          ∑ β ∈ outBox n i, ∫⁻ x, ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) *
            A.indicator (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x := by
        rw [lintegral_finsetSum (f := fun i x => ENNReal.ofReal |outCoeff r i| *
            ∑ β ∈ outBox n i, ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) *
              A.indicator (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x) _
          fun i _ => Measurable.const_mul
            (Finset.measurable_fun_sum _ fun β _ => (hPm β).fun_mul (hYm i β)) _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ fun β _ =>
            (hPm β).fun_mul (hYm i β)),
          lintegral_finsetSum (f := fun β x => ENNReal.ofReal (∏ l, |mellinOp^[β l] f (x l)|) *
            A.indicator (fun x => ENNReal.ofReal (|outCentred f i β x| / (∑ l, x l) ^ r)) x) _
            fun β _ => (hPm β).fun_mul (hYm i β)]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact Finset.sum_congr rfl fun β _ => lintegral_mul_eq_outMeasure hc β (hYm i β)

end PGM
