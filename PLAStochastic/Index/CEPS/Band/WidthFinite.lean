import PLAStochastic.Index.CEPS.Band.Moments
import PLAStochastic.Index.CEPS.Actual.Hadamard

/-!
# Finite-time width variations of killed survival and the opposite-side pin

The density representative is explicit. In particular continuity of the pin
will be proved from continuity of that representative, rather than assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

/-- Removing the redundant last-position indicator in the bottom-to-top density. -/
theorem CepsGapDensity.cepsBand_density_path (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (_hf : CepsGapDensity ν f D) {l : ℝ} (hl : 0 ≤ l)
    (β a : ℝ) (n : ℕ) :
    krDens (Icc 0 l) ν f β a (n + 1) 0 l =
      ∫ g, krAlive (Icc 0 l) β a n 0 g *
        (f ((kWalk 0 β a g n + β - l) / a) / |a|) ∂(iidLaw ν) := by
  rw [krDens_succ]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hk := krAlive_mul_indicator (J := Icc 0 l) (β := β) (a := a) n 0 g
  unfold krKer
  rw [indicator_of_mem (show l ∈ Icc 0 l from ⟨hl, le_rfl⟩)]
  linear_combination (f ((kWalk 0 β a g n + β - l) / a) / |a|) * hk

/-- A finite survival function has a quantitative width modulus without any smooth density. -/
theorem CepsGapDensity.cepsBand_survival_width_le {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ ≤ l₂) (n : ℕ) :
    0 ≤ krSurv (Icc 0 l₂) (ν : Measure ℝ) β a n 0 -
      krSurv (Icc 0 l₁) (ν : Measure ℝ) β a n 0 ∧
    krSurv (Icc 0 l₂) (ν : Measure ℝ) β a n 0 -
      krSurv (Icc 0 l₁) (ν : Measure ℝ) β a n 0 ≤
        n * (D / |a|) * (l₂ - l₁) := by
  rw [hf.krSurv_bottom_sub ha β hl₁ hl n]
  have hb : ∀ j : ℕ, ∀ z ∈ Ioc l₁ l₂,
      krDens (Icc 0 z) ν f β a (j + 1) 0 z *
        krSurv (Icc 0 z) (ν : Measure ℝ) β a (n - (j + 1)) z ≤ D / |a| := by
    intro j z _
    calc
      _ ≤ (D / |a|) * 1 := mul_le_mul (krDens_le_div ν hf.nonneg hf.le _ _ _)
        (krSurv_top_le_one ν β a _ z) (krSurv_top_nonneg ν β a _ z)
        (div_nonneg hf.nonneg_D (abs_nonneg _))
      _ = _ := mul_one _
  refine ⟨Finset.sum_nonneg fun _ _ => setIntegral_nonneg measurableSet_Ioc
    (fun z _ => mul_nonneg (krDens_nonneg ν hf.nonneg _ _ _)
      (krSurv_top_nonneg ν β a _ z)), ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range n, ∫ _z in Ioc l₁ l₂, D / |a| :=
      Finset.sum_le_sum fun j _ => setIntegral_mono_on
        (hf.integrableOn_krDens_mul a β j (n - (j + 1)) l₁ l₂)
        (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc (hb j)
    _ = _ := by
      simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hl,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Monotonicity of the path indicator with respect to bandwidth. -/
theorem cepsBand_alive_mono {l₁ l₂ : ℝ} (hl : l₁ ≤ l₂) (β a : ℝ)
    (n : ℕ) (y : ℝ) (g : ℕ → ℝ) :
    krAlive (Icc 0 l₁) β a n y g ≤ krAlive (Icc 0 l₂) β a n y g := by
  unfold krAlive
  apply Finset.prod_le_prod (fun _ _ => kr_indicator_one_nonneg _)
  intro k _
  by_cases hk : kWalk y β a g k ∈ Icc 0 l₁
  · rw [indicator_of_mem hk, indicator_of_mem (show kWalk y β a g k ∈ Icc 0 l₂ from
      ⟨hk.1, hk.2.trans hl⟩)]
  · rw [indicator_of_notMem hk]
    exact kr_indicator_one_nonneg _

/-- Each finite survival term is Lipschitz in the width on the nonnegative half-line. -/
theorem CepsGapDensity.cepsBand_survival_lipschitz {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) (n : ℕ) :
    LipschitzOnWith ⟨n * (D / |a|), mul_nonneg (Nat.cast_nonneg n)
      (div_nonneg hf.nonneg_D (abs_nonneg a))⟩
      (fun l => krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)
    (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0) ≤
      n * (D / |a|) * dist x y
  rcases le_total y x with h | h
  · obtain ⟨hn, hb⟩ := hf.cepsBand_survival_width_le ha β hy h n
    simpa only [Real.dist_eq, abs_of_nonneg hn,
      abs_of_nonneg (sub_nonneg.mpr h)] using hb
  · obtain ⟨hn, hb⟩ := hf.cepsBand_survival_width_le ha β hx h n
    rw [dist_comm, dist_comm x y]
    simpa only [Real.dist_eq, abs_of_nonneg hn,
      abs_of_nonneg (sub_nonneg.mpr h)] using hb

/-- Endpoint motion of the bottom-to-top pin is controlled by a bounded density derivative
(equivalently, the density Lipschitz constant) and the survival width variation. -/
theorem CepsGapDensity.cepsBand_pin_width_le {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {K : ℝ≥0}
    (hLip : LipschitzWith K f) {a : ℝ} (ha : a ≠ 0) (β : ℝ)
    {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ ≤ l₂) (n : ℕ) :
    |krDens (Icc 0 l₂) ν f β a (n + 1) 0 l₂ -
      krDens (Icc 0 l₁) ν f β a (n + 1) 0 l₁| ≤
      (D / |a|) * (krSurv (Icc 0 l₂) (ν : Measure ℝ) β a n 0 -
        krSurv (Icc 0 l₁) (ν : Measure ℝ) β a n 0) +
      ((K : ℝ) / |a| ^ 2) * (l₂ - l₁) * krSurv (Icc 0 l₁) (ν : Measure ℝ) β a n 0 := by
  have habs : 0 < |a| := abs_pos.mpr ha
  let A := fun l g => krAlive (Icc 0 l) β a n 0 g
  let B := fun l g => f ((kWalk 0 β a g n + β - l) / a) / |a|
  have hi : ∀ l, Integrable (fun g => A l g * B l g) (iidLaw ν) := by
    intro l
    refine kr_integrable_of_bdd ((measurable_krAlive_right measurableSet_Icc β a n 0).mul
      ((hf.measurable.comp (((measurable_kWalk_right 0 β a n).add_const β).sub_const l
        |>.div_const a)).div_const _)) (M := D / |a|) ?_
    intro g
    dsimp [A, B]
    rw [abs_mul, abs_div, abs_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
      abs_of_nonneg (hf.nonneg _)]
    calc
      _ ≤ 1 * (D / |a|) := mul_le_mul (krAlive_le_one _ _ _)
        (div_le_div_of_nonneg_right (hf.le _) habs.le)
        (div_nonneg (hf.nonneg _) habs.le) zero_le_one
      _ = _ := one_mul _
  rw [hf.cepsBand_density_path ν (hl₁.trans hl) β a n,
    hf.cepsBand_density_path ν hl₁ β a n, ← integral_sub (hi l₂) (hi l₁)]
  let G := fun g => (D / |a|) * (A l₂ g - A l₁ g) +
    ((K : ℝ) / |a| ^ 2) * (l₂ - l₁) * A l₁ g
  have hAint : ∀ l, Integrable (A l) (iidLaw ν) := fun l =>
    kr_integrable_of_bdd (measurable_krAlive_right measurableSet_Icc β a n 0)
      (abs_krAlive_le_one n 0)
  have hG : Integrable G (iidLaw ν) :=
    ((hAint l₂).sub (hAint l₁)).const_mul _ |>.add ((hAint l₁).const_mul _)
  have hb : ∀ g, |B l₂ g - B l₁ g| ≤ ((K : ℝ) / |a| ^ 2) * (l₂ - l₁) := by
    intro g
    have h := hLip.dist_le_mul ((kWalk 0 β a g n + β - l₂) / a)
      ((kWalk 0 β a g n + β - l₁) / a)
    simp only [Real.dist_eq] at h
    have he : (kWalk 0 β a g n + β - l₂) / a -
        (kWalk 0 β a g n + β - l₁) / a = -(l₂ - l₁) / a := by ring
    rw [he, abs_div, abs_neg, abs_of_nonneg (sub_nonneg.mpr hl)] at h
    dsimp [B]
    rw [← sub_div, abs_div, abs_abs]
    refine (div_le_div_of_nonneg_right h habs.le).trans_eq ?_
    field_simp
  have hdom : ∀ g, ‖A l₂ g * B l₂ g - A l₁ g * B l₁ g‖ ≤ G g := by
    intro g
    have hA := cepsBand_alive_mono hl β a n 0 g
    have hB : |B l₂ g| ≤ D / |a| := by
      dsimp [B]
      rw [abs_div, abs_abs, abs_of_nonneg (hf.nonneg _)]
      exact div_le_div_of_nonneg_right (hf.le _) habs.le
    rw [Real.norm_eq_abs, show A l₂ g * B l₂ g - A l₁ g * B l₁ g =
      (A l₂ g - A l₁ g) * B l₂ g + A l₁ g * (B l₂ g - B l₁ g) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hA),
      abs_of_nonneg (krAlive_nonneg _ _ _)]
    exact add_le_add (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hA))
      (mul_le_mul_of_nonneg_left (hb g) (krAlive_nonneg _ _ _)) |>.trans_eq (by dsimp [G]; ring)
  have hnorm := norm_integral_le_of_norm_le hG (Eventually.of_forall hdom)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans_eq ?_
  dsimp only [G]
  have hi₁ : Integrable (fun g => (D / |a|) * (A l₂ g - A l₁ g)) (iidLaw ν) :=
    ((hAint l₂).sub (hAint l₁)).const_mul _
  have hi₂ : Integrable (fun g => ((K : ℝ) / |a| ^ 2) * (l₂ - l₁) * A l₁ g)
      (iidLaw ν) := (hAint l₁).const_mul _
  rw [integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
  have hisub : (∫ g, A l₂ g - A l₁ g ∂(iidLaw ν)) =
      (∫ g, A l₂ g ∂(iidLaw ν)) - ∫ g, A l₁ g ∂(iidLaw ν) :=
    integral_sub (hAint l₂) (hAint l₁)
  rw [hisub]
  dsimp only [A]
  rw [← krSurv_eq_integral measurableSet_Icc, ← krSurv_eq_integral measurableSet_Icc]

/-- The finite opposite-side pin is Lipschitz when the density has a bounded derivative. -/
theorem CepsGapDensity.cepsBand_pin_lipschitz {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {K : ℝ≥0}
    (hLip : LipschitzWith K f) {a : ℝ} (ha : a ≠ 0) (β : ℝ) (n : ℕ) :
    LipschitzOnWith ⟨n * (D / |a|) ^ 2 + (K : ℝ) / |a| ^ 2, by positivity⟩
      (fun l => krDens (Icc 0 l) ν f β a (n + 1) 0 l) (Ici 0) := by
  have hD : 0 ≤ D / |a| := div_nonneg hf.nonneg_D (abs_nonneg _)
  have hb : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y →
      |krDens (Icc 0 y) ν f β a (n + 1) 0 y -
        krDens (Icc 0 x) ν f β a (n + 1) 0 x| ≤
      (n * (D / |a|) ^ 2 + (K : ℝ) / |a| ^ 2) * (y - x) := by
    intro x y hx hxy
    have hs := (hf.cepsBand_survival_width_le ha β hx hxy n).2
    refine (hf.cepsBand_pin_width_le hLip ha β hx hxy n).trans ?_
    calc
      _ ≤ (D / |a|) * (n * (D / |a|) * (y - x)) +
          ((K : ℝ) / |a| ^ 2) * (y - x) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hs hD)
          (mul_le_mul_of_nonneg_left (krSurv_le_one measurableSet_Icc ν β a n 0)
            (mul_nonneg (by positivity) (sub_nonneg.mpr hxy)))
      _ = _ := by ring
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (krDens (Icc 0 x) ν f β a (n + 1) 0 x)
      (krDens (Icc 0 y) ν f β a (n + 1) 0 y) ≤
    (n * (D / |a|) ^ 2 + (K : ℝ) / |a| ^ 2) * dist x y
  rcases le_total y x with h | h
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h)] using hb hy h
  · rw [dist_comm, dist_comm x y]
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h)] using hb hx h

end
end PGM
