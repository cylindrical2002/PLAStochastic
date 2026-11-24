import PLAStochastic.Index.CEPS.Output.RayDerivative
import PLAStochastic.ForMathlib.MeasureTheory.Integral.RadialSlice
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Track O: the radial Fourier bound on a cone

For a cone `A ⊆ ℝ^{m+1}` (invariant under positive dilations) and a density `f` vanishing
on `(-∞, 0]`, put `Φ(τ) = ∫_A e^{iτ ∑ x} ∏_l f(x_l) dx`. Slicing along rays through the
origin (`integral_eq_radial`, last coordinate radial) and integrating by parts `r` times on
each ray (`norm_integral_rayF_le`) gives, for `r ≤ m`,

`|τ|^r |Φ(τ)| ≤ ∫_A |∏_{a=1}^r (ℒ - a) ∏_l f(x_l)| / (∑ x)^r dx`

(`ofReal_cone_integral_le`). This is `smoothing.md` (S4)–(S6) in integrated form: the
indicator of the cone is constant along each ray, so no boundary term appears.
-/

noncomputable section

open Finset Set MeasureTheory Filter
open scoped ENNReal

namespace PGM

variable {m : ℕ}

/-- The integrand `1_A(x) e^{iτ ∑ x} ∏_l f(x_l)`. -/
def coneIntegrand {n : ℕ} (A : Set (Fin n → ℝ)) (f : ℝ → ℝ) (τ : ℝ) (x : Fin n → ℝ) : ℂ :=
  A.indicator (fun x => Complex.exp (↑(τ * ∑ l, x l) * Complex.I) * ((∏ l, f (x l) : ℝ) : ℂ)) x

/-- The weight `1_A(x) |∏_{a ≤ r} (ℒ - a) ∏_l f(x_l)| / (∑ x)^r`. -/
def coneWeight {n : ℕ} (A : Set (Fin n → ℝ)) (f : ℝ → ℝ) (r : ℕ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  A.indicator (fun x => ENNReal.ofReal (|outRadial f r x| / (∑ l, x l) ^ r)) x

theorem integrable_of_envelope {f : ℝ → ℝ} {E κ : ℝ} (hκ : 0 < κ) (hfm : Measurable f)
    (hf0 : ∀ x ≤ 0, f x = 0) (henv : ∀ x, |f x| ≤ E * Real.exp (-κ * |x|)) : Integrable f := by
  have hg : Integrable ((Ioi (0 : ℝ)).indicator fun x => E * Real.exp (-κ * x)) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (exp_neg_integrableOn_Ioi 0 hκ).const_mul E
  refine hg.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    simpa [abs_of_pos hx] using henv x
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), hf0 x (not_lt.mp hx), abs_zero]

theorem integrable_coneIntegrand {n : ℕ} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)
    {f : ℝ → ℝ} (hfi : Integrable f) (hfm : Measurable f) (τ : ℝ) :
    Integrable (coneIntegrand A f τ) := by
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ l, f (x l)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ => f) fun _ => hfi
  have hmeas : Measurable fun x : Fin n → ℝ =>
      Complex.exp (↑(τ * ∑ l, x l) * Complex.I) * ((∏ l, f (x l) : ℝ) : ℂ) := by
    refine Measurable.mul ?_ ?_
    · exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul (Finset.measurable_sum _ fun l _ => measurable_pi_apply l))).mul_const _)
    · exact Complex.measurable_ofReal.comp
        (Finset.measurable_prod _ fun l _ => hfm.comp (measurable_pi_apply l))
  refine (hprod.norm.indicator hA).mono' (hmeas.indicator hA).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simp only [coneIntegrand]
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx, indicator_of_mem hx, norm_mul, Complex.norm_exp_ofReal_mul_I,
      one_mul, Complex.norm_real]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, norm_zero]

theorem sum_smul_snoc (s : ℝ) (u : Fin m → ℝ) :
    ∑ l, (s • (Fin.snoc u 1 : Fin (m + 1) → ℝ)) l = s * ∑ l, (Fin.snoc u 1 : Fin (m + 1) → ℝ) l := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

theorem sum_snoc_ge_one {u : Fin m → ℝ} (hu : ∀ l, 0 < u l) :
    1 ≤ ∑ l, (Fin.snoc u 1 : Fin (m + 1) → ℝ) l := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have : 0 ≤ ∑ l, u l := Finset.sum_nonneg fun l _ => (hu l).le
  linarith

variable {f : ℝ → ℝ} {E κ : ℝ} {r : ℕ}

theorem measurable_coneWeight {n : ℕ} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)
    (hc : ∀ a ≤ r, Continuous (mellinOp^[a] f)) : Measurable (coneWeight A f r) := by
  refine Measurable.indicator ?_ hA
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((continuous_outRadial hc le_rfl).abs.measurable).div
    ((Finset.measurable_sum _ fun l _ => measurable_pi_apply l).pow_const r)

/-- The bound on one ray. -/
theorem ray_inner_bound (hE : 0 ≤ E) (hκ : 0 < κ) (hrm : r ≤ m)
    (hf0 : ∀ x ≤ 0, f x = 0) (hc : ∀ a ≤ r, Continuous (mellinOp^[a] f))
    (hd : ∀ a < r, Differentiable ℝ (mellinOp^[a] f))
    (henv : ∀ a ≤ r, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|))
    {A : Set (Fin (m + 1) → ℝ)} (hA : MeasurableSet A)
    (hcone : ∀ c : ℝ, 0 < c → ∀ x, c • x ∈ A ↔ x ∈ A) (τ : ℝ) (u : Fin m → ℝ) :
    ENNReal.ofReal (|τ| ^ r * ‖∫ s, coneIntegrand A f τ (s • (Fin.snoc u 1 : Fin (m + 1) → ℝ))
        ∂(radialMeasure m)‖) ≤
      ∫⁻ s, coneWeight A f r (s • (Fin.snoc u 1 : Fin (m + 1) → ℝ)) ∂(radialMeasure m) := by
  set w : Fin (m + 1) → ℝ := Fin.snoc u 1 with hw
  have hwl : w (Fin.last m) = 1 := by simp [hw]
  set σ : ℝ := ∑ l, w l with hσ
  have hdm : Measurable fun s : ℝ => ENNReal.ofReal (s ^ m) :=
    (measurable_id.pow_const m).ennreal_ofReal
  -- the inner integral as a whole-line integral of the ray density
  have hinner : ∫ s, coneIntegrand A f τ (s • w) ∂(radialMeasure m) =
      A.indicator (fun _ => (1 : ℂ)) w *
        ∫ s : ℝ, Complex.exp (↑((τ * σ) * s) * Complex.I) * (rayF f m 0 w s : ℂ) := by
    rw [radialMeasure, integral_withDensity_eq_integral_toReal_smul hdm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
      (f := fun s => A.indicator (fun _ => (1 : ℂ)) w *
        (Complex.exp (↑((τ * σ) * s) * Complex.I) * (rayF f m 0 w s : ℂ)))
      (fun s hs => by rw [rayF_eq_zero hf0 hwl (not_lt.mp hs)]; simp)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
    simp only [coneIntegrand]
    rw [ENNReal.toReal_ofReal (pow_nonneg hs.le m), rayF_zero]
    by_cases hwA : w ∈ A
    · have hsA : s • w ∈ A := (hcone s hs w).mpr hwA
      rw [indicator_of_mem hsA, indicator_of_mem hwA, sum_smul_snoc]
      simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, hσ, hw]
      push_cast
      ring_nf
    · have hsA : s • w ∉ A := fun h => hwA ((hcone s hs w).mp h)
      rw [indicator_of_notMem hsA, indicator_of_notMem hwA]
      simp
  rw [hinner]
  by_cases hwA : w ∈ A
  swap
  · rw [indicator_of_notMem hwA, zero_mul, norm_zero, mul_zero, ENNReal.ofReal_zero]
    exact bot_le
  rw [indicator_of_mem hwA, one_mul]
  by_cases hu : ∀ l, 0 < u l
  swap
  · push Not at hu
    obtain ⟨l, hl⟩ := hu
    have hz : ∀ s, rayF f m 0 w s = 0 := by
      intro s
      rcases le_or_gt s 0 with hs | hs
      · exact rayF_eq_zero hf0 hwl hs
      · rw [rayF_zero]
        refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ l.castSucc) ?_)
        rw [hw, Fin.snoc_castSucc]
        exact hf0 _ (mul_nonpos_of_nonneg_of_nonpos hs.le hl)
    simp only [hz, Complex.ofReal_zero, mul_zero, integral_zero, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hσ1 : 1 ≤ σ := sum_snoc_ge_one hu
  have hσ0 : 0 < σ := by linarith
  have hibp := norm_integral_rayF_le hE hκ hrm hf0 hc hd henv hwl (τ * σ)
  rw [abs_mul, mul_pow, abs_of_pos hσ0] at hibp
  have hσr : 0 < σ ^ r := pow_pos hσ0 r
  have hbound : |τ| ^ r * ‖∫ s : ℝ, Complex.exp (↑((τ * σ) * s) * Complex.I) *
      (rayF f m 0 w s : ℂ)‖ ≤ (∫ s, |rayF f m r w s|) / σ ^ r := by
    rw [le_div_iff₀ hσr]; linarith
  refine (ENNReal.ofReal_le_ofReal hbound).trans (le_of_eq ?_)
  -- the right-hand side
  have hint : Integrable fun s => |rayF f m r w s| / σ ^ r :=
    (integrable_rayF hE hκ hf0 hc henv le_rfl hwl).abs.div_const _
  rw [← integral_div, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun s => by positivity), radialMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hdm]
  · rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun s => ?_
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
      simp only [Pi.mul_apply, coneWeight]
      rw [indicator_of_mem ((hcone s hs w).mpr hwA), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [rayF, abs_mul, abs_pow, abs_of_pos hs, sum_smul_snoc, ← hw, ← hσ, mul_pow]
      have hsr : s ^ m = s ^ (m - r) * s ^ r := by
        rw [← pow_add, Nat.sub_add_cancel hrm]
      rw [hsr]
      field_simp
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs),
        rayF_eq_zero hf0 hwl (not_lt.mp hs), abs_zero, zero_div, ENNReal.ofReal_zero]
  · exact (measurable_coneWeight hA hc).comp (measurable_id.smul_const w)

/-- **The radial Fourier bound on a cone** (`smoothing.md` (S4)–(S6), integrated form). -/
theorem ofReal_cone_integral_le (hE : 0 ≤ E) (hκ : 0 < κ) (hrm : r ≤ m) (hfm : Measurable f)
    (hf0 : ∀ x ≤ 0, f x = 0) (hc : ∀ a ≤ r, Continuous (mellinOp^[a] f))
    (hd : ∀ a < r, Differentiable ℝ (mellinOp^[a] f))
    (henv : ∀ a ≤ r, ∀ x, |mellinOp^[a] f x| ≤ E * Real.exp (-κ * |x|))
    {A : Set (Fin (m + 1) → ℝ)} (hA : MeasurableSet A)
    (hcone : ∀ c : ℝ, 0 < c → ∀ x, c • x ∈ A ↔ x ∈ A) (τ : ℝ) :
    ENNReal.ofReal (|τ| ^ r * ‖∫ x, coneIntegrand A f τ x‖) ≤ ∫⁻ x, coneWeight A f r x := by
  have hfi : Integrable f :=
    integrable_of_envelope hκ hfm hf0 (by simpa using henv 0 (Nat.zero_le _))
  have hGi := integrable_coneIntegrand hA hfi hfm τ
  have h0 : ∀ x : Fin (m + 1) → ℝ, x (Fin.last m) ≤ 0 → coneIntegrand A f τ x = 0 := by
    intro x hx
    simp only [coneIntegrand]
    by_cases hxA : x ∈ A
    · rw [indicator_of_mem hxA, Finset.prod_eq_zero (Finset.mem_univ (Fin.last m)) (hf0 _ hx)]
      simp
    · rw [indicator_of_notMem hxA]
  rw [integral_eq_radial hGi h0]
  set inner : (Fin m → ℝ) → ℂ := fun u =>
    ∫ s, coneIntegrand A f τ (s • (Fin.snoc u 1 : Fin (m + 1) → ℝ)) ∂(radialMeasure m) with hinner
  have hτ : 0 ≤ |τ| ^ r := by positivity
  calc ENNReal.ofReal (|τ| ^ r * ‖∫ u, inner u‖)
      ≤ ENNReal.ofReal (|τ| ^ r) * ∫⁻ u, ENNReal.ofReal ‖inner u‖ := by
        rw [ENNReal.ofReal_mul hτ]
        gcongr
        refine (ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)).trans ?_
        exact ENNReal.ofReal_toReal_le
    _ = ∫⁻ u, ENNReal.ofReal (|τ| ^ r * ‖inner u‖) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun u => (ENNReal.ofReal_mul hτ).symm
    _ ≤ ∫⁻ u : Fin m → ℝ, ∫⁻ s,
          coneWeight A f r (s • (Fin.snoc u 1 : Fin (m + 1) → ℝ)) ∂(radialMeasure m) :=
        lintegral_mono fun u => ray_inner_bound hE hκ hrm hf0 hc hd henv hA hcone τ u
    _ = ∫⁻ x in {x : Fin (m + 1) → ℝ | 0 < x (Fin.last m)}, coneWeight A f r x :=
        (lintegral_halfSpace_eq_radial (measurable_coneWeight hA hc)).symm
    _ ≤ ∫⁻ x, coneWeight A f r x := setLIntegral_le_lintegral _ _

end PGM
