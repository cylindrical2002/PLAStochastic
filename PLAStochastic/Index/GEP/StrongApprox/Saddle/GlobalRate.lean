import PLAStochastic.Index.GEP.StrongApprox.Saddle.RateTaylor
import Mathlib.Analysis.Convex.Deriv

/-!
# WP5: the global truncated Legendre transform

The supremum is over the fixed tilt interval. Its convexity supplies global
linear tails from the local quadratic lower bound.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Legendre transform restricted to the common admissible tilt interval. -/
def saGlobalRate (vlo B θ : ℝ) (ν : ProbabilityMeasure ℝ) (s w : ℝ) : ℝ :=
  sSup ((fun lam => lam * w - saSmoothCGF ν s lam) ''
    Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ))

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.continuousOn_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) (s : ℝ) : ContinuousOn (saSmoothCGF ν s)
      (Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)) := by
  intro t ht
  exact (h.analyticAt_saSmoothCGF
    (lt_of_le_of_lt ((abs_le.mpr ht).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)) s).continuousAt.continuousWithinAt

theorem UnivClass.saGlobalRate_bddAbove (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) (s w : ℝ) : BddAbove ((fun lam => lam * w - saSmoothCGF ν s lam) ''
      Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)) :=
  isCompact_Icc.bddAbove_image ((continuousOn_id.mul continuousOn_const).sub
    (h.continuousOn_saSmoothCGF hθ s))

theorem UnivClass.le_saGlobalRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) (s w : ℝ) {lam : ℝ} (hlam : |lam| ≤ saTiltRadius vlo B θ) :
    lam * w - saSmoothCGF ν s lam ≤ saGlobalRate vlo B θ ν s w :=
  le_csSup (h.saGlobalRate_bddAbove hθ s w) ⟨lam, abs_le.mp hlam, rfl⟩

theorem saGlobalRate_image_nonempty {vlo B θ : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ)
    (ν : ProbabilityMeasure ℝ) (s w : ℝ) :
    ((fun lam => lam * w - saSmoothCGF ν s lam) ''
      Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)).Nonempty := by
  have hr := (saTiltRadius_pos (B := B) hvlo hθ).le
  exact ⟨_, ⟨0, ⟨by linarith, hr⟩, rfl⟩⟩

theorem UnivClass.convexOn_saGlobalRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) : ConvexOn ℝ univ (saGlobalRate vlo B θ ν s) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply csSup_le (saGlobalRate_image_nonempty hvlo hθ ν s (a * x + b * y))
  rintro z ⟨lam, hlam, rfl⟩
  have hx := mul_le_mul_of_nonneg_left (h.le_saGlobalRate hθ s x (abs_le.mpr hlam)) ha
  have hy := mul_le_mul_of_nonneg_left (h.le_saGlobalRate hθ s y (abs_le.mpr hlam)) hb
  calc
    lam * (a * x + b * y) - saSmoothCGF ν s lam =
        a * (lam * x - saSmoothCGF ν s lam) + b * (lam * y - saSmoothCGF ν s lam) := by
      nlinarith [congrArg (fun t : ℝ => t * saSmoothCGF ν s lam) hab]
    _ ≤ _ := add_le_add hx hy

theorem UnivClass.convexOn_saSmoothCGF (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) : ConvexOn ℝ
      (Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)) (saSmoothCGF ν s) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _) (h.continuousOn_saSmoothCGF hθ s)
  · intro t ht
    have ht' := interior_subset (s := Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)) ht
    exact (h.analyticAt_saSmoothCGF
      (lt_of_le_of_lt ((abs_le.mpr ht').trans (saTiltRadius_le_half vlo B hθ)) (by linarith)) s).differentiableAt.differentiableWithinAt
  · exact (h.saSmoothCGF_mean_strictMono hvlo hθ s).monotoneOn.mono interior_subset

/-- Supporting-line inequality on a real interval, including its endpoints. -/
theorem sa_convex_support {S : Set ℝ} {f : ℝ → ℝ} (hc : ConvexOn ℝ S f)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hd : DifferentiableAt ℝ f a) :
    f a + deriv f a * (b - a) ≤ f b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hh := hc.deriv_le_slope ha hb hab hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hab)] at hh
    linarith
  · simp
  · have hh := hc.slope_le_deriv hb ha hba hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hba)] at hh
    nlinarith

/-- On the central mean window the global transform is attained at the saddle. -/
theorem UnivClass.saGlobalRate_eq_saRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    saGlobalRate vlo B θ ν s w = saRate vlo B θ ν s w := by
  have hw' := hw.trans (saMeanRadius_lt_full hvlo hθ).le
  obtain ⟨hmem, heq⟩ := h.saSaddle_spec hvlo hθ s hw'
  have htθ : |saSaddle vlo B θ ν s w| < θ :=
    lt_of_le_of_lt ((abs_le.mpr hmem).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)
  apply le_antisymm
  · apply csSup_le (saGlobalRate_image_nonempty hvlo hθ ν s w)
    rintro z ⟨lam, hlam, rfl⟩
    have hs := sa_convex_support (h.convexOn_saSmoothCGF hvlo hθ s) hmem hlam
      (h.analyticAt_saSmoothCGF htθ s).differentiableAt
    rw [heq] at hs
    unfold saRate
    nlinarith
  · exact h.le_saGlobalRate hθ s w (abs_le.mpr hmem)

theorem UnivClass.saGlobalRate_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) : saGlobalRate vlo B θ ν s 0 = 0 := by
  rw [h.saGlobalRate_eq_saRate hvlo hθ s
    (by simpa using (saMeanRadius_pos (B := B) hvlo hθ).le), h.saRate_zero hvlo hθ s]

/-- A local quadratic lower bound extends to a global quadratic-or-linear bound by convexity. -/
theorem sa_convex_quadratic_linear_lower {f : ℝ → ℝ} {R c : ℝ}
    (hc : ConvexOn ℝ univ f) (hf0 : f 0 = 0) (hR : 0 < R) (hc0 : 0 ≤ c)
    (hloc : ∀ x : ℝ, |x| ≤ R → c * x ^ 2 ≤ f x) (x : ℝ) :
    c * min (x ^ 2) (R * |x|) ≤ f x := by
  by_cases hx : |x| ≤ R
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hc0).trans (hloc x hx)
  have hxR : R < |x| := lt_of_not_ge hx
  have hx0 : 0 < |x| := hR.trans hxR
  let a := R / |x|
  have ha : 0 < a := div_pos hR hx0
  have ha1 : a < 1 := (div_lt_one hx0).mpr hxR
  have hz : |a * x| = R := by
    rw [abs_mul, abs_of_pos ha]
    exact div_mul_cancel₀ R (ne_of_gt hx0)
  have hlo := hloc (a * x) hz.le
  have hco := hc.2 (x := x) (by trivial) (y := 0) (by trivial)
    ha.le (by linarith : 0 ≤ 1 - a) (by ring : a + (1 - a) = 1)
  simp only [smul_eq_mul, mul_zero, add_zero, hf0] at hco
  have hpow : (a * x) ^ 2 = R ^ 2 := by rw [← sq_abs, hz]
  rw [hpow] at hlo
  have hmain : c * (R * |x|) ≤ f x := by
    have hh : c * R ^ 2 ≤ a * f x := hlo.trans hco
    have haeq : a * |x| = R := div_mul_cancel₀ R (ne_of_gt hx0)
    have hp := mul_le_mul_of_nonneg_right hh hx0.le
    have he : (a * f x) * |x| = R * f x := by
      calc _ = (a * |x|) * f x := by ring
        _ = _ := by rw [haeq]
    rw [he] at hp
    apply le_of_mul_le_mul_left (a := R) ?_ hR
    convert hp using 1
    ring
  exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hc0).trans hmain

theorem UnivClass.saRate_second_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s w : ℝ} (hs : |s| ≤ 1)
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    4 / (5 * (vhi + 1)) ≤ iteratedDeriv 2 (saRate vlo B θ ν s) w := by
  have hw' := hw.trans_lt (saMeanRadius_lt_full hvlo hθ)
  obtain ⟨hmem, -⟩ := h.saSaddle_spec hvlo hθ s hw'.le
  have hbr := h.saSmoothCGF_variance_bracket hvlo hθ (abs_le.mpr hmem) s
  have hv0 : 0 < lawVar ν + s ^ 2 := by nlinarith [h.var_ge, sq_nonneg s]
  have hv : 0 < iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) := by
    linarith [hbr.1]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_abs s, pow_le_pow_left₀ (abs_nonneg s) hs 2]
  have hvhi : 0 < vhi + 1 := by nlinarith [h.var_ge, h.var_le]
  have hu : iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) ≤
      5 / 4 * (vhi + 1) := by linarith [hbr.2, h.var_le]
  rw [h.iteratedDeriv_two_saRate hvlo hθ s hw']
  calc
    _ = (5 / 4 * (vhi + 1))⁻¹ := by field_simp
    _ ≤ _ := inv_anti₀ hv hu

/-- A supporting parabola for the local rate, uniformly over the entire mean window. -/
theorem UnivClass.saRate_quadratic_support (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s u t : ℝ} (hs : |s| ≤ 1)
    (hut : |u| + |t| ≤ saMeanRadius vlo B θ) :
    saRate vlo B θ ν s u + deriv (saRate vlo B θ ν s) u * t +
        (4 / (5 * (vhi + 1))) * t ^ 2 / 2 ≤ saRate vlo B θ ν s (u + t) := by
  by_cases ht : t = 0
  · simp [ht]
  let f := saRate vlo B θ ν s
  let R := saMeanRadius vlo B θ
  have hu : |u| ≤ R := by have := abs_nonneg t; linarith
  have hup : |u + t| ≤ R := (abs_add_le u t).trans hut
  have hwin : uIcc u (u + t) ⊆ Icc (-R) R :=
    (convex_Icc (-R) R).ordConnected.uIcc_subset (abs_le.mp hu) (abs_le.mp hup)
  have hfull : ∀ z ∈ uIcc u (u + t), |z| < 3 / 4 * vlo * saTiltRadius vlo B θ :=
    fun z hz => (abs_le.mpr (hwin hz)).trans_lt (saMeanRadius_lt_full hvlo hθ)
  have hct : ContDiffOn ℝ 2 f (uIcc u (u + t)) :=
    fun z hz => (h.analyticAt_saRate hvlo hθ s (hfull z hz)).contDiffAt.contDiffWithinAt
  have hne : u ≠ u + t := by intro he; apply ht; linarith
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hct
  have hdiff : UniqueDiffOn ℝ (uIcc u (u + t)) := uniqueDiffOn_uIcc hne
  have hbase : u ∈ uIcc u (u + t) := left_mem_uIcc
  have hder : iteratedDerivWithin 1 f (uIcc u (u + t)) u = deriv f u := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hdiff
      (h.analyticAt_saRate hvlo hθ s (hfull u hbase)).contDiffAt hbase, iteratedDeriv_one]
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hder] at heq
  norm_num at heq
  have hz' : z ∈ uIcc u (u + t) := ⟨hz.1.le, hz.2.le⟩
  have hb := h.saRate_second_lower hvlo hθ hs (abs_le.mpr (hwin hz'))
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg t)
  change f u + deriv f u * t + 4 / (5 * (vhi + 1)) * t ^ 2 / 2 ≤ f (u + t)
  nlinarith [heq]

theorem UnivClass.saRate_quadratic_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s w : ℝ} (hs : |s| ≤ 1)
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    (2 / (5 * (vhi + 1))) * w ^ 2 ≤ saRate vlo B θ ν s w := by
  have hh := h.saRate_quadratic_support hvlo hθ hs (u := 0) (t := w) (by simpa using hw)
  have hz : |(0 : ℝ)| < 3 / 4 * vlo * saTiltRadius vlo B θ := by
    have hr := saTiltRadius_pos (B := B) hvlo hθ
    simpa using (by positivity : (0 : ℝ) < 3 / 4 * vlo * saTiltRadius vlo B θ)
  rw [h.saRate_zero hvlo hθ s, h.deriv_saRate hvlo hθ s hz, h.saSaddle_zero hvlo hθ s] at hh
  simp only [zero_mul, zero_add] at hh
  convert hh using 1
  ring

theorem UnivClass.saGlobalRate_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s : ℝ} (hs : |s| ≤ 1) (w : ℝ) :
    (2 / (5 * (vhi + 1))) * min (w ^ 2) (saMeanRadius vlo B θ * |w|) ≤
      saGlobalRate vlo B θ ν s w := by
  have hvhi : 0 < vhi + 1 := by nlinarith [h.var_ge, h.var_le]
  apply sa_convex_quadratic_linear_lower (h.convexOn_saGlobalRate hvlo hθ s)
    (h.saGlobalRate_zero hvlo hθ s) (saMeanRadius_pos hvlo hθ) (by positivity)
  intro x hx
  rw [h.saGlobalRate_eq_saRate hvlo hθ s hx]
  exact h.saRate_quadratic_lower hvlo hθ hs hx

theorem UnivClass.saRate_three_point_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s u t : ℝ} (hs : |s| ≤ 1)
    (hut : |u| + |t| ≤ saMeanRadius vlo B θ) :
    (4 / (5 * (vhi + 1))) * t ^ 2 ≤
      saRate vlo B θ ν s (u + t) + saRate vlo B θ ν s (u - t) - 2 * saRate vlo B θ ν s u := by
  have hp := h.saRate_quadratic_support hvlo hθ hs hut
  have hn := h.saRate_quadratic_support hvlo hθ hs (u := u) (t := -t) (by simpa using hut)
  simp only [neg_sq, mul_neg, ← sub_eq_add_neg] at hn
  linarith

theorem UnivClass.saGlobalRate_three_point_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s u : ℝ} (hs : |s| ≤ 1)
    (hu : |u| ≤ saMeanRadius vlo B θ / 2) (t : ℝ) :
    (4 / (5 * (vhi + 1))) * min (t ^ 2) (saMeanRadius vlo B θ / 2 * |t|) ≤
      saGlobalRate vlo B θ ν s (u + t) + saGlobalRate vlo B θ ν s (u - t) -
        2 * saGlobalRate vlo B θ ν s u := by
  let f := saGlobalRate vlo B θ ν s
  let g := fun t : ℝ => f (u + t) + f (u - t) - 2 * f u
  have hfc : ConvexOn ℝ univ f := h.convexOn_saGlobalRate hvlo hθ s
  have hgc : ConvexOn ℝ univ g := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hp := hfc.2 (x := u + x) (by trivial) (y := u + y) (by trivial) ha hb hab
    have hn := hfc.2 (x := u - x) (by trivial) (y := u - y) (by trivial) ha hb hab
    simp only [smul_eq_mul] at hp hn ⊢
    have ep : a * (u + x) + b * (u + y) = u + (a * x + b * y) := by
      calc _ = (a + b) * u + (a * x + b * y) := by ring
        _ = _ := by rw [hab, one_mul]
    have en : a * (u - x) + b * (u - y) = u - (a * x + b * y) := by
      calc _ = (a + b) * u - (a * x + b * y) := by ring
        _ = _ := by rw [hab, one_mul]
    rw [ep] at hp
    rw [en] at hn
    dsimp [g]
    nlinarith [congrArg (fun z : ℝ => z * f u) hab]
  have hvhi : 0 < vhi + 1 := by nlinarith [h.var_ge, h.var_le]
  apply sa_convex_quadratic_linear_lower hgc (by simp [g]; ring)
    (half_pos (saMeanRadius_pos hvlo hθ)) (by positivity)
  intro x hx
  have hut : |u| + |x| ≤ saMeanRadius vlo B θ := by linarith
  have hup : |u + x| ≤ saMeanRadius vlo B θ := (abs_add_le u x).trans hut
  have hum : |u - x| ≤ saMeanRadius vlo B θ := (abs_sub u x).trans hut
  have hu' : |u| ≤ saMeanRadius vlo B θ := by have := abs_nonneg x; linarith
  dsimp [g, f]
  rw [h.saGlobalRate_eq_saRate hvlo hθ s hup, h.saGlobalRate_eq_saRate hvlo hθ s hum,
    h.saGlobalRate_eq_saRate hvlo hθ s hu']
  exact h.saRate_three_point_lower hvlo hθ hs hut

end

end PGM
