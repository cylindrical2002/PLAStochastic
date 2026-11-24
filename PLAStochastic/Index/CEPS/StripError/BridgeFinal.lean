import PLAStochastic.Index.CEPS.StripError.Bridge

/-!
# WP9, S-4: the bridge error and its discount derivative

`strip_bridge_error_pt` holds for every `q ≠ 0` of the closed right half-disc; both `U` and the
regular normal bridge are holomorphic in the discount (X7, WP5), so the bound extends to `q = 0`
(`strip_bridge_error_closed`). Both are also holomorphic and polynomially bounded on discs of
radius `≍ l⁻²`, and the error is small at `q` and at `q + h` (direction of increasing `Re q`),
so the one-sided interpolation `norm_deriv_le_of_two_points` controls the discount derivative
(`ceps_strip_bridge_error`): `‖U - Û‖ + ‖∂_q U - ∂_q Û‖ ≤ K (1+l)¹⁸ e^{-c₀ l/32}`, i.e.
`|U - Û| + |𝒟(U - Û)| ≤ K w^p e^{-cw}` for `l ∈ [w/2, 2w]`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open WienerHopf
open scoped NNReal

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
/-- **S-4 on the closed half-disc**, including zero discount. -/
theorem strip_bridge_error_closed {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f Dg) {Kf : ℝ≥0} (hLip : LipschitzWith Kf f)
    {fW : ℝ → ℝ} (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : max dom.stripEntranceWidth 4 ≤ l) {ch : ℝ}
    (hch0 : 0 < ch) (hch : ∀ q : ℂ, 0 ≤ q.re → ch / l ^ 2 ≤ ‖cepsStripEntrance ν 0 μ q l‖)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount / 2) :
    ‖cepsBridge ν f μ q l - (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).regularBridge
        (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q l‖ ≤
      stripBridgeConst dom Dg vlo vhi Kf ch * (1 + l) ^ 11 * Real.exp (-(dom.c₀ / 16) * l) := by
  set ρ := (ν : Measure ℝ).map fun x => 1 - x with hρdef
  by_cases hq00 : q ≠ 0
  · exact strip_bridge_error_pt dom hθ hD hDg hθg hvlo hvhi hν hf hLip hW hμ hq0 hq hq00 hl hch0
      (hch q hq0)
  push Not at hq00
  subst hq00
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hl4 : 4 ≤ l := (le_max_right _ _).trans hl
  have hlE : dom.stripEntranceWidth ≤ l := (le_max_left _ _).trans hl
  have hlN : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hlE)
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  have hact : ContinuousAt (fun z : ℂ => cepsBridge ν f μ z l) 0 :=
    (cepsBandDisc_bridgeSeries_analyticAt hDg hθg hvlo hvhi hν hf (w := l) (l := l) (by linarith)
      (by linarith) (by linarith) (1 + μ) (a := 1) (by norm_num) (q := 0)
      (by simp; positivity [krKappa_pos hDg hvlo hvhi])).continuousAt
  have hnor : ContinuousAt (fun z : ℂ =>
      (cepsNormalData D θ ρ μ z).regularBridge (dom.canonL ρ) μ z l) 0 :=
    ((cepsNormalData_canonical_analyticOnNhd_negative dom hW hθ hD hμ0 (t := 0)
      (by simp; exact dom.c₀_pos) hlN).2 0 ⟨by simp; exact dom.q₀_pos, by
        simp; exact div_pos (cepsNormal_negativeRadius_pos dom hD) (by positivity)⟩).continuousAt
  have hcont : ContinuousAt (fun s : ℝ => ‖cepsBridge ν f μ (s : ℂ) l -
      (cepsNormalData D θ ρ μ (s : ℂ)).regularBridge (dom.canonL ρ) μ (s : ℂ) l‖) 0 := by
    have hF : ContinuousAt (fun z : ℂ => cepsBridge ν f μ z l -
        (cepsNormalData D θ ρ μ z).regularBridge (dom.canonL ρ) μ z l) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hact.sub hnor
    exact (hF.comp (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt).norm
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ‖cepsBridge ν f μ (s : ℂ) l -
      (cepsNormalData D θ ρ μ (s : ℂ)).regularBridge (dom.canonL ρ) μ (s : ℂ) l‖ ≤
      stripBridgeConst dom Dg vlo vhi Kf ch * (1 + l) ^ 11 * Real.exp (-(dom.c₀ / 16) * l) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < dom.renewalDiscount / 2 by positivity)]
      with s hs
    have hs0 : 0 ≤ ((s : ℂ)).re := by simp; exact hs.1.le
    refine strip_bridge_error_pt dom hθ hD hDg hθg hvlo hvhi hν hf hLip hW hμ hs0 ?_
      (by exact_mod_cast hs.1.ne') hl hch0 (hch _ hs0)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    exact hs.2.le
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have := le_of_tendsto ht hev
  simpa using this

include hθ hD in
/-- The bridge error is holomorphic and polynomially bounded on discs of radius `≍ l⁻²`. -/
theorem strip_bridge_disc {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f Dg)
    {fW : ℝ → ℝ} (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : max dom.stripEntranceWidth 4 ≤ l)
    {x : ℂ} (hx0 : 0 ≤ x.re) (hx : ‖x‖ ≤ dom.renewalDiscount / 2) :
    ∀ z ∈ ball x (stripDiscRadius dom Dg vlo vhi l),
      DifferentiableAt ℂ (fun z => cepsBridge ν f μ z l) z ∧
      DifferentiableAt ℂ (fun z => (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ z).regularBridge
        (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ z l) z ∧
      ‖cepsBridge ν f μ z l - (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ z).regularBridge
        (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ z l‖ ≤
        cepsBandMomentConst (cepsBandPinDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0 * l ^ 3 +
          2 * max dom.normalNegativeBridgeBound 0 := by
  set ρ := (ν : Measure ℝ).map fun x => 1 - x with hρdef
  intro z hz
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hl4 : 4 ≤ l := (le_max_right _ _).trans hl
  have hlE : dom.stripEntranceWidth ≤ l := (le_max_left _ _).trans hl
  have hlN : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hlE)
  have hlNC : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hlE
  have hl0 : 0 < l := by linarith
  have hκ := krKappa_pos hDg hvlo hvhi
  have hnr := cepsNormal_negativeRadius_pos dom hD
  have hrDq : dom.renewalDiscount ≤ dom.q₀ := min_le_left _ _
  set r := stripDiscRadius dom Dg vlo vhi l
  have hr1 : r ≤ dom.renewalDiscount / 2 := min_le_left _ _
  have hr2 : r ≤ stripDiscScale dom Dg vlo vhi / l ^ 2 := min_le_right _ _
  have hscale1 : stripDiscScale dom Dg vlo vhi ≤ krKappa Dg vlo vhi / 32 := min_le_left _ _
  have hscale2 : stripDiscScale dom Dg vlo vhi ≤ dom.normalNegativeRadius := min_le_right _ _
  have hl2' : 0 < l ^ 2 := by positivity
  rw [mem_ball, dist_eq_norm] at hz
  have hzn : ‖z‖ < dom.q₀ := by have := norm_sub_norm_le z x; linarith
  have hzre : -r < z.re := by
    have := neg_abs_le (z - x).re
    have := abs_re_le_norm (z - x)
    simp only [sub_re] at *
    linarith
  have hre' : -(krKappa Dg vlo vhi / (32 * l ^ 2)) ≤ z.re := by
    have : stripDiscScale dom Dg vlo vhi / l ^ 2 ≤ krKappa Dg vlo vhi / (32 * l ^ 2) := by
      rw [div_le_div_iff₀ hl2' (by positivity)]
      nlinarith
    linarith
  have hreN : -(dom.normalNegativeRadius / l ^ 2) < z.re := by
    have : stripDiscScale dom Dg vlo vhi / l ^ 2 ≤ dom.normalNegativeRadius / l ^ 2 :=
      div_le_div_of_nonneg_right hscale2 hl2'.le
    linarith
  have hA := cepsBandDisc_bridgeSeries_analyticAt hDg hθg hvlo hvhi hν hf (w := l) (l := l)
    (by linarith) (by linarith) (by linarith) (1 + μ) (a := 1) (by norm_num) hre'
  have hN := (cepsNormalData_canonical_analyticOnNhd_negative dom hW hθ hD hμ0 (t := 0)
    (by simp; exact dom.c₀_pos) hlN).2 z ⟨hzn, hreN⟩
  refine ⟨hA.differentiableAt, hN.differentiableAt, ?_⟩
  have hbA := cepsBandDisc_bridgeSeries_iteratedDeriv_le hDg hθg hvlo hvhi hν hf (w := l) (l := l)
    (by linarith) (by linarith) (by linarith) (1 + μ) (a := 1) (by norm_num) hre' 0
  rw [iteratedDeriv_zero] at hbA
  have hbN := cepsNormalData_canonical_regularBridge_bound_negative dom hW hθ hD hμ0 hzn.le hlNC
    hreN.le
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hrr := dom.norm_cepsRootR_le hW hθ hD hμc hzn.le
  have hrr1 := dom.rmax_one
  have hlinv : 1 / l ≤ 1 := by rw [div_le_one hl0]; linarith
  refine (norm_sub_le _ _).trans (add_le_add hbA ?_)
  refine hbN.trans ?_
  calc dom.normalNegativeBridgeBound * (‖cepsRootR D θ ρ μ z‖ + 1 / l) ≤
      max dom.normalNegativeBridgeBound 0 * (‖cepsRootR D θ ρ μ z‖ + 1 / l) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max dom.normalNegativeBridgeBound 0 * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add (hrr.trans hrr1) hlinv) (le_max_right _ _)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
include hθ hD in
/-- **S-4: the bridge error and its discount derivative**, class-uniform. -/
theorem ceps_strip_bridge_error {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (Kf : ℝ≥0) :
    ∃ K : ℝ, ∀ (ν : ProbabilityMeasure ℝ) (f fW : ℝ → ℝ), RegLaw Dg θg vlo vhi ν →
      CepsGapDensity ν f Dg → LipschitzWith Kf f →
      IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v →
      ∀ μ : ℝ, |μ| ≤ min dom.renewalMu (1 / (64 * Dg)) →
      ∀ q : ℂ, 0 ≤ q.re → ‖q‖ ≤ dom.renewalDiscount / 4 →
      ∀ l : ℝ, max dom.stripEntranceWidth 4 ≤ l →
        ‖cepsBridge ν f μ q l -
            (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).regularBridge
              (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q l‖ +
          ‖deriv (fun q' => cepsBridge ν f μ q' l) q -
            deriv (fun q' => (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q').regularBridge
              (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q' l) q‖ ≤
          K * (1 + l) ^ 18 * Real.exp (-(dom.c₀ / 32) * l) := by
  obtain ⟨ch, hch0, hchb⟩ := cepsBandDisc_stripEntrance_right_lower hDg hθg hvlo hvhi
  set K0 := max (stripBridgeConst dom Dg vlo vhi Kf ch) 0 with hK0def
  have hK0 : 0 ≤ K0 := le_max_right _ _
  set sc := stripDiscScale dom Dg vlo vhi with hscdef
  have hκ := krKappa_pos hDg hvlo hvhi
  have hnr := cepsNormal_negativeRadius_pos dom hD
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  have hsc : 0 < sc := lt_min (by positivity) hnr
  set ρ' := min (dom.renewalDiscount / 2) sc with hρ'def
  have hρ' : 0 < ρ' := lt_min (by positivity) hsc
  set C0 := cepsBandMomentConst (cepsBandPinDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0
  set A := max C0 0 + 2 * max dom.normalNegativeBridgeBound 0 with hAdef
  have hA : 0 ≤ A := by
    have : 0 ≤ max C0 0 := le_max_right _ _
    have : 0 ≤ max dom.normalNegativeBridgeBound 0 := le_max_right _ _
    positivity
  refine ⟨K0 + (8 * K0 / ρ' + 2 * K0 + 32 * A / ρ' ^ 2), ?_⟩
  intro ν f fW hν hf hLip hW μ hμ q hq0 hq l hl
  set ρ := (ν : Measure ℝ).map fun x => 1 - x with hρdef
  have hμR : |μ| ≤ dom.renewalMu := hμ.trans (min_le_left _ _)
  have hμD : |μ| ≤ 1 / (64 * Dg) := hμ.trans (min_le_right _ _)
  have hl4 : 4 ≤ l := (le_max_right _ _).trans hl
  have hl0 : 0 ≤ l := by linarith
  have hc0 := dom.c₀_pos
  have hch : ∀ z : ℂ, 0 ≤ z.re → ch / l ^ 2 ≤ ‖cepsStripEntrance ν 0 μ z l‖ := fun z hz =>
    hchb ν hν l (by linarith) l (by linarith) (by linarith) μ hμD z hz
  have hbase : ∀ z : ℂ, 0 ≤ z.re → ‖z‖ ≤ dom.renewalDiscount / 2 →
      ‖cepsBridge ν f μ z l - (cepsNormalData D θ ρ μ z).regularBridge (dom.canonL ρ) μ z l‖ ≤
        K0 * (1 + l) ^ 11 * Real.exp (-(dom.c₀ / 16) * l) := fun z hz0 hz =>
    (strip_bridge_error_closed dom hθ hD hDg hθg hvlo hvhi hν hf hLip hW hμR hl hch0 hch hz0 hz).trans
      (by gcongr; exact le_max_left _ _)
  -- the interpolation in the direction of increasing `Re q`
  set F : ℂ → ℂ := fun z => cepsBridge ν f μ z l -
    (cepsNormalData D θ ρ μ z).regularBridge (dom.canonL ρ) μ z l with hFdef
  set r := stripDiscRadius dom Dg vlo vhi l with hrdef
  have hl1 : 1 ≤ 1 + l := by linarith
  have hrlow : ρ' / (1 + l) ^ 2 ≤ r := by
    apply le_min
    · calc ρ' / (1 + l) ^ 2 ≤ ρ' / 1 := div_le_div_of_nonneg_left hρ'.le one_pos
            (one_le_pow₀ hl1)
        _ = ρ' := div_one _
        _ ≤ _ := min_le_left _ _
    · exact div_le_div₀ hsc.le (min_le_right _ _) (by positivity) (by nlinarith)
  have hr : 0 < r := lt_of_lt_of_le (div_pos hρ' (by positivity)) hrlow
  have hr1 : r ≤ dom.renewalDiscount / 2 := min_le_left _ _
  have hqh : ‖q‖ ≤ dom.renewalDiscount / 2 := by linarith
  have hdisc := strip_bridge_disc dom hθ hD hDg hθg hvlo hvhi hν hf hW hμR hl hq0 hqh
  set M := C0 * l ^ 3 + 2 * max dom.normalNegativeBridgeBound 0 with hMdef
  have hM : M ≤ A * (1 + l) ^ 3 := by
    have h1 : C0 * l ^ 3 ≤ max C0 0 * (1 + l) ^ 3 :=
      calc C0 * l ^ 3 ≤ max C0 0 * l ^ 3 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C0 0 * (1 + l) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 (by linarith) 3) (le_max_right _ _)
    have h2 : 2 * max dom.normalNegativeBridgeBound 0 ≤
        2 * max dom.normalNegativeBridgeBound 0 * (1 + l) ^ 3 :=
      le_mul_of_one_le_right (by have := le_max_right dom.normalNegativeBridgeBound 0; positivity)
        (one_le_pow₀ hl1)
    rw [hMdef, hAdef]
    nlinarith
  set c := dom.c₀ / 16 with hcdef
  have hc : 0 < c := by positivity
  set h := min (r / 4) (Real.exp (-(c / 2) * l)) with hhdef
  have hh : 0 < h := lt_min (by positivity) (Real.exp_pos _)
  have hh4 : h ≤ r / 4 := min_le_left _ _
  have hz : q + (h : ℂ) ∈ ball q (r / 2) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh]
    linarith
  have hzq : q + (h : ℂ) ≠ q := by
    intro he
    have : (h : ℂ) = 0 := by linear_combination he
    exact hh.ne' (Complex.ofReal_eq_zero.mp this)
  have hDF : DifferentiableOn ℂ F (ball q r) := fun z hz' =>
    ((hdisc z hz').1.sub (hdisc z hz').2.1).differentiableWithinAt
  have hMF : ∀ z ∈ ball q r, ‖F z‖ ≤ M := fun z hz' => (hdisc z hz').2.2
  have hLK := norm_deriv_le_of_two_points hr hDF hMF hz hzq
  have hnorm : ‖q + (h : ℂ) - q‖ = h := by
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  rw [hnorm] at hLK
  set K1 := K0 * (1 + l) ^ 11 with hK1def
  have hK1 : 0 ≤ K1 := by positivity
  have hFq : ‖F q‖ ≤ K1 * Real.exp (-c * l) := hbase q hq0 hqh
  have hFz : ‖F (q + (h : ℂ))‖ ≤ K1 * Real.exp (-c * l) := by
    refine hbase _ (by simp; linarith [hh]) ?_
    calc ‖q + (h : ℂ)‖ ≤ ‖q‖ + h := by
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      _ ≤ dom.renewalDiscount / 4 + r / 4 := add_le_add hq hh4
      _ ≤ _ := by linarith
  have hderivF : ‖deriv F q‖ ≤ 2 * (K1 * Real.exp (-c * l)) / h + 32 * M / r ^ 2 * h := by
    refine hLK.trans ?_
    gcongr
    linarith
  have hbud := interp_budget_le hc hK1 hA hρ' hl0 hrlow hM
  have hdsub : deriv F q = deriv (fun q' => cepsBridge ν f μ q' l) q -
      deriv (fun q' => (cepsNormalData D θ ρ μ q').regularBridge (dom.canonL ρ) μ q' l) q :=
    deriv_sub (hdisc q (mem_ball_self hr)).1 (hdisc q (mem_ball_self hr)).2.1
  have hc2 : c / 2 = dom.c₀ / 32 := by rw [hcdef]; ring
  rw [← hdsub]
  have hp18 : (1 + l) ^ 11 ≤ (1 + l) ^ 18 := pow_le_pow_right₀ hl1 (by norm_num)
  have hE : Real.exp (-c * l) ≤ Real.exp (-(dom.c₀ / 32) * l) :=
    Real.exp_le_exp.mpr (by rw [hcdef]; nlinarith)
  have h1 : ‖F q‖ ≤ K0 * (1 + l) ^ 18 * Real.exp (-(dom.c₀ / 32) * l) := by
    refine hFq.trans ?_
    rw [hK1def]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp18 hK0) hE (Real.exp_pos _).le (by positivity)
  have h2 : ‖deriv F q‖ ≤ (8 * K0 / ρ' + 2 * K0 + 32 * A / ρ' ^ 2) * (1 + l) ^ 18 *
      Real.exp (-(dom.c₀ / 32) * l) := by
    refine hderivF.trans (hbud.trans ?_)
    rw [hK1def, hc2]
    have hE0 : 0 ≤ Real.exp (-(dom.c₀ / 32) * l) := (Real.exp_pos _).le
    have hp : (1 + l) ^ 7 ≤ (1 + l) ^ 18 := pow_le_pow_right₀ hl1 (by norm_num)
    calc (8 * (K0 * (1 + l) ^ 11) / ρ' + 2 * (K0 * (1 + l) ^ 11) + 32 * A / ρ' ^ 2) * (1 + l) ^ 7 *
          Real.exp (-(dom.c₀ / 32) * l) =
        (8 * K0 / ρ' + 2 * K0) * ((1 + l) ^ 11 * (1 + l) ^ 7) * Real.exp (-(dom.c₀ / 32) * l) +
          32 * A / ρ' ^ 2 * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 32) * l) := by ring
      _ ≤ (8 * K0 / ρ' + 2 * K0) * (1 + l) ^ 18 * Real.exp (-(dom.c₀ / 32) * l) +
          32 * A / ρ' ^ 2 * (1 + l) ^ 18 * Real.exp (-(dom.c₀ / 32) * l) := by
          rw [← pow_add]
          gcongr
      _ = _ := by ring
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  ring

end

end PGM
