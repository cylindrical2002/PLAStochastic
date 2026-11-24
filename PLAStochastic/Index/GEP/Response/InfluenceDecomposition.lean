import PLAStochastic.Index.GEP.Response.Defs

/-!
# WP4: the derivative layer of the joint response (JR §3–4)

`research/2026-09-28-gep-closure/joint-response.md` §3–4 turns the pointwise smallness (P) of
the influences, the approximate Lipschitz decomposition (AL) of their derivatives on
`[0, b log ε]`, and the coarse tail (T) into the weighted derivative bound (W), i.e. JR (R).

Real-variable part (§1–4):

* `le_of_ae_le_Ici`: an a.e. inequality between continuous functions on `(0,∞)` holds on `[0,∞)`;
* `abs_le_of_interp`: JR (I), `|F'| ≤ 2S/h + L h + 2ρ` on `(0,R)` when `|F| ≤ S`, `F' = G + r`,
  `Lip G ≤ L`, `|r| ≤ ρ` and `2h ≤ R`;
* `weighted_bound`: (I) on `(0,R)` together with the tail `|F'| ≤ N e^{ζx}` gives
  `|F'| ≤ E e^{ηx}` on `(0,∞)`, `E = 2S/h + L h + 2ρ + N e^{-(η-ζ)R}`;
* `inflDecomp_of_primitive`: the same bound in the form `InflDecomp` for an influence whose
  distance to a quadratic `l₀ + l₁ x + l₂ x²` is at most `S e^{αx}`.

Assembly (§5–9):

* §5: closure of `AEPrimitive`, `KernelApproxLip`, `KernelTail` under sums, scalars and affine
  terms; `OutTest` is monotone in `η`, and `psiVar` is an `OutTest η (2/η + 2)`;
* `quad_coeff_bound`: JR (Q), `|l₂| ≤ Q + 2 S e^{3α}` from the response `Q` to `quadDir`;
* `inflDecomp_of_rates`: JR (W) with the choices of JR §4 (`R = b log ε`,
  `h = ε^{-(1/2+γ/4)}`), giving the rate `ε^{-γ/4} (Λ + 1)`;
* `aePrimitive_outJ`: JR (ID), `J_φ' = H_φ + B_φ - κ_φ j`;
* `inflDecomp_lawJA`, `inflDecomp_outJ`: JR (R) for one law and one test;
* `influenceDecomp_of_leaves`: the leaves imply `InfluenceDecomp`.
-/

namespace PGM

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral

/-! ## 1. From a.e. bounds to pointwise bounds -/

theorem le_of_ae_le_Ioi {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), u x ≤ v x) {x : ℝ} (hx : 0 < x) :
    u x ≤ v x := by
  by_contra hlt
  rw [not_le] at hlt
  have hUo : IsOpen ({y | v y < u y} ∩ Ioi (0 : ℝ)) := (isOpen_lt hv hu).inter isOpen_Ioi
  have hpos : 0 < volume ({y | v y < u y} ∩ Ioi (0 : ℝ)) := hUo.measure_pos volume ⟨x, hlt, hx⟩
  rw [ae_restrict_iff' measurableSet_Ioi, ae_iff] at h
  refine hpos.ne' (measure_mono_null (fun y hy => ?_) h)
  exact Classical.not_imp.2 ⟨hy.2, not_le.2 hy.1⟩

/-- An a.e. inequality on `(0,∞)` between continuous functions holds on `[0,∞)`. -/
theorem le_of_ae_le_Ici {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), u x ≤ v x) {x : ℝ} (hx : 0 ≤ x) :
    u x ≤ v x := by
  have hsub : Ioi (0 : ℝ) ⊆ {y | u y ≤ v y} := fun y hy => le_of_ae_le_Ioi hu hv h hy
  have hcl := (isClosed_le hu hv).closure_subset_iff.2 hsub
  rw [closure_Ioi] at hcl
  exact hcl hx

/-! ## 2. JR (I): derivative interpolation on `[0,R]` -/

/-- **JR (I).**  If `F` is a primitive of `r`, `|F| ≤ S` on `[0,R]`, and `r = G + (r - G)` with
`Lip G ≤ L` on `[0,R]` and `|r - G| ≤ ρ` a.e., then `|r| ≤ 2S/h + L h + 2ρ` a.e. on `(0,R)`
for every `0 < h` with `2h ≤ R`. -/
theorem abs_le_of_interp {F r G : ℝ → ℝ} {R L ρ S h : ℝ} (hh : 0 < h) (hhR : 2 * h ≤ R)
    (hL : 0 ≤ L)
    (hF : ∀ x y, F y - F x = ∫ t in x..y, r t)
    (hrI : ∀ a b, IntervalIntegrable r volume a b)
    (hS : ∀ x ∈ Icc 0 R, |F x| ≤ S)
    (hG : ∀ x ∈ Icc 0 R, ∀ y ∈ Icc 0 R, |G x - G y| ≤ L * |x - y|)
    (hrG : ∀ᵐ x ∂(volume.restrict (Ioo 0 R)), |r x - G x| ≤ ρ) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 R)), |r x| ≤ 2 * S / h + L * h + 2 * ρ := by
  have hGc : ContinuousOn G (Icc 0 R) := by
    intro x hx
    refine Metric.continuousWithinAt_iff.2 fun δ hδ => ⟨δ / (L + 1), by positivity, fun y hy hxy => ?_⟩
    rw [Real.dist_eq] at hxy ⊢
    calc |G y - G x| ≤ L * |y - x| := hG y hy x hx
      _ ≤ L * (δ / (L + 1)) := by gcongr
      _ < δ := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  -- the a.e. bound on the open interval, as an implication on the whole line
  have hrG' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 R → t ≠ 0 → t ≠ R → |r t - G t| ≤ ρ := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hrG] with t ht h1 h2 h3
    exact ht ⟨lt_of_le_of_ne h1.1 (Ne.symm h2), lt_of_le_of_ne h1.2 h3⟩
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  have hR : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ R := compl_mem_ae_iff.2 (measure_singleton R)
  -- the pointwise bound on `G`
  have hGx : ∀ x ∈ Icc 0 R, |G x| ≤ 2 * S / h + L * h + ρ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ Icc 0 R, |y - x| = h := by
      by_cases hc : x + h ≤ R
      · exact ⟨x + h, ⟨by linarith [hx.1], hc⟩, by rw [add_sub_cancel_left, abs_of_pos hh]⟩
      · refine ⟨x - h, ⟨by linarith, by linarith [hx.2]⟩, ?_⟩
        rw [sub_sub_cancel_left, abs_neg, abs_of_pos hh]
    have huIcc : uIcc x y ⊆ Icc 0 R := uIcc_subset_Icc hx hy
    have hGI : IntervalIntegrable G volume x y := (hGc.mono huIcc).intervalIntegrable
    have hcI : IntervalIntegrable (fun _ => G x) volume x y := intervalIntegrable_const
    have e1 : ∫ t in x..y, G x = (∫ t in x..y, r t) - (∫ t in x..y, (r t - G t)) -
        ∫ t in x..y, (G t - G x) := by
      rw [intervalIntegral.integral_sub (hrI x y) hGI, intervalIntegral.integral_sub hGI hcI]
      ring
    have b1 : |∫ t in x..y, r t| ≤ 2 * S := by
      rw [← hF x y]
      calc |F y - F x| ≤ |F y| + |F x| := abs_sub _ _
        _ ≤ S + S := add_le_add (hS y hy) (hS x hx)
        _ = 2 * S := by ring
    have b2 : |∫ t in x..y, (r t - G t)| ≤ ρ * h := by
      rw [← hxy, ← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
      filter_upwards [hrG', h0, hR] with t ht ht0 htR htI
      exact ht (huIcc (uIoc_subset_uIcc htI)) ht0 htR
    have b3 : |∫ t in x..y, (G t - G x)| ≤ L * h * h := by
      rw [← Real.norm_eq_abs, show L * h * h = (L * h) * |y - x| by rw [hxy]]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      have htI : t ∈ uIcc x y := uIoc_subset_uIcc ht
      rw [Real.norm_eq_abs]
      calc |G t - G x| ≤ L * |t - x| := hG t (huIcc htI) x hx
        _ ≤ L * h := by
            gcongr
            rw [← hxy]
            exact abs_sub_left_of_mem_uIcc htI
    have hmain : h * |G x| ≤ 2 * S + ρ * h + L * h * h := by
      have e2 : |∫ t in x..y, G x| = h * |G x| := by
        rw [intervalIntegral.integral_const, smul_eq_mul, abs_mul, hxy]
      rw [← e2, e1]
      calc |(∫ t in x..y, r t) - (∫ t in x..y, (r t - G t)) - ∫ t in x..y, (G t - G x)|
          ≤ |∫ t in x..y, r t| + |∫ t in x..y, (r t - G t)| + |∫ t in x..y, (G t - G x)| := by
            exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ 2 * S + ρ * h + L * h * h := add_le_add (add_le_add b1 b2) b3
    have e3 : (2 * S + ρ * h + L * h * h) / h = 2 * S / h + L * h + ρ := by
      field_simp
      ring
    rw [← e3, le_div_iff₀ hh, mul_comm]
    exact hmain
  filter_upwards [hrG, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  have hxI' : x ∈ Icc 0 R := Ioo_subset_Icc_self hxI
  calc |r x| ≤ |r x - G x| + |G x| := by
        have := abs_add_le (r x - G x) (G x)
        rwa [sub_add_cancel] at this
    _ ≤ ρ + (2 * S / h + L * h + ρ) := add_le_add hx (hGx x hxI')
    _ = 2 * S / h + L * h + 2 * ρ := by ring

/-! ## 3. The weighted bound on `(0,∞)` -/

/-- (I) on `(0,R)` and the tail `|r| ≤ N e^{ζx}` on `(0,∞)` give `|r| ≤ E e^{ηx}` on `(0,∞)`. -/
theorem weighted_bound {F r G : ℝ → ℝ} {R L ρ S h N η ζ : ℝ} (hh : 0 < h) (hhR : 2 * h ≤ R)
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hS0 : 0 ≤ S) (hN : 0 ≤ N) (hη : 0 ≤ η) (hζη : ζ ≤ η)
    (hF : ∀ x y, F y - F x = ∫ t in x..y, r t)
    (hrI : ∀ a b, IntervalIntegrable r volume a b)
    (hS : ∀ x ∈ Icc 0 R, |F x| ≤ S)
    (hG : ∀ x ∈ Icc 0 R, ∀ y ∈ Icc 0 R, |G x - G y| ≤ L * |x - y|)
    (hrG : ∀ᵐ x ∂(volume.restrict (Ioo 0 R)), |r x - G x| ≤ ρ)
    (htail : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |r x| ≤ N * Real.exp (ζ * x)) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |r x| ≤
      (2 * S / h + L * h + 2 * ρ + N * Real.exp (-(η - ζ) * R)) * Real.exp (η * x) := by
  have hI := (ae_restrict_iff' measurableSet_Ioo).1
    (abs_le_of_interp hh hhR hL hF hrI hS hG hrG)
  have hT := (ae_restrict_iff' measurableSet_Ioi).1 htail
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hI, hT] with x hxI hxT hx0
  have hx0' : (0 : ℝ) < x := hx0
  have hE1 : 0 ≤ 2 * S / h + L * h + 2 * ρ := by positivity
  have hE2 : 0 ≤ N * Real.exp (-(η - ζ) * R) := by positivity
  have hexp : 1 ≤ Real.exp (η * x) := Real.one_le_exp (by positivity)
  by_cases hxR : x < R
  · calc |r x| ≤ 2 * S / h + L * h + 2 * ρ := hxI ⟨hx0', hxR⟩
      _ ≤ 2 * S / h + L * h + 2 * ρ + N * Real.exp (-(η - ζ) * R) := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hexp
  · rw [not_lt] at hxR
    calc |r x| ≤ N * Real.exp (ζ * x) := hxT hx0
      _ = N * Real.exp (-(η - ζ) * x) * Real.exp (η * x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ N * Real.exp (-(η - ζ) * R) * Real.exp (η * x) := by
          have hxR' : -(η - ζ) * x ≤ -(η - ζ) * R := by
            have := mul_le_mul_of_nonneg_left hxR (sub_nonneg.2 hζη)
            linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hxR') hN)
            (Real.exp_pos _).le
      _ ≤ _ := by
          gcongr
          linarith

/-! ## 4. The decomposition `InflDecomp` from a primitive -/

/-- `∫_x^y (l₁ + 2 l₂ t) dt = l₁ (y - x) + l₂ (y² - x²)`. -/
theorem integral_affine (l₁ l₂ x y : ℝ) :
    ∫ t in x..y, (l₁ + 2 * l₂ * t) = l₁ * (y - x) + l₂ * (y ^ 2 - x ^ 2) := by
  have h3 : IntervalIntegrable (fun t : ℝ => 2 * l₂ * t) volume x y :=
    (by fun_prop : Continuous fun t : ℝ => 2 * l₂ * t).intervalIntegrable x y
  rw [intervalIntegral.integral_add intervalIntegrable_const h3, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

theorem intervalIntegrable_of_aePrimitive {J j : ℝ → ℝ} (h : AEPrimitive J j) (a b : ℝ) :
    IntervalIntegrable j volume a b :=
  ((h.1 a).symm).trans (h.1 b)

/-- **JR (W) for one influence.**  If `J = c + ∫_0^x j` a.e., `|J - (l₀ + l₁x + l₂x²)| ≤ S e^{αx}`
a.e., and `r = j - l₁ - 2l₂x` has the (AL) shape on `(0,R)` and the tail `N e^{ζx}`, then
`J' = l₁ + 2 l₂ x + r` with `|r| ≤ E e^{ηx}`, `E = 2S e^{αR}/h + L h + 2ρ + N e^{-(η-ζ)R}`. -/
theorem inflDecomp_of_primitive {J j : ℝ → ℝ} (hJ : AEPrimitive J j) {l₀ l₁ l₂ : ℝ}
    {R L ρ S α h N η ζ K : ℝ} (hh : 0 < h) (hhR : 2 * h ≤ R) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hS0 : 0 ≤ S) (hα : 0 ≤ α) (hN : 0 ≤ N) (hη : 0 ≤ η) (hζη : ζ ≤ η) (hK : |l₂| ≤ K)
    (hsmall : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |J x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤ S * Real.exp (α * x))
    (hlip : KernelApproxLip R L ρ (fun t => j t - l₁ - 2 * l₂ * t))
    (htail : KernelTail N ζ (fun t => j t - l₁ - 2 * l₂ * t)) :
    InflDecomp η (2 * (S * Real.exp (α * R)) / h + L * h + 2 * ρ +
      N * Real.exp (-(η - ζ) * R)) K J := by
  obtain ⟨hII, c, hc⟩ := hJ
  have hjI := intervalIntegrable_of_aePrimitive ⟨hII, c, hc⟩
  set r : ℝ → ℝ := fun t => j t - l₁ - 2 * l₂ * t with hr_def
  have hpI : ∀ a b, IntervalIntegrable (fun t : ℝ => l₁ + 2 * l₂ * t) volume a b := fun a b =>
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable a b
  have hrI : ∀ a b, IntervalIntegrable r volume a b := fun a b =>
    ((hjI a b).sub (hpI a b)).congr fun t _ => by simp only [hr_def]; ring
  -- the continuous version of `J - quadratic`
  set F : ℝ → ℝ := fun x => c + (∫ t in (0 : ℝ)..x, j t) - (l₀ + l₁ * x + l₂ * x ^ 2)
    with hF_def
  have hFc : Continuous F :=
    ((continuous_const.add (intervalIntegral.continuous_primitive hjI 0)).sub
      (by fun_prop))
  have hFd : ∀ x y, F y - F x = ∫ t in x..y, r t := by
    intro x y
    have e1 : (∫ t in (0 : ℝ)..y, j t) - ∫ t in (0 : ℝ)..x, j t = ∫ t in x..y, j t :=
      intervalIntegral.integral_interval_sub_left (hjI 0 y) (hjI 0 x)
    have e2 : ∫ t in x..y, r t = (∫ t in x..y, j t) - ∫ t in x..y, (l₁ + 2 * l₂ * t) := by
      rw [← intervalIntegral.integral_sub (hjI x y) (hpI x y)]
      congr 1; ext t; simp only [hr_def]; ring
    rw [e2, integral_affine, ← e1]
    simp only [hF_def]
    ring
  -- `|F| ≤ S e^{αx}` everywhere on `[0,∞)`
  have hFae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |F x| ≤ S * Real.exp (α * x) := by
    filter_upwards [hsmall, hc] with x hx hcx
    simpa only [hF_def, ← hcx] using hx
  have hFall : ∀ x, 0 ≤ x → |F x| ≤ S * Real.exp (α * x) := fun x hx =>
    le_of_ae_le_Ici (continuous_abs.comp hFc)
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      hFae hx
  have hS : ∀ x ∈ Icc 0 R, |F x| ≤ S * Real.exp (α * R) := fun x hx =>
    (hFall x hx.1).trans (by gcongr; exact hx.2)
  obtain ⟨G, hG, hrG⟩ := hlip
  have hw := weighted_bound (F := F) (r := r) (G := G) hh hhR hL hρ (by positivity) hN hη hζη
    hFd hrI hS hG hrG htail
  refine ⟨l₁, l₂, r, hK, ?_, hw⟩
  have hfun : (fun t => l₁ + 2 * l₂ * t + r t) = j := by
    funext t
    simp only [hr_def]
    ring
  rw [hfun]
  exact ⟨hII, c, hc⟩

/-! ## 5. Algebra of the interface shapes -/

theorem InflDecomp.mono {η ε ε' K K' : ℝ} {J : ℝ → ℝ} (h : InflDecomp η ε K J) (hε : ε ≤ ε')
    (hK : K ≤ K') : InflDecomp η ε' K' J := by
  obtain ⟨a, q, r, hq, hP, hr⟩ := h
  refine ⟨a, q, r, hq.trans hK, hP, ?_⟩
  filter_upwards [hr] with t ht using ht.trans (mul_le_mul_of_nonneg_right hε (Real.exp_pos _).le)

theorem OutTest.M_nonneg {η M : ℝ} {ψ : ℝ → ℝ} (h : OutTest η M ψ) : 0 ≤ M := by
  have h0 := h.2 0 le_rfl
  rw [mul_zero, Real.exp_zero, mul_one] at h0
  exact (abs_nonneg _).trans h0

theorem OutTest.mono {η η' M : ℝ} {ψ : ℝ → ℝ} (h : OutTest η M ψ) (hηη : η ≤ η') :
    OutTest η' M ψ :=
  ⟨h.1, fun x hx => (h.2 x hx).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hηη hx)) h.M_nonneg)⟩

/-- The variance test `φ(y) = y² - 2y` has `|φ'(x)| = |2x - 2| ≤ (2/η + 2) e^{ηx}` on `x ≥ 0`. -/
theorem outTest_psiVar {η : ℝ} (hη : 0 < η) : OutTest η (2 / η + 2) psiVar := by
  refine ⟨(by fun_prop : Continuous fun y : ℝ => 2 * y - 2).measurable, fun x hx => ?_⟩
  have h1 : 1 ≤ Real.exp (η * x) := Real.one_le_exp (by positivity)
  have h2 : η * x ≤ Real.exp (η * x) := by linarith [Real.add_one_le_exp (η * x)]
  have h3 : 2 * x ≤ 2 / η * Real.exp (η * x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    linarith
  have h4 : 0 ≤ 2 / η * Real.exp (η * x) := by positivity
  show |2 * x - 2| ≤ (2 / η + 2) * Real.exp (η * x)
  rw [abs_le]
  constructor <;> nlinarith

theorem AEPrimitive.add {J₁ J₂ j₁ j₂ : ℝ → ℝ} (h₁ : AEPrimitive J₁ j₁) (h₂ : AEPrimitive J₂ j₂) :
    AEPrimitive (fun x => J₁ x + J₂ x) (fun t => j₁ t + j₂ t) := by
  obtain ⟨hI₁, c₁, hc₁⟩ := h₁
  obtain ⟨hI₂, c₂, hc₂⟩ := h₂
  refine ⟨fun R => (hI₁ R).add (hI₂ R), c₁ + c₂, ?_⟩
  filter_upwards [hc₁, hc₂] with x hx₁ hx₂
  rw [hx₁, hx₂, intervalIntegral.integral_add (hI₁ x) (hI₂ x)]
  ring

theorem AEPrimitive.const_mul {J j : ℝ → ℝ} (h : AEPrimitive J j) (k : ℝ) :
    AEPrimitive (fun x => k * J x) (fun t => k * j t) := by
  obtain ⟨hI, c, hc⟩ := h
  refine ⟨fun R => (hI R).const_mul k, k * c, ?_⟩
  filter_upwards [hc] with x hx
  rw [hx, intervalIntegral.integral_const_mul]
  ring

theorem AEPrimitive.poly (a₀ a₁ a₂ : ℝ) :
    AEPrimitive (fun x => a₀ + a₁ * x + a₂ * x ^ 2) (fun t => a₁ + 2 * a₂ * t) := by
  refine ⟨fun R => (by fun_prop : Continuous fun t : ℝ => a₁ + 2 * a₂ * t).intervalIntegrable 0 R,
    a₀, Eventually.of_forall fun x => ?_⟩
  rw [integral_affine]
  ring

theorem KernelApproxLip.mono {R L L' ρ ρ' : ℝ} {j : ℝ → ℝ} (h : KernelApproxLip R L ρ j)
    (hL : L ≤ L') (hρ : ρ ≤ ρ') : KernelApproxLip R L' ρ' j := by
  obtain ⟨G, hG, hr⟩ := h
  refine ⟨G, fun x hx y hy => (hG x hx y hy).trans
    (mul_le_mul_of_nonneg_right hL (abs_nonneg _)), ?_⟩
  filter_upwards [hr] with x hx using hx.trans hρ

theorem KernelApproxLip.add {R L₁ L₂ ρ₁ ρ₂ : ℝ} {j₁ j₂ : ℝ → ℝ}
    (h₁ : KernelApproxLip R L₁ ρ₁ j₁) (h₂ : KernelApproxLip R L₂ ρ₂ j₂) :
    KernelApproxLip R (L₁ + L₂) (ρ₁ + ρ₂) (fun t => j₁ t + j₂ t) := by
  obtain ⟨G₁, hG₁, hr₁⟩ := h₁
  obtain ⟨G₂, hG₂, hr₂⟩ := h₂
  refine ⟨fun t => G₁ t + G₂ t, fun x hx y hy => ?_, ?_⟩
  · calc |G₁ x + G₂ x - (G₁ y + G₂ y)| = |(G₁ x - G₁ y) + (G₂ x - G₂ y)| := by ring_nf
      _ ≤ |G₁ x - G₁ y| + |G₂ x - G₂ y| := abs_add_le _ _
      _ ≤ L₁ * |x - y| + L₂ * |x - y| := add_le_add (hG₁ x hx y hy) (hG₂ x hx y hy)
      _ = (L₁ + L₂) * |x - y| := by ring
  · filter_upwards [hr₁, hr₂] with x hx₁ hx₂
    calc |j₁ x + j₂ x - (G₁ x + G₂ x)| = |(j₁ x - G₁ x) + (j₂ x - G₂ x)| := by ring_nf
      _ ≤ |j₁ x - G₁ x| + |j₂ x - G₂ x| := abs_add_le _ _
      _ ≤ ρ₁ + ρ₂ := add_le_add hx₁ hx₂

theorem KernelApproxLip.const_mul {R L ρ : ℝ} {j : ℝ → ℝ} (h : KernelApproxLip R L ρ j)
    (k : ℝ) : KernelApproxLip R (|k| * L) (|k| * ρ) (fun t => k * j t) := by
  obtain ⟨G, hG, hr⟩ := h
  refine ⟨fun t => k * G t, fun x hx y hy => ?_, ?_⟩
  · calc |k * G x - k * G y| = |k| * |G x - G y| := by rw [← mul_sub, abs_mul]
      _ ≤ |k| * (L * |x - y|) := mul_le_mul_of_nonneg_left (hG x hx y hy) (abs_nonneg k)
      _ = |k| * L * |x - y| := by ring
  · filter_upwards [hr] with x hx
    calc |k * j x - k * G x| = |k| * |j x - G x| := by rw [← mul_sub, abs_mul]
      _ ≤ |k| * ρ := mul_le_mul_of_nonneg_left hx (abs_nonneg k)

theorem KernelApproxLip.const_mul_le {R L ρ k c : ℝ} {j : ℝ → ℝ} (h : KernelApproxLip R L ρ j)
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hk : |k| ≤ c) :
    KernelApproxLip R (c * L) (c * ρ) (fun t => k * j t) :=
  (h.const_mul k).mono (mul_le_mul_of_nonneg_right hk hL) (mul_le_mul_of_nonneg_right hk hρ)

theorem KernelApproxLip.affine (R c₀ c₁ : ℝ) :
    KernelApproxLip R |c₁| 0 (fun t => c₀ + c₁ * t) := by
  refine ⟨fun t => c₀ + c₁ * t, fun x _ y _ => le_of_eq ?_, Eventually.of_forall fun x => ?_⟩
  · show |c₀ + c₁ * x - (c₀ + c₁ * y)| = |c₁| * |x - y|
    rw [← abs_mul]
    congr 1
    ring
  · show |c₀ + c₁ * x - (c₀ + c₁ * x)| ≤ 0
    simp

/-- A kernel within `ρ e^{αx}` of a constant is (AL) on `(0,R)` with `L = 0`. -/
theorem kernelApproxLip_of_ae {R ρ α a : ℝ} {H : ℝ → ℝ} (hρ : 0 ≤ ρ) (hα : 0 ≤ α)
    (h : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |H x - a| ≤ ρ * Real.exp (α * x)) :
    KernelApproxLip R 0 (ρ * Real.exp (α * R)) H := by
  refine ⟨fun _ => a, fun x _ y _ => by simp, ?_⟩
  have h' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self : Ioo (0 : ℝ) R ⊆ Ioi 0) h
  filter_upwards [h', ae_restrict_mem measurableSet_Ioo] with x hx hxI
  refine hx.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hρ)
  exact mul_le_mul_of_nonneg_left hxI.2.le hα

theorem KernelTail.mono {N N' ζ : ℝ} {j : ℝ → ℝ} (h : KernelTail N ζ j) (hN : N ≤ N') :
    KernelTail N' ζ j := by
  filter_upwards [h] with x hx using hx.trans (mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le)

theorem KernelTail.add {N₁ N₂ ζ : ℝ} {j₁ j₂ : ℝ → ℝ} (h₁ : KernelTail N₁ ζ j₁)
    (h₂ : KernelTail N₂ ζ j₂) : KernelTail (N₁ + N₂) ζ (fun t => j₁ t + j₂ t) := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc |j₁ x + j₂ x| ≤ |j₁ x| + |j₂ x| := abs_add_le _ _
    _ ≤ N₁ * Real.exp (ζ * x) + N₂ * Real.exp (ζ * x) := add_le_add hx₁ hx₂
    _ = (N₁ + N₂) * Real.exp (ζ * x) := by ring

theorem KernelTail.const_mul {N ζ : ℝ} {j : ℝ → ℝ} (h : KernelTail N ζ j) (k : ℝ) :
    KernelTail (|k| * N) ζ (fun t => k * j t) := by
  filter_upwards [h] with x hx
  calc |k * j x| = |k| * |j x| := abs_mul _ _
    _ ≤ |k| * (N * Real.exp (ζ * x)) := mul_le_mul_of_nonneg_left hx (abs_nonneg k)
    _ = |k| * N * Real.exp (ζ * x) := by ring

theorem KernelTail.const_mul_le {N ζ k c : ℝ} {j : ℝ → ℝ} (h : KernelTail N ζ j) (hN : 0 ≤ N)
    (hk : |k| ≤ c) : KernelTail (c * N) ζ (fun t => k * j t) :=
  (h.const_mul k).mono (mul_le_mul_of_nonneg_right hk hN)

theorem KernelTail.affine {ζ : ℝ} (hζ : 0 < ζ) (c₀ c₁ : ℝ) :
    KernelTail (|c₀| + |c₁| * ζ⁻¹) ζ (fun t => c₀ + c₁ * t) := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
  have h1 : 1 ≤ Real.exp (ζ * x) := Real.one_le_exp (by positivity)
  have h2 : ζ * x ≤ Real.exp (ζ * x) := by linarith [Real.add_one_le_exp (ζ * x)]
  have h3 : x ≤ Real.exp (ζ * x) * ζ⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hζ]
    linarith
  show |c₀ + c₁ * x| ≤ (|c₀| + |c₁| * ζ⁻¹) * Real.exp (ζ * x)
  calc |c₀ + c₁ * x| ≤ |c₀| + |c₁ * x| := abs_add_le _ _
    _ = |c₀| + |c₁| * x := by rw [abs_mul, abs_of_nonneg hx0]
    _ ≤ |c₀| * Real.exp (ζ * x) + |c₁| * (Real.exp (ζ * x) * ζ⁻¹) :=
        add_le_add (le_mul_of_one_le_right (abs_nonneg _) h1)
          (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
    _ = (|c₀| + |c₁| * ζ⁻¹) * Real.exp (ζ * x) := by ring

theorem lip_weaken {K s p Λ : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) (hpΛ : p ≤ Λ) :
    K * s * p ≤ |K| * s * Λ :=
  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hs) hp).trans
    (mul_le_mul_of_nonneg_left hpΛ (mul_nonneg (abs_nonneg K) hs))

theorem rho_weaken {K eps e : ℝ} (heps : 0 < eps) (he : 1 ≤ e) : K / eps ≤ |K| / eps * e :=
  (div_le_div_of_nonneg_right (le_abs_self K) heps.le).trans
    (le_mul_of_one_le_right (div_nonneg (abs_nonneg K) heps.le) he)

theorem tail_weaken {K eps : ℝ} {n m : ℕ} (heps : 1 ≤ eps) (hnm : n ≤ m) :
    K * eps ^ n ≤ |K| * eps ^ m :=
  mul_le_mul (le_abs_self K) (pow_le_pow_right₀ heps hnm) (pow_nonneg (by linarith) n)
    (abs_nonneg K)

/-! ## 6. JR (Q): the quadratic coefficient -/

theorem integral_quad (l₀ l₁ l₂ a b : ℝ) :
    ∫ t in a..b, (l₀ + l₁ * t + l₂ * t ^ 2) =
      l₀ * (b - a) + l₁ * ((b ^ 2 - a ^ 2) / 2) + l₂ * ((b ^ 3 - a ^ 3) / 3) := by
  have h1 : IntervalIntegrable (fun t : ℝ => l₀ + l₁ * t) volume a b :=
    (by fun_prop : Continuous fun t : ℝ => l₀ + l₁ * t).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun t : ℝ => l₂ * t ^ 2) volume a b :=
    (by fun_prop : Continuous fun t : ℝ => l₂ * t ^ 2).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun t : ℝ => l₁ * t) volume a b :=
    (by fun_prop : Continuous fun t : ℝ => l₁ * t).intervalIntegrable a b
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_add intervalIntegrable_const h3,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow, smul_eq_mul]
  push_cast
  ring

theorem integrableOn_of_aePrimitive {J j : ℝ → ℝ} (hJ : AEPrimitive J j) {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn J (Ioc a b) := by
  obtain ⟨hII, c, hc⟩ := hJ
  have hjI := intervalIntegrable_of_aePrimitive ⟨hII, c, hc⟩
  have hFc : Continuous fun x => c + ∫ t in (0 : ℝ)..x, j t :=
    continuous_const.add (intervalIntegral.continuous_primitive hjI 0)
  refine hFc.integrableOn_Ioc.congr_fun_ae ?_
  have h := ae_restrict_of_ae_restrict_of_subset
    (show Ioc a b ⊆ Ioi 0 from fun x hx => lt_of_le_of_lt ha hx.1) hc
  filter_upwards [h] with x hx using hx.symm

/-- `∫ f ω = ½ ∫_0^1 f - ∫_1^2 f + ½ ∫_2^3 f` for the calibration direction `ω = quadDir`. -/
theorem integral_mul_quadDir {f : ℝ → ℝ} (hf : IntegrableOn f (Ioc 0 3)) :
    ∫ x, f x * quadDir x = 1 / 2 * (∫ x in (0 : ℝ)..1, f x) - (∫ x in (1 : ℝ)..2, f x) +
      1 / 2 * ∫ x in (2 : ℝ)..3, f x := by
  have e : (fun x => f x * quadDir x) = fun x => 1 / 2 * (Ioc (0 : ℝ) 1).indicator f x -
      (Ioc (1 : ℝ) 2).indicator f x + 1 / 2 * (Ioc (2 : ℝ) 3).indicator f x := by
    funext x
    simp only [quadDir, Set.indicator_apply]
    split_ifs <;> ring
  have i1 : Integrable ((Ioc (0 : ℝ) 1).indicator f) :=
    (hf.mono_set (Ioc_subset_Ioc le_rfl (by norm_num))).integrable_indicator measurableSet_Ioc
  have i2 : Integrable ((Ioc (1 : ℝ) 2).indicator f) :=
    (hf.mono_set (Ioc_subset_Ioc (by norm_num) (by norm_num))).integrable_indicator
      measurableSet_Ioc
  have i3 : Integrable ((Ioc (2 : ℝ) 3).indicator f) :=
    (hf.mono_set (Ioc_subset_Ioc (by norm_num) le_rfl)).integrable_indicator measurableSet_Ioc
  have i1' : Integrable (fun x => 1 / 2 * (Ioc (0 : ℝ) 1).indicator f x) := i1.const_mul _
  have i3' : Integrable (fun x => 1 / 2 * (Ioc (2 : ℝ) 3).indicator f x) := i3.const_mul _
  have i12 : Integrable (fun x => 1 / 2 * (Ioc (0 : ℝ) 1).indicator f x -
      (Ioc (1 : ℝ) 2).indicator f x) := i1'.sub i2
  rw [e, MeasureTheory.integral_add i12 i3', MeasureTheory.integral_sub i1' i2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le one_le_two,
    intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 3)]

/-- **JR (Q).**  If `J` has a primitive and is within `S e^{αx}` of `l₀ + l₁ x + l₂ x²`, then the
quadratic coefficient is controlled by the response to `quadDir`: `|l₂| ≤ Q + 2 S e^{3α}`. -/
theorem quad_coeff_bound {J j : ℝ → ℝ} (hJ : AEPrimitive J j) {l₀ l₁ l₂ S α Q : ℝ}
    (hα : 0 ≤ α)
    (hsmall : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |J x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤ S * Real.exp (α * x))
    (hQ : |∫ x, J x * quadDir x| ≤ Q) (hS : 0 ≤ S) :
    |l₂| ≤ Q + 2 * (S * Real.exp (α * 3)) := by
  have hqc : Continuous fun x : ℝ => l₀ + l₁ * x + l₂ * x ^ 2 := by fun_prop
  have hJI : ∀ a b : ℝ, 0 ≤ a → a ≤ b → IntervalIntegrable J volume a b := fun a b ha hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (integrableOn_of_aePrimitive hJ ha)
  have hsm := (ae_restrict_iff' measurableSet_Ioi).1 hsmall
  have piece : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 3 →
      ∃ E, |E| ≤ S * Real.exp (α * 3) * (b - a) ∧ (∫ x in a..b, J x) =
        l₀ * (b - a) + l₁ * ((b ^ 2 - a ^ 2) / 2) + l₂ * ((b ^ 3 - a ^ 3) / 3) + E := by
    intro a b ha hab hb
    refine ⟨∫ x in a..b, (J x - (l₀ + l₁ * x + l₂ * x ^ 2)), ?_, ?_⟩
    · have hn := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b)
        (C := S * Real.exp (α * 3)) (f := fun x => J x - (l₀ + l₁ * x + l₂ * x ^ 2)) ?_
      · rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at hn
      filter_upwards [hsm] with x hx hxI
      rw [uIoc_of_le hab] at hxI
      rw [Real.norm_eq_abs]
      refine (hx (lt_of_le_of_lt ha hxI.1)).trans ?_
      gcongr
      linarith [hxI.2]
    · rw [intervalIntegral.integral_sub (hJI a b ha hab) (hqc.intervalIntegrable a b),
        integral_quad]
      ring
  obtain ⟨E₁, hE₁, e₁⟩ := piece 0 1 le_rfl zero_le_one (by norm_num)
  obtain ⟨E₂, hE₂, e₂⟩ := piece 1 2 zero_le_one one_le_two (by norm_num)
  obtain ⟨E₃, hE₃, e₃⟩ := piece 2 3 zero_le_two (by norm_num) le_rfl
  have hdec := integral_mul_quadDir (integrableOn_of_aePrimitive (a := 0) (b := 3) hJ le_rfl)
  rw [e₁, e₂, e₃] at hdec
  have hl : l₂ = (∫ x, J x * quadDir x) - (1 / 2 * E₁ - E₂ + 1 / 2 * E₃) := by
    rw [hdec]
    ring
  obtain ⟨hA1, hA2⟩ := abs_le.1 hQ
  obtain ⟨h11, h12⟩ := abs_le.1 hE₁
  obtain ⟨h21, h22⟩ := abs_le.1 hE₂
  obtain ⟨h31, h32⟩ := abs_le.1 hE₃
  rw [hl, abs_le]
  constructor <;> linarith

/-! ## 7. JR (W) with the rates of §4 -/

/-- The bookkeeping of JR §4 in logarithmic variables `u = log ε`: with `h = e^{-(1/2+γ/4)u}`,
`R = b u`, all four terms of the weighted bound are `O(e^{-γu/4} (Λ + 1))`. -/
theorem rate_ineq {u b α β γ η ζ Λ A₁ A₂ A₃ A₄ A₅ : ℝ} {Pn : ℕ} (hu0 : 0 ≤ u) (hγ : 0 < γ)
    (hγ2 : γ ≤ 1 / 2) (hβ : 1 / 2 + γ ≤ β) (hαb : α * b ≤ γ / 2)
    (hbP : (Pn : ℝ) + 2 ≤ (η - ζ) * b) (hΛ : 0 ≤ Λ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hA₃ : 0 ≤ A₃) (hA₄ : 0 ≤ A₄) (hA₅ : 0 ≤ A₅) :
    2 * (A₁ * Real.exp (-β * u) * Real.exp (α * (b * u))) / Real.exp (-(1 / 2 + γ / 4) * u) +
      (A₂ * Real.exp (u / 2) * Λ + A₃) * Real.exp (-(1 / 2 + γ / 4) * u) +
      2 * (A₄ * Real.exp (-u) * Real.exp (α * (b * u))) +
      A₅ * Real.exp (Pn * u) * Real.exp (-(η - ζ) * (b * u)) ≤
    (2 * A₁ + A₂ + A₃ + 2 * A₄ + A₅) * (Real.exp (-(γ / 4) * u) * (Λ + 1)) := by
  have h1 : (1 / 2 + γ) * u ≤ β * u := mul_le_mul_of_nonneg_right hβ hu0
  have h2 : α * b * u ≤ γ / 2 * u := mul_le_mul_of_nonneg_right hαb hu0
  have h3 : γ * u ≤ 1 / 2 * u := mul_le_mul_of_nonneg_right hγ2 hu0
  have h4 : ((Pn : ℝ) + 2) * u ≤ (η - ζ) * b * u := mul_le_mul_of_nonneg_right hbP hu0
  have hγu : 0 ≤ γ * u := mul_nonneg hγ.le hu0
  have hX0 : 0 < Real.exp (-(γ / 4) * u) := Real.exp_pos _
  have T1 : 2 * (A₁ * Real.exp (-β * u) * Real.exp (α * (b * u))) /
      Real.exp (-(1 / 2 + γ / 4) * u) ≤ 2 * A₁ * Real.exp (-(γ / 4) * u) := by
    rw [div_le_iff₀ (Real.exp_pos _), mul_assoc A₁, ← Real.exp_add, mul_assoc (2 * A₁),
      ← Real.exp_add]
    have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (show -β * u + α * (b * u) ≤ -(γ / 4) * u + -(1 / 2 + γ / 4) * u by linarith)) hA₁
    linarith
  have T2 : (A₂ * Real.exp (u / 2) * Λ + A₃) * Real.exp (-(1 / 2 + γ / 4) * u) ≤
      (A₂ * Λ + A₃) * Real.exp (-(γ / 4) * u) := by
    have e5 : Real.exp (u / 2) * Real.exp (-(1 / 2 + γ / 4) * u) = Real.exp (-(γ / 4) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e6 : Real.exp (-(1 / 2 + γ / 4) * u) ≤ Real.exp (-(γ / 4) * u) :=
      Real.exp_le_exp.2 (by linarith)
    have e7 : (A₂ * Real.exp (u / 2) * Λ + A₃) * Real.exp (-(1 / 2 + γ / 4) * u) =
        A₂ * Λ * (Real.exp (u / 2) * Real.exp (-(1 / 2 + γ / 4) * u)) +
          A₃ * Real.exp (-(1 / 2 + γ / 4) * u) := by ring
    rw [e7, e5]
    have := mul_le_mul_of_nonneg_left e6 hA₃
    linarith
  have T3 : 2 * (A₄ * Real.exp (-u) * Real.exp (α * (b * u))) ≤
      2 * A₄ * Real.exp (-(γ / 4) * u) := by
    rw [mul_assoc A₄, ← Real.exp_add]
    have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (show -u + α * (b * u) ≤ -(γ / 4) * u by linarith)) hA₄
    linarith
  have T4 : A₅ * Real.exp (Pn * u) * Real.exp (-(η - ζ) * (b * u)) ≤
      A₅ * Real.exp (-(γ / 4) * u) := by
    rw [mul_assoc A₅, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hA₅
  have hs1 : 0 ≤ (2 * A₁ + A₃ + 2 * A₄ + A₅) * Real.exp (-(γ / 4) * u) * Λ := by positivity
  have hs2 : 0 ≤ A₂ * Real.exp (-(γ / 4) * u) := by positivity
  linarith

/-- **JR (W) with the rates of JR §4.**  An influence `J = c + ∫ j` within `A₁ ε^{-β} e^{αx}` of a
quadratic whose compensated derivative `r` has the (AL) shape with `Lip ≤ A₂ √ε Λ + A₃`,
`|r - G| ≤ A₄ ε⁻¹ e^{αR}` on `(0, b log ε)` and the tail `A₅ ε^{Pn} e^{ζx}` satisfies (R) with the
rate `e^{-(γ/4) log ε} (Λ + 1)`. -/
theorem inflDecomp_of_rates {J j r : ℝ → ℝ} (hJ : AEPrimitive J j)
    {l₀ l₁ l₂ K eps b α β γ η ζ Λ A₁ A₂ A₃ A₄ A₅ : ℝ} {Pn : ℕ}
    (heps : 1 ≤ eps) (hbe : 2 ≤ b * Real.log eps) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hβ : 1 / 2 + γ ≤ β) (hα : 0 ≤ α) (hαb : α * b ≤ γ / 2) (hη : 0 ≤ η) (hζη : ζ ≤ η)
    (hbP : (Pn : ℝ) + 2 ≤ (η - ζ) * b) (hΛ : 0 ≤ Λ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hA₃ : 0 ≤ A₃) (hA₄ : 0 ≤ A₄) (hA₅ : 0 ≤ A₅) (hK : |l₂| ≤ K)
    (hr : ∀ t, j t - l₁ - 2 * l₂ * t = r t)
    (hsmall : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |J x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤ A₁ * eps ^ (-β) * Real.exp (α * x))
    (hlip : KernelApproxLip (b * Real.log eps) (A₂ * Real.sqrt eps * Λ + A₃)
      (A₄ / eps * Real.exp (α * (b * Real.log eps))) r)
    (htail : KernelTail (A₅ * eps ^ Pn) ζ r) :
    InflDecomp η ((2 * A₁ + A₂ + A₃ + 2 * A₄ + A₅) *
      (Real.exp (-(γ / 4) * Real.log eps) * (Λ + 1))) K J := by
  have heps0 : 0 < eps := by linarith
  have hu0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hfun : (fun t => j t - l₁ - 2 * l₂ * t) = r := funext hr
  subst hfun
  have hh1 : Real.exp (-(1 / 2 + γ / 4) * Real.log eps) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have hmain := inflDecomp_of_primitive hJ (h := Real.exp (-(1 / 2 + γ / 4) * Real.log eps))
    (Real.exp_pos _) (by linarith) (by positivity) (by positivity) (by positivity) hα
    (by positivity) hη hζη hK hsmall hlip htail
  refine InflDecomp.mono hmain ?_ le_rfl
  have e1 : eps ^ (-β) = Real.exp (-β * Real.log eps) := by
    rw [Real.rpow_def_of_pos heps0, mul_comm]
  have e2 : Real.sqrt eps = Real.exp (Real.log eps / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos heps0, mul_one_div]
  have e3 : A₄ / eps = A₄ * Real.exp (-Real.log eps) := by
    rw [Real.exp_neg, Real.exp_log heps0, div_eq_mul_inv]
  have e4 : eps ^ Pn = Real.exp (Pn * Real.log eps) := by
    rw [Real.exp_nat_mul, Real.exp_log heps0]
  rw [e1, e2, e3, e4]
  exact rate_ineq hu0 hγ hγ2 hβ hαb hbP hΛ hA₁ hA₂ hA₃ hA₄ hA₅

/-! ## 8. The three influences -/

/-- (ID) for the output test: `J_φ = I_φ - κ_φ J_C / C` has the derivative `H_φ + B_φ - κ_φ j`. -/
theorem aePrimitive_outJ {eps : ℝ} {ν : ProbabilityMeasure ℝ} {ψ B j : ℝ → ℝ}
    (hB : IsBdryKernel eps ν ψ B) (hj : AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j) :
    AEPrimitive (outJ eps ν ψ)
      (fun t => directKernel eps ν ψ t + B t + -outKappa eps ν ψ * j t) := by
  have e : outJ eps ν ψ = fun x =>
      outIns eps ν ψ x + -outKappa eps ν ψ * (lawJC eps ν x / lawC eps ν) := by
    funext x
    simp only [outJ]
    ring
  rw [e]
  exact AEPrimitive.add hB (hj.const_mul _)

/-- JR (R) for `J_A = J_C / C + (x - 1)² / v`. -/
theorem inflDecomp_lawJA {eps b α β γ η ζ Λ vlo KC KP C l₀ l₁ : ℝ} {PC P₀C P₁ Pn : ℕ}
    {ν : ProbabilityMeasure ℝ} {j : ℝ → ℝ}
    (heps : 1 ≤ eps) (hbe : 2 ≤ b * Real.log eps) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hβ : 1 / 2 + γ ≤ β) (hα : 0 ≤ α) (hαb : α * b ≤ γ / 2) (hη : 0 ≤ η) (hζ : 0 < ζ)
    (hζη : ζ ≤ η) (hbP : (Pn : ℝ) + 2 ≤ (η - ζ) * b) (hP₀ : P₀C ≤ Pn) (hP₁ : P₁ ≤ Pn)
    (hΛ0 : 0 ≤ Λ) (hΛ : Real.log eps ^ PC ≤ Λ) (hvlo : 0 < vlo) (hv : vlo ≤ lawVar ν)
    (hj : AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j)
    (hjL : KernelApproxLip (b * Real.log eps) (KC * Real.sqrt eps * Real.log eps ^ PC)
      (KC / eps) j)
    (hjT : KernelTail (KC * eps ^ P₀C) ζ j)
    (hl₁ : |l₁| ≤ KP * eps ^ P₁)
    (hsm : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |lawJA eps ν x - (l₀ + l₁ * x)| ≤ KP * eps ^ (-β) * Real.exp (α * x))
    (hC : 2 * |KP| + |KC| + 2 / vlo + 2 * |KC| + (|KC| + 2 / vlo + |KP| + 2 / vlo * ζ⁻¹) ≤ C) :
    InflDecomp η (C * (Real.exp (-(γ / 4) * Real.log eps) * (Λ + 1))) 0 (lawJA eps ν) := by
  have heps0 : 0 < eps := by linarith
  have hlog0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hs0 : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have hv0 : 0 < lawVar ν := lt_of_lt_of_le hvlo hv
  have hE1 : 1 ≤ eps ^ Pn := one_le_pow₀ heps
  have hαR : 1 ≤ Real.exp (α * (b * Real.log eps)) :=
    Real.one_le_exp (mul_nonneg hα (by linarith))
  have hv2 : 2 / lawVar ν ≤ 2 / vlo := div_le_div_of_nonneg_left (by norm_num) hvlo hv
  have hv2' : |2 / lawVar ν| ≤ 2 / vlo := by rw [abs_of_pos (by positivity)]; exact hv2
  have hA : AEPrimitive (lawJA eps ν)
      (fun t => j t + (-(2 / lawVar ν) + 2 * (1 / lawVar ν) * t)) := by
    have e : lawJA eps ν = fun x => lawJC eps ν x / lawC eps ν +
        (1 / lawVar ν + -(2 / lawVar ν) * x + 1 / lawVar ν * x ^ 2) := by
      funext x
      simp only [lawJA]
      ring
    rw [e]
    exact hj.add (AEPrimitive.poly _ _ _)
  have hrate : 0 ≤ Real.exp (-(γ / 4) * Real.log eps) * (Λ + 1) := by positivity
  refine InflDecomp.mono (inflDecomp_of_rates hA (l₀ := l₀) (l₁ := l₁) (l₂ := 0) (K := 0)
    (r := fun t => j t + (-(2 / lawVar ν) - l₁ + 2 / lawVar ν * t))
    (A₁ := |KP|) (A₂ := |KC|) (A₃ := 2 / vlo) (A₄ := |KC|)
    (A₅ := |KC| + 2 / vlo + |KP| + 2 / vlo * ζ⁻¹) heps hbe hγ hγ2 hβ hα hαb hη hζη hbP hΛ0
    (abs_nonneg _) (abs_nonneg _) (by positivity) (abs_nonneg _) (by positivity) abs_zero.le
    (fun t => by ring) ?_ ?_ ?_) (mul_le_mul_of_nonneg_right hC hrate) le_rfl
  · filter_upwards [hsm] with x hx
    rw [zero_mul, add_zero]
    exact hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
      (by positivity)) (Real.exp_pos _).le)
  · refine (hjL.add (KernelApproxLip.affine _ (-(2 / lawVar ν) - l₁) (2 / lawVar ν))).mono ?_ ?_
    · have := lip_weaken (K := KC) hs0 (pow_nonneg hlog0 PC) hΛ
      linarith
    · have := rho_weaken (K := KC) heps0 hαR
      linarith
  · refine (hjT.add (KernelTail.affine hζ (-(2 / lawVar ν) - l₁) (2 / lawVar ν))).mono ?_
    have t1 := tail_weaken (K := KC) heps hP₀
    have t2 : |-(2 / lawVar ν) - l₁| ≤ 2 / vlo + |KP| * eps ^ Pn := by
      have hl : |l₁| ≤ |KP| * eps ^ Pn := hl₁.trans (tail_weaken heps hP₁)
      calc |-(2 / lawVar ν) - l₁| ≤ |-(2 / lawVar ν)| + |l₁| := abs_sub _ _
        _ ≤ 2 / vlo + |KP| * eps ^ Pn := by rw [abs_neg]; linarith
    have t3 : |2 / lawVar ν| * ζ⁻¹ ≤ 2 / vlo * ζ⁻¹ :=
      mul_le_mul_of_nonneg_right hv2' (by positivity)
    have t4 : 2 / vlo ≤ 2 / vlo * eps ^ Pn := le_mul_of_one_le_right (by positivity) hE1
    have t5 : 2 / vlo * ζ⁻¹ ≤ 2 / vlo * ζ⁻¹ * eps ^ Pn :=
      le_mul_of_one_le_right (by positivity) hE1
    linarith

/-- JR (R) for the full influence `J_φ` of an output test of size `M`, given the leaf data at
`(ε, ν, ψ)` and a quadratic approximation with `|l₁| ≤ T₁ ε^{P₁}`, `|l₂| ≤ T₂`. -/
theorem inflDecomp_outJ {eps b α β γ η ζ Λ M KC Kφ KD Kk S₀ T₁ T₂ C a l₀ l₁ l₂ : ℝ}
    {PC Pφ P₀C P₀φ P₁ Pn : ℕ} {ν : ProbabilityMeasure ℝ} {ψ j B : ℝ → ℝ}
    (heps : 1 ≤ eps) (hbe : 2 ≤ b * Real.log eps) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hβ : 1 / 2 + γ ≤ β) (hα : 0 ≤ α) (hαb : α * b ≤ γ / 2) (hη : 0 ≤ η) (hζ : 0 < ζ)
    (hζη : ζ ≤ η) (hbP : (Pn : ℝ) + 2 ≤ (η - ζ) * b) (hP₀C : P₀C ≤ Pn) (hP₀φ : P₀φ ≤ Pn)
    (hP₁ : P₁ ≤ Pn) (hP2 : 2 ≤ Pn) (hΛ0 : 0 ≤ Λ) (hΛC : Real.log eps ^ PC ≤ Λ)
    (hΛφ : Real.log eps ^ Pφ ≤ Λ) (hM : 0 ≤ M) (hS₀ : 0 ≤ S₀) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hj : AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j)
    (hjL : KernelApproxLip (b * Real.log eps) (KC * Real.sqrt eps * Real.log eps ^ PC)
      (KC / eps) j)
    (hjT : KernelTail (KC * eps ^ P₀C) ζ j)
    (hB : IsBdryKernel eps ν ψ B)
    (hBL : KernelApproxLip (b * Real.log eps) (M * (Kφ * Real.sqrt eps * Real.log eps ^ Pφ))
      (M * (Kφ / eps)) B)
    (hBT : KernelTail (M * (Kφ * eps ^ P₀φ)) ζ B)
    (hH : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |directKernel eps ν ψ x - a| ≤ M * (KD / eps) * Real.exp (α * x))
    (hHT : KernelTail (M * (KD * eps ^ 2)) ζ (directKernel eps ν ψ))
    (hκ : |outKappa eps ν ψ| ≤ M * Kk)
    (hl₁ : |l₁| ≤ T₁ * eps ^ P₁) (hl₂ : |l₂| ≤ T₂)
    (hsm : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |outJ eps ν ψ x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤ S₀ * eps ^ (-β) * Real.exp (α * x))
    (hC : 2 * S₀ + M * (|Kφ| + |Kk| * |KC|) + 2 * T₂ + 2 * (M * (|KD| + |Kφ| + |Kk| * |KC|)) +
      (M * (|KD| + |Kφ| + |Kk| * |KC|) + T₁ + 2 * T₂ * ζ⁻¹) ≤ C) :
    InflDecomp η (C * (Real.exp (-(γ / 4) * Real.log eps) * (Λ + 1))) T₂ (outJ eps ν ψ) := by
  have heps0 : 0 < eps := by linarith
  have hlog0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hs0 : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have hE1 : 1 ≤ eps ^ Pn := one_le_pow₀ heps
  have hαR : 1 ≤ Real.exp (α * (b * Real.log eps)) :=
    Real.one_le_exp (mul_nonneg hα (by linarith))
  have hκ' : |-outKappa eps ν ψ| ≤ M * |Kk| := by
    rw [abs_neg]
    exact hκ.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hM)
  have hMk : 0 ≤ M * |Kk| := mul_nonneg hM (abs_nonneg _)
  -- (AL) of the three kernels
  have hHL : KernelApproxLip (b * Real.log eps) 0
      (M * |KD| / eps * Real.exp (α * (b * Real.log eps))) (directKernel eps ν ψ) := by
    refine kernelApproxLip_of_ae (a := a) (by positivity) hα ?_
    filter_upwards [hH] with x hx
    refine hx.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self _) heps0.le) hM
  have hBL' : KernelApproxLip (b * Real.log eps) (M * |Kφ| * Real.sqrt eps * Λ)
      (M * |Kφ| / eps * Real.exp (α * (b * Real.log eps))) B :=
    hBL.mono ((mul_le_mul_of_nonneg_left (lip_weaken hs0 (pow_nonneg hlog0 _) hΛφ) hM).trans_eq
        (by ring))
      ((mul_le_mul_of_nonneg_left (rho_weaken heps0 hαR) hM).trans_eq (by ring))
  have hjL' : KernelApproxLip (b * Real.log eps) (M * |Kk| * (|KC| * Real.sqrt eps * Λ))
      (M * |Kk| * (|KC| / eps * Real.exp (α * (b * Real.log eps))))
      (fun t => -outKappa eps ν ψ * j t) :=
    (hjL.mono (lip_weaken hs0 (pow_nonneg hlog0 _) hΛC) (rho_weaken heps0 hαR)).const_mul_le
      (by positivity) (by positivity) hκ'
  -- tails
  have hHT' : KernelTail (M * |KD| * eps ^ Pn) ζ (directKernel eps ν ψ) :=
    hHT.mono ((mul_le_mul_of_nonneg_left (tail_weaken heps hP2) hM).trans_eq (by ring))
  have hBT' : KernelTail (M * |Kφ| * eps ^ Pn) ζ B :=
    hBT.mono ((mul_le_mul_of_nonneg_left (tail_weaken heps hP₀φ) hM).trans_eq (by ring))
  have hjT' : KernelTail (M * |Kk| * (|KC| * eps ^ Pn)) ζ (fun t => -outKappa eps ν ψ * j t) :=
    (hjT.mono (tail_weaken heps hP₀C)).const_mul_le (by positivity) hκ'
  have hl₂' : |-2 * l₂| ≤ 2 * T₂ := by
    rw [abs_mul, abs_neg, abs_two]
    linarith
  have hrate : 0 ≤ Real.exp (-(γ / 4) * Real.log eps) * (Λ + 1) := by positivity
  refine InflDecomp.mono (inflDecomp_of_rates (aePrimitive_outJ hB hj) (l₀ := l₀) (l₁ := l₁)
    (l₂ := l₂) (K := T₂)
    (r := fun t => directKernel eps ν ψ t + B t + -outKappa eps ν ψ * j t + (-l₁ + -2 * l₂ * t))
    (A₁ := S₀) (A₂ := M * (|Kφ| + |Kk| * |KC|)) (A₃ := 2 * T₂)
    (A₄ := M * (|KD| + |Kφ| + |Kk| * |KC|))
    (A₅ := M * (|KD| + |Kφ| + |Kk| * |KC|) + T₁ + 2 * T₂ * ζ⁻¹)
    heps hbe hγ hγ2 hβ hα hαb hη hζη hbP hΛ0 hS₀ (by positivity) (by positivity) (by positivity)
    (by positivity) hl₂ (fun t => by ring) hsm ?_ ?_)
    (mul_le_mul_of_nonneg_right hC hrate) le_rfl
  · refine (((hHL.add hBL').add hjL').add (KernelApproxLip.affine _ (-l₁) (-2 * l₂))).mono ?_
      (le_of_eq (by ring))
    linarith
  · refine (((hHT'.add hBT').add hjT').add (KernelTail.affine hζ (-l₁) (-2 * l₂))).mono ?_
    have n1 : |-l₁| ≤ T₁ * eps ^ Pn := by
      rw [abs_neg]
      exact hl₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ heps hP₁) hT₁)
    have n2 : |-2 * l₂| * ζ⁻¹ ≤ 2 * T₂ * ζ⁻¹ * eps ^ Pn :=
      (mul_le_mul_of_nonneg_right hl₂' (by positivity)).trans
        (le_mul_of_one_le_right (by positivity) hE1)
    linarith

/-! ## 9. Assembly: JR (R) from the leaves -/

/-- **JR §3–4: the derivative layer.**  The leaves 4B-C, 4B-φ, 4A-D, 4A-P, 4A-Q and 4A-κ give
JR (R) for `J_A`, `J_V` and `J_φ`, uniformly on the class.  The parameters are chosen in the
order of JR §4: the weight `η ≤ ηm`, then `ζ = η/2` and the tail power `Pn`, then
`b = 2(Pn + 2)/η`, then the input weight `α ≤ γ/(2b)` with `γ = min(β - 1/2, 1/2)`; the rate is
`ε_e = C e^{-γ/4} ((log e)^{P_C} + (log e)^{P_φ} + 1)`. -/
theorem influenceDecomp_of_leaves (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm)
    (hS : PointwiseSmall) (hQ : QuadResponse) (hk : KappaBound) : InfluenceDecomp := by
  intro D θ vlo vhi hD0 hθ hvlo hvv
  obtain ⟨P₀C, hC₁⟩ := hC D θ vlo vhi hD0 hθ hvlo hvv
  obtain ⟨ηB, hηB, hP₁⟩ := hP D θ vlo vhi hD0 hθ hvlo hvv
  obtain ⟨ηD, hηD, hD₁⟩ := hD D θ vlo vhi hD0 hθ hvlo hvv
  obtain ⟨β, hβ, P₁, ηP, hηP, αP, hαP, hS₁⟩ := hS D θ vlo vhi hD0 hθ hvlo hvv
  obtain ⟨ηQ, hηQ, KQ, e0Q, hQ₁⟩ := hQ D θ vlo vhi hD0 hθ hvlo hvv
  obtain ⟨ηk, hηk, Kk, e0k, hk₁⟩ := hk D θ vlo vhi hD0 hθ hvlo hvv
  refine ⟨min (min ηB ηD) (min ηP (min ηQ ηk)),
    lt_min (lt_min hηB hηD) (lt_min hηP (lt_min hηQ hηk)), fun η hη hηm => ?_⟩
  simp only [le_min_iff] at hηm
  obtain ⟨⟨hηB', hηD'⟩, hηP', hηQ', hηk'⟩ := hηm
  obtain ⟨P₀φ, hP₂⟩ := hP₁ η hη hηB'
  obtain ⟨αD, hαD, hD₂⟩ := hD₁ η hη hηD'
  -- the tail weight `ζ`, the tail power `Pn` and the window constant `b`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = η / 2 := ⟨_, rfl⟩
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have hζη : ζ ≤ η := by rw [hζ]; linarith
  obtain ⟨Pn, hPn⟩ : ∃ Pn : ℕ, Pn = max (max P₀C P₀φ) (max 2 P₁) := ⟨_, rfl⟩
  have hP₀C : P₀C ≤ Pn := by rw [hPn]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hP₀φ : P₀φ ≤ Pn := by rw [hPn]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hP2 : 2 ≤ Pn := by rw [hPn]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hP₁n : P₁ ≤ Pn := by rw [hPn]; exact (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * ((Pn : ℝ) + 2) / η := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have hbP : (Pn : ℝ) + 2 ≤ (η - ζ) * b := by
    have e : (η - ζ) * b = (Pn : ℝ) + 2 := by
      rw [hb, hζ]
      field_simp
      ring
    exact e.ge
  obtain ⟨PC, KC, e0C, hC₂⟩ := hC₁ b ζ hb0 hζ0
  obtain ⟨Pφ, Kφ, e0φ, hP₃⟩ := hP₂ b ζ hb0 hζ0
  -- the rate exponent `γ` and the input weight `α`
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = min (β - 1 / 2) (1 / 2) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; exact lt_min (by linarith) (by norm_num)
  have hγ2 : γ ≤ 1 / 2 := by rw [hγ]; exact min_le_right _ _
  have hγβ : 1 / 2 + γ ≤ β := by
    have := min_le_left (β - 1 / 2) (1 / 2)
    rw [← hγ] at this
    linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = min (min αP αD) (γ / (2 * b)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; exact lt_min (lt_min hαP hαD) (by positivity)
  have hαP' : α ≤ αP := by rw [hα]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hαD' : α ≤ αD := by rw [hα]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hαb : α * b ≤ γ / 2 := by
    have h1 : α ≤ γ / (2 * b) := by rw [hα]; exact min_le_right _ _
    have h2 : γ / (2 * b) * b = γ / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hb0.ne']
    calc α * b ≤ γ / (2 * b) * b := mul_le_mul_of_nonneg_right h1 hb0.le
      _ = γ / 2 := h2
  obtain ⟨KP, e0P, hS₂⟩ := hS₁ α hα0 hαP'
  obtain ⟨KD, e0D, hD₃⟩ := hD₂ α ζ hα0 hαD' hζ0
  -- the constants
  obtain ⟨Kq, hKq⟩ : ∃ K : ℝ, K = |KQ| + 2 * |KP| * Real.exp (α * 3) := ⟨_, rfl⟩
  have hKq0 : 0 ≤ Kq := by rw [hKq]; positivity
  obtain ⟨CA, hCA⟩ : ∃ C : ℝ, C = 2 * |KP| + |KC| + 2 / vlo + 2 * |KC| +
      (|KC| + 2 / vlo + |KP| + 2 / vlo * ζ⁻¹) := ⟨_, rfl⟩
  obtain ⟨CV, hCV⟩ : ∃ C : ℝ, C = 2 * |KP| + (2 / η + 2) * (|Kφ| + |Kk| * |KC|) + 2 * 0 +
      2 * ((2 / η + 2) * (|KD| + |Kφ| + |Kk| * |KC|)) +
      ((2 / η + 2) * (|KD| + |Kφ| + |Kk| * |KC|) + |KP| + 2 * 0 * ζ⁻¹) := ⟨_, rfl⟩
  obtain ⟨Cφ, hCφ⟩ : ∃ C : ℝ, C = 2 * |KP| + (|Kφ| + |Kk| * |KC|) + 2 * Kq +
      2 * (|KD| + |Kφ| + |Kk| * |KC|) + ((|KD| + |Kφ| + |Kk| * |KC|) + |KP| + 2 * Kq * ζ⁻¹) :=
    ⟨_, rfl⟩
  have hCA0 : 0 ≤ CA := by rw [hCA]; positivity
  have hCV0 : 0 ≤ CV := by rw [hCV]; positivity
  have hCφ0 : 0 ≤ Cφ := by rw [hCφ]; positivity
  obtain ⟨e₁, he₁⟩ : ∃ e : ℝ, e = max (max (max e0C e0φ) (max e0D e0P))
      (max (max e0Q e0k) (max 1 (Real.exp (2 / b)))) := ⟨_, rfl⟩
  have he₁1 : 1 ≤ e₁ := by
    rw [he₁]
    exact (le_max_left 1 _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Kq, e₁, fun e => if e₁ ≤ e then (CA + CV + Cφ) *
      (Real.exp (-(γ / 4) * Real.log e) * (Real.log e ^ PC + Real.log e ^ Pφ + 1)) else 0,
    hKq0, ?_, ?_, ?_⟩
  · -- `ε_e ≥ 0`
    intro e
    dsimp only
    split_ifs with h
    · have hl : 0 ≤ Real.log e := Real.log_nonneg (he₁1.trans h)
      have := pow_nonneg hl PC
      have := pow_nonneg hl Pφ
      exact mul_nonneg (by linarith) (mul_nonneg (Real.exp_pos _).le (by linarith))
    · exact le_rfl
  · -- `ε_e → 0`
    have hlim : Tendsto (fun u : ℝ => Real.exp (-(γ / 4) * u) * (u ^ PC + u ^ Pφ + 1)) atTop
        (𝓝 0) := by
      have t1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (PC : ℝ) (γ / 4) (by positivity)
      have t2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (Pφ : ℝ) (γ / 4) (by positivity)
      have t3 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (γ / 4) (by positivity)
      have t := (t1.add t2).add t3
      rw [add_zero, add_zero] at t
      refine t.congr' (Eventually.of_forall fun u => ?_)
      simp only [Real.rpow_natCast, Real.rpow_zero]
      ring
    have hcomp := (hlim.comp Real.tendsto_log_atTop).const_mul (CA + CV + Cφ)
    rw [mul_zero] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop e₁] with e he
    simp only [Function.comp_apply, if_pos he]
  · intro eps heps ν hν
    have heps' := heps
    rw [he₁] at heps'
    simp only [max_le_iff] at heps'
    obtain ⟨⟨⟨heC, heφ⟩, heD, heP⟩, ⟨heQ, hek⟩, he1, heb⟩ := heps'
    have heps0 : 0 < eps := by linarith
    have hlog0 : 0 ≤ Real.log eps := Real.log_nonneg he1
    have hbe : 2 ≤ b * Real.log eps := by
      have h1 : 2 / b ≤ Real.log eps := (Real.le_log_iff_exp_le heps0).2 heb
      have h2 := mul_le_mul_of_nonneg_left h1 hb0.le
      rwa [mul_div_cancel₀ _ hb0.ne'] at h2
    simp only [if_pos heps]
    have hv : vlo ≤ lawVar ν := hν.var_ge
    obtain ⟨j, hj, hjL, hjT⟩ := hC₂ eps heC ν hν
    obtain ⟨hSA, hSV, hSφ⟩ := hS₂ eps heP ν hν
    have hΛ0 : 0 ≤ Real.log eps ^ PC + Real.log eps ^ Pφ :=
      add_nonneg (pow_nonneg hlog0 _) (pow_nonneg hlog0 _)
    have hΛC : Real.log eps ^ PC ≤ Real.log eps ^ PC + Real.log eps ^ Pφ :=
      le_add_of_nonneg_right (pow_nonneg hlog0 _)
    have hΛφ : Real.log eps ^ Pφ ≤ Real.log eps ^ PC + Real.log eps ^ Pφ :=
      le_add_of_nonneg_left (pow_nonneg hlog0 _)
    refine ⟨?_, ?_, ?_⟩
    · -- `J_A`
      obtain ⟨l₀, l₁, hl₁, hsm⟩ := hSA
      exact inflDecomp_lawJA he1 hbe hγ0 hγ2 hγβ hα0.le hαb hη.le hζ0 hζη hbP hP₀C hP₁n hΛ0 hΛC
        hvlo hv hj hjL hjT hl₁ hsm (by linarith)
    · -- `J_V = J_{psiVar}`
      have hMv := outTest_psiVar hη
      obtain ⟨B, hB, hBL, hBT⟩ := hP₃ eps heφ ν hν _ _ hMv
      obtain ⟨⟨a, hH⟩, hHT⟩ := hD₃ eps heD ν hν _ _ hMv
      have hκ := hk₁ eps hek ν hν _ _ (hMv.mono hηk')
      obtain ⟨l₀, l₁, hl₁, hsm⟩ := hSV
      have hsm' : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
          |outJ eps ν psiVar x - (l₀ + l₁ * x + 0 * x ^ 2)| ≤
            |KP| * eps ^ (-β) * Real.exp (α * x) := by
        filter_upwards [hsm] with x hx
        rw [zero_mul, add_zero]
        exact hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
          (by positivity)) (Real.exp_pos _).le)
      have hl₁' : |l₁| ≤ |KP| * eps ^ P₁ :=
        hl₁.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      show InflDecomp η _ _ (outJ eps ν psiVar)
      exact inflDecomp_outJ (M := 2 / η + 2) he1 hbe hγ0 hγ2 hγβ hα0.le hαb hη.le hζ0 hζη hbP
        hP₀C hP₀φ hP₁n hP2 hΛ0 hΛC hΛφ (by positivity) (abs_nonneg _) (abs_nonneg _) le_rfl
        hj hjL hjT hB hBL hBT hH hHT hκ hl₁' abs_zero.le hsm' (by linarith)
    · -- `J_φ`
      intro M ψ hψ
      have hM : 0 ≤ M := hψ.M_nonneg
      obtain ⟨B, hB, hBL, hBT⟩ := hP₃ eps heφ ν hν M ψ hψ
      obtain ⟨⟨a, hH⟩, hHT⟩ := hD₃ eps heD ν hν M ψ hψ
      have hκ := hk₁ eps hek ν hν M ψ (hψ.mono hηk')
      have hQφ := hQ₁ eps heQ ν hν M ψ (hψ.mono hηQ')
      obtain ⟨l₀, l₁, l₂, hl, hsm⟩ := hSφ M ψ (hψ.mono hηP')
      have hsm' : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
          |outJ eps ν ψ x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤
            M * |KP| * eps ^ (-β) * Real.exp (α * x) := by
        filter_upwards [hsm] with x hx
        refine hx.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hM
      -- JR (Q)
      have hq := quad_coeff_bound (aePrimitive_outJ hB hj) hα0.le hsm' hQφ (by positivity)
      have hl₂ : |l₂| ≤ M * Kq := by
        have h1 : M * KQ ≤ M * |KQ| := mul_le_mul_of_nonneg_left (le_abs_self _) hM
        have h2 : eps ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos he1 (by linarith)
        have h3 : M * |KP| * eps ^ (-β) * Real.exp (α * 3) ≤ M * |KP| * Real.exp (α * 3) :=
          mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_right (mul_nonneg hM (abs_nonneg _)) h2) (Real.exp_pos _).le
        rw [hKq]
        linarith
      have hl₁ : |l₁| ≤ M * |KP| * eps ^ P₁ := by
        have : M * (KP * eps ^ P₁) ≤ M * |KP| * eps ^ P₁ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hM
        linarith [abs_nonneg l₂]
      refine InflDecomp.mono (inflDecomp_outJ (C := M * (CA + CV + Cφ)) he1 hbe hγ0 hγ2 hγβ
        hα0.le hαb hη.le hζ0 hζη hbP hP₀C hP₀φ hP₁n hP2 hΛ0 hΛC hΛφ hM
        (mul_nonneg hM (abs_nonneg _)) (mul_nonneg hM (abs_nonneg _)) (mul_nonneg hM hKq0)
        hj hjL hjT hB hBL hBT hH hHT hκ hl₁ hl₂ hsm' ?_) (le_of_eq (by ring)) le_rfl
      linarith [mul_nonneg hM hCA0, mul_nonneg hM hCV0, congrArg (HMul.hMul M) hCφ]

end

end PGM
