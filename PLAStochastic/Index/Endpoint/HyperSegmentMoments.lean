import PLAStochastic.Index.Endpoint.LayerInduction

/-!
# Model G, endpoint hierarchy: layer-uniform exponential moments of hyper-segments

This file proves the iid (reference hierarchy) version of `lem:hyperexp`
(`proofG_one_layer_core.tex`) and of `cor:Ghyper` (`proofG_endpoint_core.tex`).  In the
reference hierarchy every layer is an iid pair sequence, so the conditioning on `𝓕₀` is
trivial and `ϱ' = 0`.

Write `N⁽ℓ⁾ = (epLayerSeq eps g ℓ 0).2` for the first hyper-segment count of layer `ℓ` and
`m_ℓ = lcount P (epLayerSeq eps g ℓ) = E N⁽ℓ⁾`.  With the absolute constants
`aK = 1 / (144 · 5185)`, `θK = aK / 512`, `CK = 73` and `GK = 10¹⁴`, and for `eps` with
`epsZero b β ≤ eps` and `GK b ≤ eps²` (both implied by `epsK b β ≤ eps`), every layer satisfies

`E exp(θK N⁽ℓ⁾ / m_ℓ) ≤ CK`,  `P(N⁽ℓ⁾ > λ m_ℓ) ≤ CK exp(-θK λ)`,  `E (N⁽ℓ⁾ / m_ℓ)² ≤ 2 CK / θK²`

(`hyperexp_all`, `hyperexp_tail_all`, `hyperexp_sq_all`; `hyperexp_input` for an input
gap law).  The one-step argument (`hyperexp_step`, for an abstract iid pair sequence, and
`hyperexp_layer_step` under `LayerOK`) follows the proof of `lem:hyperexp`, with
`θ = aK / (2G)`, `Λ = θ + KZ θ²`, `G = μ² eps² / σ²`:

* (a) `E exp(θ n / m) ≤ exp(θ + KZ θ²)` for `0 ≤ θ ≤ θK / 2`, `KZ = 8 CK / θK²`
  (`integral_exp_mul_le`), from `exp y ≤ 1 + y + y² exp y` and `x² ≤ 8 θK⁻² exp(θK x / 2)`;
* (b) `E exp(∑_{t<T} (θ n_t / m - Λ)) ≤ 1`, by induction along the truncated stopping
  times, independence of pair `t` from `{t < T}`, and Fatou (`lintegral_exp_stopped_le_one`);
* (c) `E exp(s T) ≤ 145` whenever `s L ≤ 1/144` for the block length `L ≤ 5185 G` of the
  geometric tail `P(T > jL) ≤ (71/72)^j` (`lintegral_exp_toNat_le_145`);
* (d) the arithmetic–geometric mean inequality in place of Cauchy–Schwarz,
  `exp(θ N / (2m)) ≤ (exp(θ N / m - T Λ) + exp(T Λ)) / 2`, so `E exp(θ N / (2m)) ≤ 73`;
* (e) rescaling by `m⁺ = m C` with `C = E T ≥ G / 128`: `θK / (m C) ≤ θ / (2m)`, and since
  `N ≥ 0`, monotonicity of `exp` replaces Jensen.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## Constants -/

/-- The segment-length exponential scale `1 / (144 · 5185)`. -/
def aK : ℝ := 1 / 746640

/-- The layer-uniform exponential rate. -/
def θK : ℝ := aK / 512

/-- The layer-uniform exponential-moment bound. -/
def CK : ℝ := 73

/-- The cumulant constant `8 CK / θK²`. -/
def KZ : ℝ := 8 * CK / θK ^ 2

/-- Threshold for `G = μ² eps² / σ²`. -/
def GK : ℝ := 10 ^ 14

theorem aK_pos : 0 < aK := by unfold aK; norm_num

theorem θK_pos : 0 < θK := by unfold θK aK; norm_num

theorem θK_le_one : θK ≤ 1 := by unfold θK aK; norm_num

theorem CK_pos : 0 < CK := by unfold CK; norm_num

theorem KZ_pos : 0 < KZ := by unfold KZ; have := θK_pos; unfold CK; positivity

theorem KZ_mul_aK_le : KZ * aK ≤ 2 * GK := by
  unfold KZ GK CK θK aK; norm_num

theorem le_GK : 512 ≤ GK := by unfold GK; norm_num

theorem one_le_GK : 1 ≤ GK := by unfold GK; norm_num

theorem exp_θK_le_CK : Real.exp θK ≤ CK := by
  have h1 : θK < 1 := by unfold θK aK; norm_num
  have h := Real.exp_bound_div_one_sub_of_interval θK_pos.le h1
  have h2 : 1 / (1 - θK) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : θK ≤ 1 / 2 := by unfold θK aK; norm_num
    linarith
  unfold CK
  linarith

/-! ## Elementary inequalities -/

/-- `exp y ≤ 1 + y + y² exp y` for `y ≥ 0`. -/
theorem exp_le_one_add_add_sq_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    Real.exp y ≤ 1 + y + y ^ 2 * Real.exp y := by
  have h1 : Real.exp y - 1 ≤ y * Real.exp y := by
    have h := Real.add_one_le_exp (-y)
    have he := Real.exp_pos y
    have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h2 : y * (Real.exp y - 1) ≤ y * (y * Real.exp y) := mul_le_mul_of_nonneg_left h1 hy
  nlinarith

/-- `x² ≤ (8/a²) exp(a x / 2)` for `x ≥ 0`, `a > 0`. -/
theorem sq_le_mul_exp_half {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ 2 ≤ 8 / a ^ 2 * Real.exp (a * x / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := a * x / 2) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a * x), mul_nonneg ha.le hx]

/-- The key pointwise bound behind the cumulant estimate: for `x ≥ 0`, `0 ≤ θ ≤ a/2`,
`exp(θ x) ≤ 1 + θ x + θ² (8/a²) exp(a x)`. -/
theorem exp_mul_le_quadratic {a θ x : ℝ} (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ : θ ≤ a / 2)
    (hx : 0 ≤ x) :
    Real.exp (θ * x) ≤ 1 + θ * x + θ ^ 2 * (8 / a ^ 2 * Real.exp (a * x)) := by
  have h1 := exp_le_one_add_add_sq_mul_exp (mul_nonneg hθ0 hx)
  have h2 : Real.exp (θ * x) ≤ Real.exp (a * x / 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h3 := sq_le_mul_exp_half ha hx
  have h4 : x ^ 2 * Real.exp (θ * x) ≤ 8 / a ^ 2 * Real.exp (a * x) := by
    have e : Real.exp (a * x) = Real.exp (a * x / 2) * Real.exp (a * x / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h5 : x ^ 2 * Real.exp (θ * x) ≤ x ^ 2 * Real.exp (a * x / 2) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg x)
    have h6 : x ^ 2 * Real.exp (a * x / 2) ≤ 8 / a ^ 2 * Real.exp (a * x / 2) *
        Real.exp (a * x / 2) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    linarith
  have h7 : (θ * x) ^ 2 * Real.exp (θ * x) = θ ^ 2 * (x ^ 2 * Real.exp (θ * x)) := by ring
  rw [h7] at h1
  have h8 := mul_le_mul_of_nonneg_left h4 (sq_nonneg θ)
  linarith

/-! ## (c) Exponential moment of a segment length with a geometric block tail -/

/-- Pointwise: `exp(s n) ≤ 1 + ∑_j 1{jL < n} exp(s L (j+1))`. -/
theorem ofReal_exp_toNat_le_tsum (n : ℕ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (Real.exp (s * n.toNat)) ≤ 1 + ∑' j : ℕ,
      if ((j * L : ℕ) : ℕ∞) < n then ENNReal.ofReal (Real.exp (s * L * (j + 1))) else 0 := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    set j := (n - 1) / L with hj
    have hj1 : j * L < n := by
      have := Nat.div_mul_le_self (n - 1) L
      rw [← hj] at this
      omega
    have hj2 : n ≤ (j + 1) * L := by
      have := Nat.lt_div_mul_add (a := n - 1) (b := L) (by omega)
      rw [← hj] at this
      rw [add_mul, one_mul]
      omega
    have hj2' : (n : ℝ) ≤ L * (j + 1) := by
      have : ((n : ℕ) : ℝ) ≤ ((j + 1) * L : ℕ) := by exact_mod_cast hj2
      push_cast at this
      linarith
    calc ENNReal.ofReal (Real.exp (s * ((n : ℕ∞).toNat : ℕ)))
        ≤ ENNReal.ofReal (Real.exp (s * L * (j + 1))) := by
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          simp only [ENat.toNat_natCast]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hj2' hs
      _ = (if ((j * L : ℕ) : ℕ∞) < (n : ℕ∞) then
            ENNReal.ofReal (Real.exp (s * L * (j + 1))) else 0) := by
          rw [if_pos (by exact_mod_cast hj1)]
      _ ≤ ∑' j : ℕ, if ((j * L : ℕ) : ℕ∞) < (n : ℕ∞) then
            ENNReal.ofReal (Real.exp (s * L * (j + 1))) else 0 :=
          ENNReal.le_tsum (f := fun j : ℕ => if ((j * L : ℕ) : ℕ∞) < (n : ℕ∞) then
            ENNReal.ofReal (Real.exp (s * L * (j + 1))) else 0) j
      _ ≤ _ := le_add_self

/-- **Exponential moment engine.** Under the geometric block tail `P(jL < T) ≤ r^j`,
`E exp(s T) ≤ 1 + x / (1 - r x)` with `x = exp(s L)`, whenever `r x < 1`. -/
theorem lintegral_exp_toNat_le_of_tail [IsProbabilityMeasure P] {T : Ω → ℕ∞}
    (hT : Measurable T) {L : ℕ} (hL : 1 ≤ L) {r s : ℝ} (hr0 : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r * Real.exp (s * L) < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (T ω).toNat)) ∂P ≤
      ENNReal.ofReal (1 + Real.exp (s * L) / (1 - r * Real.exp (s * L))) := by
  set x := Real.exp (s * L) with hx
  have hx0 : 0 < x := Real.exp_pos _
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (s * L * (j + 1))) with hc
  have hs' : ∀ j : ℕ, MeasurableSet {ω | ((j * L : ℕ) : ℕ∞) < T ω} := fun j =>
    tail_measurableSet_lt hT _
  -- the geometric series
  have hq0 : 0 ≤ r * x := by positivity
  have hgeom := (hasSum_geometric_of_lt_one hq0 hrs).mul_left x
  have hterm : ∀ j : ℕ, Real.exp (s * L * (j + 1)) * r ^ j = x * (r * x) ^ j := by
    intro j
    have e : s * L * (j + 1) = (j : ℝ) * (s * L) + s * L := by ring
    rw [e, Real.exp_add, Real.exp_nat_mul, mul_pow]
    ring
  have hsum : ∑' j : ℕ, c j * ENNReal.ofReal (r ^ j) = ENNReal.ofReal (x * (1 - r * x)⁻¹) := by
    rw [← hgeom.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeom.summable]
    refine tsum_congr fun j => ?_
    rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hterm]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (T ω).toNat)) ∂P
      ≤ ∫⁻ ω, (1 + ∑' j : ℕ,
          Set.indicator {ω | ((j * L : ℕ) : ℕ∞) < T ω} (fun _ => c j) ω) ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa only [Set.indicator_apply, Set.mem_ofPred_eq, hc] using
          ofReal_exp_toNat_le_tsum (T ω) hL hs
    _ = 1 + ∑' j : ℕ, c j * P {ω | ((j * L : ℕ) : ℕ∞) < T ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
          lintegral_tsum fun j => (measurable_const.indicator (hs' j)).aemeasurable]
        simp_rw [lintegral_indicator_const (hs' _)]
    _ ≤ 1 + ∑' j : ℕ, c j * ENNReal.ofReal (r ^ j) := by
        gcongr with j
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (htail j)
    _ = ENNReal.ofReal (1 + x / (1 - r * x)) := by
        rw [hsum, ENNReal.ofReal_add zero_le_one (by
          have : 0 < 1 - r * x := by linarith
          positivity), ENNReal.ofReal_one, div_eq_mul_inv]

/-- **Exponential moment of `T`** at the block scale: if `s L ≤ 1/144` and
`P(jL < T) ≤ (71/72)^j`, then `E exp(s T) ≤ 145`. -/
theorem lintegral_exp_toNat_le_145 [IsProbabilityMeasure P] {T : Ω → ℕ∞}
    (hT : Measurable T) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 ≤ s) (hsL : s * L ≤ 1 / 144)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ (71 / 72 : ℝ) ^ j) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * (T ω).toNat)) ∂P ≤ ENNReal.ofReal 145 := by
  have hx : Real.exp (s * L) ≤ 144 / 143 := by
    calc Real.exp (s * L) ≤ Real.exp (1 / 144) := Real.exp_le_exp.2 hsL
      _ ≤ 1 / (1 - 1 / 144) :=
          Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 144 / 143 := by norm_num
  have hx1 : 1 ≤ Real.exp (s * L) := Real.one_le_exp (by positivity)
  have hrs : (71 / 72 : ℝ) * Real.exp (s * L) < 1 := by linarith
  refine (lintegral_exp_toNat_le_of_tail hT hL (by norm_num) hs hrs htail).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h : Real.exp (s * L) / (1 - 71 / 72 * Real.exp (s * L)) ≤ 144 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-! ## (a) The cumulant bound -/

/-- **Cumulant bound** (`eq:LambdaZ`, iid case).  If `X ≥ 0`, `E X ≤ 1` and
`E exp(θK X) ≤ CK`, then for `0 ≤ θ ≤ θK / 2`, `E exp(θ X) ≤ exp(θ + KZ θ²)`. -/
theorem integral_exp_mul_le [IsProbabilityMeasure P] {X : Ω → ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    (hX1 : Integrable X P) (hXmean : ∫ ω, X ω ∂P ≤ 1)
    (hXe : Integrable (fun ω => Real.exp (θK * X ω)) P)
    (hXeC : ∫ ω, Real.exp (θK * X ω) ∂P ≤ CK) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ θK / 2) :
    Integrable (fun ω => Real.exp (θ * X ω)) P ∧
      ∫ ω, Real.exp (θ * X ω) ∂P ≤ Real.exp (θ + KZ * θ ^ 2) := by
  have hθK := θK_pos
  have hint : Integrable (fun ω => Real.exp (θ * X ω)) P := by
    refine hXe.mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact (Real.measurable_exp.comp_aemeasurable
        (hX1.aemeasurable.const_mul θ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (hX0 ω))
  refine ⟨hint, ?_⟩
  have hbd : Integrable (fun ω => 1 + θ * X ω + θ ^ 2 * (8 / θK ^ 2 *
      Real.exp (θK * X ω))) P :=
    ((integrable_const 1).add (hX1.const_mul θ)).add ((hXe.const_mul _).const_mul _)
  calc ∫ ω, Real.exp (θ * X ω) ∂P
      ≤ ∫ ω, (1 + θ * X ω + θ ^ 2 * (8 / θK ^ 2 * Real.exp (θK * X ω))) ∂P :=
        integral_mono hint hbd fun ω => exp_mul_le_quadratic hθK hθ0 hθ (hX0 ω)
    _ = 1 + θ * ∫ ω, X ω ∂P + θ ^ 2 * (8 / θK ^ 2 * ∫ ω, Real.exp (θK * X ω) ∂P) := by
        rw [integral_add (f := fun ω => 1 + θ * X ω)
          (g := fun ω => θ ^ 2 * (8 / θK ^ 2 * Real.exp (θK * X ω)))
          ((integrable_const 1).add (hX1.const_mul θ)) ((hXe.const_mul _).const_mul _),
          integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => θ * X ω) (integrable_const 1)
          (hX1.const_mul θ), integral_const_mul, integral_const_mul, integral_const_mul]
        simp
    _ ≤ 1 + θ * 1 + θ ^ 2 * (8 / θK ^ 2 * CK) := by
        gcongr
    _ = 1 + (θ + KZ * θ ^ 2) := by unfold KZ; ring
    _ ≤ Real.exp (θ + KZ * θ ^ 2) := by linarith [Real.add_one_le_exp (θ + KZ * θ ^ 2)]

/-! ## (b) The stopped exponential supermartingale -/

/-- **Exponential Wald inequality** (step (b) of `lem:hyperexp`, iid case).  For an iid pair
sequence, a measurable `f` with `E exp(f(Z 0) - Λ) ≤ 1`, and the first segment length `T`
(almost surely finite), `E exp(∑_{t<T} (f(Z t) - Λ)) ≤ 1`. -/
theorem lintegral_exp_stopped_le_one [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ}
    (hZ : IIDPairs P Z) (eps : ℝ) {f : ℝ × ℕ → ℝ} (hf : Measurable f) (Λ : ℝ)
    (hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (f (Z 0 ω) - Λ)) ∂P ≤ 1)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ)
      (fun ω => pairSegLen eps (seq Z ω)) ω)) ∂P ≤ 1 := by
  set F := pairFiltration Z hZ.measurable with hF
  set Y : ℕ → Ω → ℝ := fun t ω => f (Z t ω) - Λ with hYdef
  set T : Ω → ℕ∞ := fun ω => pairSegLen eps (seq Z ω) with hTdef
  have hY : IndepIncrements P F Y := hZ.indepIncrements f hf Λ
  have hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω} :=
    pairSegLen_lt_measurable hZ.measurable eps
  have hW := stopWeight_predictable hT
  have hφ : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp x) :=
    ENNReal.measurable_ofReal.comp Real.measurable_exp
  have hexpt : ∀ t, ∫⁻ ω, ENNReal.ofReal (Real.exp (Y t ω)) ∂P ≤ 1 := by
    intro t
    have hu : Measurable fun p : ℝ × ℕ => ENNReal.ofReal (Real.exp (f p - Λ)) :=
      hφ.comp (hf.sub_const Λ)
    have := ((hZ.ident t).comp hu).lintegral_eq
    simp only [Function.comp_def] at this
    simp only [hYdef]
    rw [this]
    exact hexp
  -- one step of the truncated supermartingale
  have hstep : ∀ j : ℕ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (weightedSum (stopWeight T) Y (j + 1) ω)) ∂P ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (weightedSum (stopWeight T) Y j ω)) ∂P := by
    intro j
    set A := {ω | (j : ℕ∞) < T ω} with hAdef
    have hA : MeasurableSet A := F.le j _ (hT j)
    set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (weightedSum (stopWeight T) Y j ω))
      with hgdef
    have hg : Measurable[F j] g := hφ.comp (weightedSum_measurable_past hY hW j)
    have hgA : Measurable[F j] (A.indicator g) := hg.indicator (hT j)
    set e : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (Y j ω)) with hedef
    have he : Measurable[MeasurableSpace.comap (Y j) inferInstance] e :=
      hφ.comp (comap_measurable (Y j))
    have hpt : ∀ ω, ENNReal.ofReal (Real.exp (weightedSum (stopWeight T) Y (j + 1) ω)) =
        A.indicator g ω * e ω + Aᶜ.indicator g ω := by
      intro ω
      rw [weightedSum_succ]
      by_cases hω : ω ∈ A
      · have hw : stopWeight T j ω = 1 := by
          simp only [stopWeight]; exact if_pos hω
        rw [hw, one_mul, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω),
          add_zero]
      · have hw : stopWeight T j ω = 0 := by
          simp only [stopWeight]; exact if_neg hω
        rw [hw, zero_mul, add_zero, Set.indicator_of_notMem hω, zero_mul, zero_add,
          Set.indicator_of_mem (Set.mem_compl hω)]
    have hmA : Measurable (A.indicator g) := hgA.mono (F.le j) le_rfl
    have hme : Measurable e := he.mono (MeasurableSpace.comap_le_iff_le_map.2
      (hY.measurable' j)) le_rfl
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (weightedSum (stopWeight T) Y (j + 1) ω)) ∂P
        = ∫⁻ ω, (A.indicator g ω * e ω + Aᶜ.indicator g ω) ∂P := lintegral_congr hpt
      _ = ∫⁻ ω, A.indicator g ω * e ω ∂P + ∫⁻ ω, Aᶜ.indicator g ω ∂P :=
          lintegral_add_left (hmA.mul hme) _
      _ = (∫⁻ ω, A.indicator g ω ∂P) * (∫⁻ ω, e ω ∂P) + ∫⁻ ω, Aᶜ.indicator g ω ∂P := by
          rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
            (F.le j) (MeasurableSpace.comap_le_iff_le_map.2 (hY.measurable' j))
            (hY.indep j).symm hgA he]
      _ ≤ (∫⁻ ω, A.indicator g ω ∂P) * 1 + ∫⁻ ω, Aᶜ.indicator g ω ∂P := by
          gcongr
          exact hexpt j
      _ = ∫⁻ ω, g ω ∂P := by
          rw [mul_one, lintegral_indicator hA, lintegral_indicator hA.compl,
            lintegral_add_compl g hA]
  have hall : ∀ j : ℕ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (weightedSum (stopWeight T) Y j ω)) ∂P ≤ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => exact (hstep j).trans ih
  refine (lintegral_stopped_le_liminf (φ := Real.exp) hfin
    (fun n => hφ.comp (weightedSum_measurable hY hW n))).trans ?_
  exact Filter.liminf_le_of_frequently_le' (Frequently.of_forall hall)

/-! ## One step of the hyper-segment bound -/

/-- `exp((u + v)/2) ≤ (exp u + exp v)/2`. -/
theorem exp_half_add_le (u v : ℝ) :
    Real.exp ((u + v) / 2) ≤ (Real.exp u + Real.exp v) / 2 := by
  have ha : Real.exp u = Real.exp (u / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hb : Real.exp v = Real.exp (v / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hab : Real.exp ((u + v) / 2) = Real.exp (u / 2) * Real.exp (v / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [ha, hb, hab]
  nlinarith [sq_nonneg (Real.exp (u / 2) - Real.exp (v / 2))]

/-- **One step of `lem:hyperexp`** (iid case).  Let `Z` be an iid pair sequence whose counts
`n_t = (Z t).2` satisfy `E n ≤ m` and `E exp(θK n / m) ≤ CK`, let `T` be the first segment
length, with block tail `P(jL < T) ≤ (71/72)^j` for a block length `L ≤ 5185 G`, where
`G ≥ GK`.  Then the stopped count `N = ∑_{t<T} n_t` of the first block satisfies
`E exp(θK N / (m C)) ≤ CK` for every `C ≥ G / 128`. -/
theorem hyperexp_step [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ} (hZ : IIDPairs P Z)
    {eps G m C : ℝ} {L : ℕ} (hm : 0 < m) (hmean : ∫ ω, ((Z 0 ω).2 : ℝ) ∂P ≤ m)
    (hZe : Integrable (fun ω => Real.exp (θK * ((Z 0 ω).2 : ℝ) / m)) P)
    (hZeC : ∫ ω, Real.exp (θK * ((Z 0 ω).2 : ℝ) / m) ∂P ≤ CK)
    (hL1 : 1 ≤ L) (hLG : (L : ℝ) ≤ 5185 * G)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < pairSegLen eps (seq Z ω)} ≤
      (71 / 72 : ℝ) ^ j)
    (hG : GK ≤ G) (hC : G / 128 ≤ C) :
    Integrable (fun ω => Real.exp (θK * ((firstBlock eps (seq Z ω)).2 : ℝ) / (m * C))) P ∧
      ∫ ω, Real.exp (θK * ((firstBlock eps (seq Z ω)).2 : ℝ) / (m * C)) ∂P ≤ CK := by
  have hθK := θK_pos
  have haK := aK_pos
  have hG512 : 512 ≤ G := le_trans le_GK hG
  have hGpos : 0 < G := by linarith
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC
  set T : Ω → ℕ∞ := fun ω => pairSegLen eps (seq Z ω) with hTdef
  have hTm : Measurable T := (measurable_pairSegLen eps).comp (measurable_seq hZ.measurable)
  have hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤ := by
    filter_upwards [ae_lt_top_of_tail hTm hL1 (by norm_num) (by norm_num) htail] with ω h
    exact h.ne
  -- the normalised counts
  set X : Ω → ℝ := fun ω => ((Z 0 ω).2 : ℝ) / m with hXdef
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => by positivity
  have hXm : Measurable X := (measurable_natCast_snd.comp (hZ.measurable 0)).div_const m
  have hXe : Integrable (fun ω => Real.exp (θK * X ω)) P := by
    refine hZe.congr (Eventually.of_forall fun ω => ?_)
    simp only [hXdef, mul_div_assoc]
  have hXeC : ∫ ω, Real.exp (θK * X ω) ∂P ≤ CK := by
    refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun ω => ?_))) hZeC
    simp only [hXdef, mul_div_assoc]
  have hX1 : Integrable X P := by
    refine (hXe.div_const θK).mono' hXm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω), le_div_iff₀ hθK]
    linarith [Real.add_one_le_exp (θK * X ω), mul_comm (X ω) θK]
  have hXmean : ∫ ω, X ω ∂P ≤ 1 := by
    simp only [hXdef]
    rw [integral_div, div_le_one hm]
    exact hmean
  -- the parameters
  set θ : ℝ := aK / (2 * G) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθK2 : θ ≤ θK / 2 := by
    rw [hθdef, θK, div_le_iff₀ (by positivity)]
    have : aK * 1024 ≤ aK * (2 * G) := by nlinarith
    nlinarith
  set Λ : ℝ := θ + KZ * θ ^ 2 with hΛdef
  have hKZθ : KZ * θ ≤ 1 := by
    rw [hθdef, mul_div_assoc', div_le_one (by positivity)]
    linarith [KZ_mul_aK_le]
  have hΛ0 : 0 ≤ Λ := by have := KZ_pos; positivity
  have hΛ2 : Λ ≤ 2 * θ := by
    have : KZ * θ ^ 2 ≤ θ := by nlinarith
    linarith
  have hΛL : Λ * L ≤ 1 / 144 := by
    have h1 : Λ * L ≤ 2 * θ * (5185 * G) := by
      have := mul_le_mul hΛ2 hLG (Nat.cast_nonneg L) (by positivity)
      linarith
    have h2 : 2 * θ * (5185 * G) = 5185 * aK := by
      rw [hθdef]; field_simp
    rw [h2] at h1
    unfold aK at h1
    linarith
  -- (a) the cumulant bound
  obtain ⟨hθint, hθle⟩ := integral_exp_mul_le hX0 hX1 hXmean hXe hXeC hθ0 hθK2
  -- (b) the stopped supermartingale
  set f : ℝ × ℕ → ℝ := fun p => θ * ((p.2 : ℝ) / m) with hfdef
  have hf : Measurable f := measurable_natCast_snd.div_const m |>.const_mul θ
  have hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (f (Z 0 ω) - Λ)) ∂P ≤ 1 := by
    have hint : Integrable (fun ω => Real.exp (f (Z 0 ω) - Λ)) P := by
      refine (hθint.mul_const (Real.exp (-Λ))).congr (Eventually.of_forall fun ω => ?_)
      simp only [hfdef, hXdef, sub_eq_add_neg, Real.exp_add]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ ω, Real.exp (f (Z 0 ω) - Λ) ∂P = (∫ ω, Real.exp (θ * X ω) ∂P) *
        Real.exp (-Λ) := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hfdef, hXdef, sub_eq_add_neg, Real.exp_add]
    rw [e]
    calc (∫ ω, Real.exp (θ * X ω) ∂P) * Real.exp (-Λ) ≤ Real.exp Λ * Real.exp (-Λ) :=
          mul_le_mul_of_nonneg_right hθle (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hM := lintegral_exp_stopped_le_one hZ eps hf Λ hexp hfin
  -- (c) the exponential moment of `T`
  have hTexp := lintegral_exp_toNat_le_145 (P := P) hTm hL1 hΛ0 hΛL htail
  -- (d) the arithmetic-geometric mean inequality, pathwise
  set N : Ω → ℝ := fun ω => ((firstBlock eps (seq Z ω)).2 : ℝ) with hNdef
  have hNm : Measurable N :=
    measurable_natCast_snd.comp ((measurable_firstBlock eps).comp (measurable_seq hZ.measurable))
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => Nat.cast_nonneg _
  have hid : ∀ ω, stoppedSumE (fun t ω => f (Z t ω) - Λ) T ω =
      θ * N ω / m - Λ * ((T ω).toNat : ℝ) := by
    intro ω
    simp only [stoppedSumE, partialSum, hNdef, firstBlock, Prod.snd_sum, seq, Nat.cast_sum,
      sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hfdef, ← sum_div, ← mul_sum, hTdef]
    ring
  have hθC : 2 * θK ≤ θ * C := by
    have h1 : θ * (G / 128) ≤ θ * C := mul_le_mul_of_nonneg_left hC hθ0
    have h2 : θ * (G / 128) = 2 * θK := by
      rw [hθdef, θK]; field_simp; ring
    linarith
  have hpt : ∀ ω, Real.exp (θK * N ω / (m * C)) ≤
      (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ) T ω) +
        Real.exp (Λ * ((T ω).toNat : ℝ))) / 2 := by
    intro ω
    refine le_trans ?_ (exp_half_add_le _ _)
    rw [hid]
    refine Real.exp_le_exp.2 ?_
    have hsum : (θ * N ω / m - Λ * ((T ω).toNat : ℝ) + Λ * ((T ω).toNat : ℝ)) / 2 =
        θ * N ω / (2 * m) := by field_simp; ring
    rw [hsum, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hθC (mul_nonneg (hN0 ω) hm.le)
    nlinarith
  -- (e) integrate
  set u : Ω → ℝ := fun ω => Real.exp (θK * N ω / (m * C)) with hudef
  have hum : Measurable u := (hNm.const_mul θK |>.div_const (m * C)).exp
  have hTn : Measurable fun ω => ((T ω).toNat : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp hTm
  have hlint : ∫⁻ ω, ENNReal.ofReal (u ω) ∂P ≤ ENNReal.ofReal 73 := by
    calc ∫⁻ ω, ENNReal.ofReal (u ω) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal
            (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ) T ω)) +
            ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.exp (Λ * ((T ω).toNat : ℝ)))) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hpt ω
          simp only [hudef]
          linarith
      _ = ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal
            (Real.exp (stoppedSumE (fun t ω => f (Z t ω) - Λ) T ω)) ∂P +
          ENNReal.ofReal (1 / 2) * ∫⁻ ω, ENNReal.ofReal
            (Real.exp (Λ * ((T ω).toNat : ℝ))) ∂P := by
          rw [lintegral_add_right _ (((hTn.const_mul Λ).exp.ennreal_ofReal).const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / 2) * 1 + ENNReal.ofReal (1 / 2) * ENNReal.ofReal 145 := by
          gcongr
      _ = ENNReal.ofReal 73 := by
          rw [mul_one, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have hu0 : 0 ≤ᵐ[P] u := Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hint : Integrable u P :=
    ⟨hum.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hu0).2
      (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hu0 hum.aestronglyMeasurable]
  unfold CK
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hlint

/-! ## Along the endpoint hierarchy -/

/-- **One layer step** under the layer invariant: the normalised exponential moment
`E exp(θK N / m) ≤ CK` passes from a layer to the next one. -/
theorem hyperexp_layer_step [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ}
    {b β vmin Kc eps : ℝ} (hL : LayerOK P Z b β vmin Kc) (hb : bAbs ≤ b) (hβ : βAbs ≤ β)
    (hvmin0 : 0 < vmin) (hvmin : vmin ≤ deltaVar / 2) (hKc : KcAbs ≤ Kc)
    (heps : epsZero b β ≤ eps) (hepsK : GK * b ≤ eps ^ 2)
    (hZe : Integrable (fun ω => Real.exp (θK * ((Z 0 ω).2 : ℝ) / lcount P Z)) P)
    (hZeC : ∫ ω, Real.exp (θK * ((Z 0 ω).2 : ℝ) / lcount P Z) ∂P ≤ CK) :
    Integrable (fun ω => Real.exp (θK * ((nextLayer eps Z 0 ω).2 : ℝ) /
        lcount P (nextLayer eps Z))) P ∧
      ∫ ω, Real.exp (θK * ((nextLayer eps Z 0 ω).2 : ℝ) / lcount P (nextLayer eps Z)) ∂P
        ≤ CK := by
  obtain ⟨-, -, hcnt, -, -⟩ := layerOK_step hL hb hβ hvmin0 hvmin hKc heps
  set μ := lmean P Z with hμdef
  set σ := lsig P Z with hσdef
  set κ := lkap P Z with hκdef
  have hX := hL.law
  have hμ : 0 < μ := hX.mu_pos
  have hσ : 0 < σ := hX.sigma_pos
  have hκ : 0 ≤ κ := hX.kappa_nonneg
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero b β) heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions hμ hσ hκ hL.var_le hL.third_le heps
  set G := μ ^ 2 * eps ^ 2 / σ ^ 2 with hGdef
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX hepspos hGdef c1 c2 c3 c4
  have hCm := integral_layerSegLen_ge_of_large hX hepspos hGdef c1 c2 c3 c4
  -- `G ≥ GK`
  have hbpos : 0 < b := lt_of_lt_of_le bAbs_pos hb
  have hGb : eps ^ 2 / b ≤ G := by
    rw [hGdef, div_le_div_iff₀ hbpos (by positivity)]
    calc eps ^ 2 * σ ^ 2 ≤ eps ^ 2 * (b * μ ^ 2) :=
          mul_le_mul_of_nonneg_left hL.var_le (sq_nonneg eps)
      _ = μ ^ 2 * eps ^ 2 * b := by ring
  have hGK : GK ≤ G := by
    refine le_trans ?_ hGb
    rw [le_div_iff₀ hbpos]
    exact hepsK
  have hC : G / 128 ≤ segMean P eps Z := by
    have : cMinus * G = G / 128 := by unfold cMinus; ring
    rw [← this]
    exact hCm
  have h := hyperexp_step hL.iid hL.cnt_pos le_rfl hZe hZeC hL1 hLG htail hGK hC
  rw [hcnt]
  exact h

/-- **Layer-uniform exponential moments of the hyper-segment counts** (`cor:Ghyper`,
reference hierarchy).  Under the hypotheses of `layerOK_all`, and for `eps` with
`GK b ≤ eps²`, every layer `ℓ` satisfies `E exp(θK N⁽ℓ⁾ / m_ℓ) ≤ CK`, where
`N⁽ℓ⁾ = (epLayerSeq eps g ℓ 0).2` and `m_ℓ = lcount P (epLayerSeq eps g ℓ)`. -/
theorem hyperexp_all [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {b β vmin Kc eps : ℝ}
    (h0 : LayerOK P (inputPairs g) b β vmin Kc) (hb : bAbs ≤ b) (hβ : βAbs ≤ β)
    (hvmin0 : 0 < vmin) (hvmin : vmin ≤ deltaVar / 2) (hKc : KcAbs ≤ Kc)
    (heps : epsZero b β ≤ eps) (hepsK : GK * b ≤ eps ^ 2) :
    ∀ ℓ, Integrable (fun ω => Real.exp (θK * ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) /
        lcount P (epLayerSeq eps g ℓ))) P ∧
      ∫ ω, Real.exp (θK * ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) / lcount P (epLayerSeq eps g ℓ)) ∂P
        ≤ CK := by
  have hall := layerOK_all h0 hb hβ hvmin0 hvmin hKc heps
  intro ℓ
  induction ℓ with
  | zero =>
    have e1 : lcount P (epLayerSeq eps g 0) = 1 := by
      simp [lcount, epLayerSeq, inputPairs]
    have e2 : ∀ ω, ((epLayerSeq eps g 0 0 ω).2 : ℝ) = 1 := fun ω => by
      simp [epLayerSeq, inputPairs]
    simp only [e1, e2, mul_one, div_one, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact ⟨integrable_const _, exp_θK_le_CK⟩
  | succ ℓ ih =>
    have e : epLayerSeq eps g (ℓ + 1) = nextLayer eps (epLayerSeq eps g ℓ) := by
      simp only [epLayerSeq, Function.iterate_succ_apply']
    rw [e]
    exact hyperexp_layer_step (hall ℓ).1 hb hβ hvmin0 hvmin hKc heps hepsK ih.1 ih.2

/-- **Exponential tail of the hyper-segment counts**: `P(N⁽ℓ⁾ > λ m_ℓ) ≤ CK exp(-θK λ)`. -/
theorem hyperexp_tail_all [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {b β vmin Kc eps : ℝ}
    (h0 : LayerOK P (inputPairs g) b β vmin Kc) (hb : bAbs ≤ b) (hβ : βAbs ≤ β)
    (hvmin0 : 0 < vmin) (hvmin : vmin ≤ deltaVar / 2) (hKc : KcAbs ≤ Kc)
    (heps : epsZero b β ≤ eps) (hepsK : GK * b ≤ eps ^ 2) (ℓ : ℕ) (lam : ℝ) :
    P.real {ω | lam * lcount P (epLayerSeq eps g ℓ) < ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)} ≤
      CK * Real.exp (-(θK * lam)) := by
  obtain ⟨hint, hle⟩ := hyperexp_all h0 hb hβ hvmin0 hvmin hKc heps hepsK ℓ
  have hm := ((layerOK_all h0 hb hβ hvmin0 hvmin hKc heps) ℓ).1.cnt_pos
  set m := lcount P (epLayerSeq eps g ℓ)
  set N : Ω → ℝ := fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)
  have hsub : {ω | lam * m < N ω} ⊆
      {ω | Real.exp (θK * lam) ≤ Real.exp (θK * N ω / m)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine Real.exp_le_exp.2 ?_
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ θK_pos.le
    rw [le_div_iff₀ hm]
    exact hω.le
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => (Real.exp_pos (θK * N ω / m)).le) hint (Real.exp (θK * lam))
  have h1 : Real.exp (θK * lam) * P.real {ω | lam * m < N ω} ≤ CK :=
    le_trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le)
      (hmark.trans hle)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact h1

/-- **Second moment of the normalised hyper-segment counts**:
`E (N⁽ℓ⁾ / m_ℓ)² ≤ 2 CK / θK²`. -/
theorem hyperexp_sq_all [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {b β vmin Kc eps : ℝ}
    (h0 : LayerOK P (inputPairs g) b β vmin Kc) (hb : bAbs ≤ b) (hβ : βAbs ≤ β)
    (hvmin0 : 0 < vmin) (hvmin : vmin ≤ deltaVar / 2) (hKc : KcAbs ≤ Kc)
    (heps : epsZero b β ≤ eps) (hepsK : GK * b ≤ eps ^ 2) (ℓ : ℕ) :
    Integrable (fun ω => (((epLayerSeq eps g ℓ 0 ω).2 : ℝ) / lcount P (epLayerSeq eps g ℓ)) ^ 2)
        P ∧
      ∫ ω, (((epLayerSeq eps g ℓ 0 ω).2 : ℝ) / lcount P (epLayerSeq eps g ℓ)) ^ 2 ∂P ≤
        2 * CK / θK ^ 2 := by
  obtain ⟨hint, hle⟩ := hyperexp_all h0 hb hβ hvmin0 hvmin hKc heps hepsK ℓ
  have hLℓ := ((layerOK_all h0 hb hβ hvmin0 hvmin hKc heps) ℓ).1
  have hm := hLℓ.cnt_pos
  have hθK := θK_pos
  set m := lcount P (epLayerSeq eps g ℓ)
  set N : Ω → ℝ := fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)
  have hNm : Measurable N := measurable_natCast_snd.comp (hLℓ.iid.measurable 0)
  have hpt : ∀ ω, (N ω / m) ^ 2 ≤ 2 / θK ^ 2 * Real.exp (θK * N ω / m) := by
    intro ω
    have hz : 0 ≤ N ω / m := div_nonneg (Nat.cast_nonneg _) hm.le
    have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg hθK.le hz)
    rw [← mul_div_assoc] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (θK * N ω / m), mul_nonneg hθK.le hz, mul_pow θK (N ω / m) 2,
      mul_div_assoc θK (N ω) m]
  have hint2 : Integrable (fun ω => (N ω / m) ^ 2) P := by
    refine (hint.const_mul (2 / θK ^ 2)).mono' ((hNm.div_const m).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint2, ?_⟩
  calc ∫ ω, (N ω / m) ^ 2 ∂P ≤ ∫ ω, 2 / θK ^ 2 * Real.exp (θK * N ω / m) ∂P :=
        integral_mono hint2 (hint.const_mul _) hpt
    _ = 2 / θK ^ 2 * ∫ ω, Real.exp (θK * N ω / m) ∂P := integral_const_mul _ _
    _ ≤ 2 / θK ^ 2 * CK := by gcongr
    _ = 2 * CK / θK ^ 2 := by ring

/-! ## A single threshold and the input law -/

/-- A single explicit threshold covering both `epsZero b β ≤ eps` and `GK b ≤ eps²`. -/
def epsK (b β : ℝ) : ℝ := max (epsZero b β) (Real.sqrt (GK * b))

theorem epsZero_le_of_epsK_le {b β eps : ℝ} (h : epsK b β ≤ eps) : epsZero b β ≤ eps :=
  le_trans (le_max_left _ _) h

theorem GK_mul_le_sq_of_epsK_le {b β eps : ℝ} (hb : 0 ≤ b) (h : epsK b β ≤ eps) :
    GK * b ≤ eps ^ 2 := by
  have h1 : Real.sqrt (GK * b) ≤ eps := le_trans (le_max_right _ _) h
  have h0 : 0 ≤ GK * b := mul_nonneg (le_trans zero_le_one one_le_GK) hb
  calc GK * b = Real.sqrt (GK * b) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ eps ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- **`cor:Ghyper` for an input gap law** (reference hierarchy): with the class constants
`bIn, βIn, vIn, KcIn` of the input law and `eps ≥ epsK (bIn μ₀ σ₀) (βIn σ₀ κ)`, every layer
satisfies `E exp(θK N⁽ℓ⁾ / m_ℓ) ≤ CK` and `P(N⁽ℓ⁾ > λ m_ℓ) ≤ CK exp(-θK λ)`. -/
theorem hyperexp_input [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Integrable (fun ω => Real.exp (θK * ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) /
        lcount P (epLayerSeq eps g ℓ))) P ∧
      ∫ ω, Real.exp (θK * ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) / lcount P (epLayerSeq eps g ℓ)) ∂P
        ≤ CK ∧
      ∀ lam : ℝ, P.real {ω | lam * lcount P (epLayerSeq eps g ℓ) <
        ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)} ≤ CK * Real.exp (-(θK * lam)) := by
  have hb0 : 0 ≤ bIn μ₀ σ₀ := le_trans bAbs_pos.le (bAbs_le_bIn μ₀ σ₀)
  have hvmin0 := vIn_pos hg.mu_pos hg.sigma_pos
  have he1 := epsZero_le_of_epsK_le heps
  have he2 := GK_mul_le_sq_of_epsK_le hb0 heps
  have h := hyperexp_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _) hvmin0
    (vIn_le μ₀ σ₀) KcAbs_le_KcIn he1 he2 ℓ
  exact ⟨h.1, h.2, hyperexp_tail_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    hvmin0 (vIn_le μ₀ σ₀) KcAbs_le_KcIn he1 he2 ℓ⟩

end

end PGM
