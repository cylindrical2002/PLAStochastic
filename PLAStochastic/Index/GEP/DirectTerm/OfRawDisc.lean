import PLAStochastic.Index.GEP.DirectTerm.SlopeCalibration
import PLAStochastic.Index.GEP.DirectTerm.BumpDirections
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# WP4 leaf `DirectTerm`: the reduction `DiscInterp ∧ RawDisc → DirectTerm`

The route of `direct-endpoint-response.md` (DT) §3 and `positive-direction-response.md` (PD)
§1, §5, §8, §9, on top of the coarse bound (`PLAStochastic/Index/GEP/DirectTerm/CoarseBound.lean`), the bump directions
(`PLAStochastic/Index/GEP/DirectTerm/BumpDirections.lean`) and the calibration (`PLAStochastic/Index/GEP/DirectTerm/SlopeCalibration.lean`).

1. **Interpolation** (`interp_bound`): `RawDisc` gives, for each direction law `σ`, a holomorphic
   `f` on a fixed disc with `‖f‖ ≤ K ε^p`, `‖f‖ ≤ K` on `[0, r/8]` and
   `f'(0) = ∫ I_F dσ - ∫ I_F dν`; `DiscInterp` with `δ = K + 1` turns this into
   `|∫ I_F dσ - ∫ I_F dν| ≤ K₂ (1 + log ε)²` (`dir_bound`).
2. **Positive directions and Lebesgue points** (`affine_core`, PD §5): the two laws of
   `exists_sigmaPair` differ by `c(x) (β_{x,h} - A(x) b₀ - B(x) b₁)`, so
   `|⨍_{[x-h,x+h]} I_F - ℓ(x)| ≤ 2K₂(1 + log ε)²/c(x)` with `ℓ` affine; the Lebesgue
   differentiation theorem (`IsUnifLocDoublingMeasure.ae_tendsto_average`) passes to `h → 0` at
   a.e. `x > 0`.  With `θσ = α/4`, `1/c(x) ≤ K e^{αx/2}`.
3. **Calibration** (`calib_bound`): the slope of `ℓ` is `O(ε)`.
4. **Conclusion** (`directTerm_of_rawDisc`): for `OutTest η M ψ`, `M > 0`, apply the above to
   `F(y) = ψ(y/C)/M` (so `|F y| ≤ e^{ηy/C}`, `κ = η/C ≤ 128 b η / ε²`); then
   `H_φ = M I_F / C` (`insKernel_const_mul`) and `C ≥ ε²/(128 b)` give (i) with the constant
   `a = M a'/C`, and the coarse bound `|I_F| ≤ K₁ ε⁴ e^{κx}` gives the tail (ii).  For `M = 0`
   the test vanishes on `[0,∞)` and so does the kernel (`directKernel_eq_zero`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {D θ vlo vhi : ℝ}

/-! ## Elementary inequalities -/

theorem one_add_log_sq_le {eps : ℝ} (heps : 1 ≤ eps) : (1 + Real.log eps) ^ 2 ≤ 4 * eps := by
  have h0 : 0 < eps := by linarith
  have hs : 0 < Real.sqrt eps := Real.sqrt_pos.2 h0
  have hl : Real.log eps = 2 * Real.log (Real.sqrt eps) := by
    rw [← Real.log_rpow hs, Real.rpow_two, Real.sq_sqrt h0.le]
  have h1 : Real.log (Real.sqrt eps) ≤ Real.sqrt eps - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have h3 : 1 + Real.log eps ≤ 2 * Real.sqrt eps := by linarith
  calc (1 + Real.log eps) ^ 2 ≤ (2 * Real.sqrt eps) ^ 2 := by gcongr
    _ = 4 * eps := by rw [mul_pow, Real.sq_sqrt h0.le]; ring

theorem one_add_mul_exp_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (a * x) ≤ (1 + 1 / a) * Real.exp (2 * a * x) := by
  have h1 : Real.exp (a * x) ≤ Real.exp (2 * a * x) := Real.exp_le_exp.2 (by nlinarith)
  have h2 : x * Real.exp (a * x) ≤ Real.exp (2 * a * x) / (2 * a - a) :=
    mul_exp_le_exp_div (by linarith)
  have h3 : Real.exp (2 * a * x) / (2 * a - a) = 1 / a * Real.exp (2 * a * x) := by
    rw [show 2 * a - a = a by ring]; ring
  calc (1 + x) * Real.exp (a * x) = Real.exp (a * x) + x * Real.exp (a * x) := by ring
    _ ≤ Real.exp (2 * a * x) + 1 / a * Real.exp (2 * a * x) := by linarith
    _ = (1 + 1 / a) * Real.exp (2 * a * x) := by ring

/-! ## Step 1: analytic interpolation on the disc -/

/-- **Interpolation bound**: a function with the three properties of `RawDisc` has
`‖f'(0)‖ ≤ K₂ (1 + log ε)²`. -/
theorem interp_bound (hI : DiscInterp) {r K : ℝ} (p : ℕ) (hr : 0 < r) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ (f : ℂ → ℂ) (eps : ℝ), 1 ≤ eps →
      DifferentiableOn ℂ f (Metric.ball 0 r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, ‖f z‖ ≤ K * eps ^ p) →
      (∀ t : ℝ, 0 ≤ t → t ≤ r / 8 → ‖f t‖ ≤ K) →
        ‖deriv f 0‖ ≤ K₂ * (1 + Real.log eps) ^ 2 := by
  obtain ⟨KI, hKI, hI⟩ := hI
  refine ⟨KI * (|K| + 1) * (2 + p) ^ 2 / r, by positivity, fun f eps heps hf hball hseg => ?_⟩
  have heps0 : 0 < eps := by linarith
  have hep : 1 ≤ eps ^ p := one_le_pow₀ heps
  set δ := |K| + 1 with hδ
  set M := |K| * eps ^ p + |K| + 1 with hM
  have hδ0 : 0 < δ := by positivity
  have hδM : δ ≤ M := by rw [hδ, hM]; nlinarith [abs_nonneg K]
  have h := hI f r M δ hr hδ0 hδM hf
    (fun z hz => (hball z hz).trans (by
      rw [hM]; nlinarith [le_abs_self K, abs_nonneg K]))
    (fun t ht0 ht1 => (hseg t ht0 ht1).trans (by rw [hδ]; linarith [le_abs_self K]))
  have hMδ1 : 1 ≤ M / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hMδ : M / δ ≤ 2 * eps ^ p := by
    rw [div_le_iff₀ hδ0, hM, hδ]
    nlinarith [abs_nonneg K]
  have hlog : Real.log (M / δ) ≤ 1 + p * Real.log eps := by
    calc Real.log (M / δ) ≤ Real.log (2 * eps ^ p) :=
          Real.log_le_log (by linarith) hMδ
      _ = Real.log 2 + p * Real.log eps := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ 1 + p * Real.log eps := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
  have hl0 : 0 ≤ Real.log (M / δ) := Real.log_nonneg hMδ1
  have hle0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsq : (1 + Real.log (M / δ)) ^ 2 ≤ (2 + p) ^ 2 * (1 + Real.log eps) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  calc ‖deriv f 0‖ ≤ KI * δ * (1 + Real.log (M / δ)) ^ 2 / r := h
    _ ≤ KI * δ * ((2 + p) ^ 2 * (1 + Real.log eps) ^ 2) / r := by gcongr
    _ = KI * (|K| + 1) * (2 + p) ^ 2 / r * (1 + Real.log eps) ^ 2 := by rw [hδ]; ring

/-! ## The kernel on compact intervals -/

theorem integrableOn_Icc_of_abs_le {I : ℝ → ℝ} (hI : Measurable I) {a b B : ℝ}
    (hB : ∀ y ∈ Icc a b, |I y| ≤ B) : IntegrableOn I (Icc a b) :=
  Integrable.of_bound hI.aestronglyMeasurable B
    (ae_restrict_of_forall_mem measurableSet_Icc fun y hy => by
      rw [Real.norm_eq_abs]; exact hB y hy)

/-- A kernel bounded by `B e^{κy}` on `[0,∞)` is integrable on every compact interval
of `[0,∞)`. -/
theorem integrableOn_Icc_of_exp {I : ℝ → ℝ} (hI : Measurable I) {B κ : ℝ} (hκ : 0 ≤ κ)
    (hb : ∀ y, 0 ≤ y → |I y| ≤ B * Real.exp (κ * y)) {a b : ℝ} (ha : 0 ≤ a) :
    IntegrableOn I (Icc a b) := by
  refine integrableOn_Icc_of_abs_le hI (B := |B| * Real.exp (κ * b)) fun y hy => ?_
  refine (hb y (ha.trans hy.1)).trans ?_
  calc B * Real.exp (κ * y) ≤ |B| * Real.exp (κ * y) :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
    _ ≤ |B| * Real.exp (κ * b) := by
        gcongr
        exact hy.2

/-- The kernel restricted to `(0,∞)` is locally integrable. -/
theorem locallyIntegrable_indicator_Ioi {I : ℝ → ℝ} (hI : Measurable I) {B κ : ℝ}
    (hb : ∀ y, 0 ≤ y → |I y| ≤ B * Real.exp (κ * y)) :
    LocallyIntegrable ((Ioi (0 : ℝ)).indicator I) volume := by
  have hc : Continuous fun x : ℝ => |B| * Real.exp (κ * |x|) := by fun_prop
  refine hc.locallyIntegrable.mono (hI.indicator measurableSet_Ioi).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ |B| * Real.exp (κ * |x|) by positivity)]
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), abs_of_pos hx]
    exact (hb x hx.le).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le)
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), abs_zero]
    positivity

/-! ## The vanishing test -/

/-- A test vanishing on `[0,∞)` has a vanishing direct kernel on `[0,∞)`. -/
theorem directKernel_eq_zero {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {eps : ℝ}
    (hC : 0 < lawC eps ν) {ψ : ℝ → ℝ} (hψ : ∀ y, 0 ≤ y → ψ y = 0) {x : ℝ} (hx : 0 ≤ x) :
    directKernel eps ν ψ x = 0 := by
  rw [directKernel, insKernel, div_eq_zero_iff]
  left
  refine (tsum_congr fun i => ?_).trans tsum_zero
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hν.ae_coord_nonneg] with g hg
  by_cases hgi : (i : ℕ∞) < gapSegLen eps g
  · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi)]
    exact hψ _ (div_nonneg (stopSum_nonneg (update_nonneg hg hx i)) hC.le)
  · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi)]
    rfl

/-! ## Steps 2–3: the affine approximation of the kernel -/

/-- **The kernel is affine up to `O((1 + log ε)² e^{αx/2})`** (PD §1, §5; DT (5), (6)), with a
slope `O(ε)`, for every normalized test `|F y| ≤ e^{κy}`, `κ ε² ≤ κ₀`. -/
theorem affine_core (hI : DiscInterp) (hR : RawDisc) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ α : ℝ, 0 < α → α ≤ θ / 2 → ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧
      ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ κ : ℝ, 0 ≤ κ → κ * eps ^ 2 ≤ κ₀ → ∀ F : ℝ → ℝ, Measurable F →
      (∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y)) →
        ∃ a' b' : ℝ, |b'| ≤ K * eps ∧ ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
          |insKernel eps ν (fun g => F (stopSum eps g)) x - (a' + b' * x)| ≤
            K * (1 + Real.log eps) ^ 2 * Real.exp (α / 2 * x) := by
  obtain ⟨γ, hγ, hRD⟩ := hR D θ vlo vhi hD hθ hvlo hv
  obtain ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, hker⟩ := kernel_coarse hD hθ hvlo hv
  obtain ⟨κ₂, K₅, e₅, hκ₂, hK₅, he₅, hcal⟩ := calib_bound hD hθ hvlo hv
  refine ⟨min (min κ₁ κ₂) γ, lt_min (lt_min hκ₁ hκ₂) hγ, fun α hα hαθ => ?_⟩
  set θσ := α / 4 with hθσdef
  have hθσ : 0 < θσ := by positivity
  obtain ⟨r, KR, eR, p, hr, hraw⟩ := hRD (1 + Real.exp (θσ * (5 / 2))) θσ hθσ
  obtain ⟨K₂, hK₂, hint⟩ := interp_bound hI (K := KR) p hr
  set K₃ := 4 * K₂ * Real.exp (α / 4) * (1 + 4 / α) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  refine ⟨max K₃ (K₅ * (1 + 4 * K₃)), max (max e₁ e₅) (max eR 1), by positivity,
    le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro eps heps ν hν κ hκ0 hκ F hF hFb
  have he1 : e₁ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he5 : e₅ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have heR : eR ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have heps1 : 1 ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have heps0 : 0 < eps := by linarith
  have hκa : κ * eps ^ 2 ≤ κ₁ := hκ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hκb : κ * eps ^ 2 ≤ κ₂ := hκ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hκc : κ * eps ^ 2 ≤ γ := hκ.trans (min_le_right _ _)
  set I := insKernel eps ν (fun g => F (stopSum eps g)) with hIdef
  set L := (1 + Real.log eps) ^ 2 with hL
  have hL0 : 0 ≤ L := sq_nonneg _
  obtain ⟨hIm, hIb, -⟩ := hker eps he1 ν hν κ hκ0 hκa F hF hFb
  -- one direction (RawDisc and DiscInterp)
  have hFγ : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (γ * y / eps ^ 2) := by
    intro y hy
    refine (hFb y hy).trans (Real.exp_le_exp.2 ?_)
    have hκ' : κ ≤ γ / eps ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hκc
    calc κ * y ≤ γ / eps ^ 2 * y := mul_le_mul_of_nonneg_right hκ' hy
      _ = γ * y / eps ^ 2 := by ring
  have hdir : ∀ σ : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (θσ * (5 / 2))) θσ σ →
      |∫ y, I y ∂(σ : Measure ℝ) - ∫ y, I y ∂(ν : Measure ℝ)| ≤ K₂ * L := by
    intro σ hσ
    obtain ⟨f, hf, hfb, hfs, hfd⟩ := hraw eps heR ν σ hν hσ F hF hFγ
    have h := hint f eps heps1 hf hfb hfs
    rwa [hfd, Complex.norm_real, Real.norm_eq_abs] at h
  -- the affine function
  set i₀ := ⨍ y in Icc (1 / 4 : ℝ) (3 / 4), I y with hi₀
  set i₁ := ⨍ y in Icc (3 / 2 : ℝ) (5 / 2), I y with hi₁
  set a' := (4 * i₀ - i₁) / 3 with ha'
  set b' := 2 * (i₁ - i₀) / 3 with hb'
  have hℓ : ∀ x, dirA x * i₀ + dirB x * i₁ = a' + b' * x := by
    intro x; simp only [dirA, dirB, ha', hb']; ring
  -- the averaged bound for small bumps
  have hloc : ∀ x, 0 < x → ∀ h, 0 < h → h < x → h ≤ 1 →
      |(⨍ y in Metric.closedBall x h, I y) - (a' + b' * x)| ≤ 2 * K₂ * L / dirC θσ x := by
    intro x hx h hh hhx hh1
    obtain ⟨σp, σm, hσp, hσm, hdiff⟩ := exists_sigmaPair hθσ hx hh hhx hh1
    obtain ⟨-, -, heq⟩ := hdiff I (integrableOn_Icc_of_exp hIm hκ0 hIb (by linarith))
      (integrableOn_Icc_of_exp hIm hκ0 hIb (by norm_num))
      (integrableOn_Icc_of_exp hIm hκ0 hIb (by norm_num))
    have h1 := hdir σp hσp
    have h2 := hdir σm hσm
    have hc := dirC_pos θσ hx
    have h3 : |∫ y, I y ∂(σp : Measure ℝ) - ∫ y, I y ∂(σm : Measure ℝ)| ≤ 2 * K₂ * L := by
      calc |∫ y, I y ∂(σp : Measure ℝ) - ∫ y, I y ∂(σm : Measure ℝ)|
          = |(∫ y, I y ∂(σp : Measure ℝ) - ∫ y, I y ∂(ν : Measure ℝ)) -
              (∫ y, I y ∂(σm : Measure ℝ) - ∫ y, I y ∂(ν : Measure ℝ))| := by ring_nf
        _ ≤ |∫ y, I y ∂(σp : Measure ℝ) - ∫ y, I y ∂(ν : Measure ℝ)| +
              |∫ y, I y ∂(σm : Measure ℝ) - ∫ y, I y ∂(ν : Measure ℝ)| := abs_sub _ _
        _ ≤ 2 * K₂ * L := by linarith
    rw [heq, abs_mul, abs_of_pos hc] at h3
    rw [le_div_iff₀ hc]
    calc |(⨍ y in Metric.closedBall x h, I y) - (a' + b' * x)| * dirC θσ x
        = dirC θσ x * |(⨍ y in Metric.closedBall x h, I y) - dirA x * i₀ - dirB x * i₁| := by
          rw [← hℓ x, mul_comm]; ring_nf
      _ ≤ 2 * K₂ * L := h3
  -- Lebesgue differentiation
  have hJ := locallyIntegrable_indicator_Ioi hIm hIb
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) hJ 1
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), 0 < x →
      |I x - (a' + b' * x)| ≤ 2 * K₂ * L / dirC θσ x := by
    filter_upwards [hleb] with x hx hx0
    have ht := hx (ι := ℝ) (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id
      (eventually_nhdsWithin_of_forall fun j hj =>
        Metric.mem_closedBall_self (by rw [one_mul]; exact le_of_lt hj))
    have hJx : (Ioi (0 : ℝ)).indicator I x = I x := indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx0) _
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), |(⨍ y in Metric.closedBall x (id h),
        (Ioi (0 : ℝ)).indicator I y) - (a' + b' * x)| ≤ 2 * K₂ * L / dirC θσ x := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (x / 2) 1 by positivity)] with h hh
      have hhx : h < x := lt_of_lt_of_le hh.2 ((min_le_left _ _).trans (by linarith))
      have hh1 : h ≤ 1 := hh.2.le.trans (min_le_right _ _)
      have hJI : (⨍ y in Metric.closedBall x (id h), (Ioi (0 : ℝ)).indicator I y) =
          ⨍ y in Metric.closedBall x h, I y := by
        refine setAverage_congr_fun Metric.isClosed_closedBall.measurableSet
          (Eventually.of_forall fun y hy => ?_)
        have hy' : x - h ≤ y := by
          rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
          simp only [id] at hy
          linarith [hy.1]
        exact indicator_of_mem (show y ∈ Ioi (0 : ℝ) from by
          show 0 < y; linarith) _
      rw [hJI]
      exact hloc x hx0 h hh.1 hhx hh1
    have hlim : Tendsto (fun h => |(⨍ y in Metric.closedBall x (id h),
        (Ioi (0 : ℝ)).indicator I y) - (a' + b' * x)|) (𝓝[>] (0 : ℝ))
        (𝓝 |(Ioi (0 : ℝ)).indicator I x - (a' + b' * x)|) := (ht.sub_const _).abs
    rw [← hJx]
    exact le_of_tendsto hlim hev
  -- the exponential form of the error
  have hE : ∀ x, 0 < x → 2 * K₂ * L / dirC θσ x ≤ K₃ * L * Real.exp (α / 2 * x) := by
    intro x hx
    have h1 := one_add_mul_exp_le (a := α / 4) (by positivity) hx.le
    rw [show 2 * (α / 4) * x = α / 2 * x by ring, show 1 / (α / 4) = 4 / α by field_simp] at h1
    rw [div_eq_mul_one_div, one_div_dirC θσ hx, hθσdef,
      show α / 4 * (x + 1) = α / 4 * x + α / 4 by ring, Real.exp_add, hK₃]
    have hK₂L : 0 ≤ 2 * K₂ * L := by positivity
    calc 2 * K₂ * L * (2 * (1 + x) * (Real.exp (α / 4 * x) * Real.exp (α / 4)))
        = 4 * K₂ * L * Real.exp (α / 4) * ((1 + x) * Real.exp (α / 4 * x)) := by ring
      _ ≤ 4 * K₂ * L * Real.exp (α / 4) * ((1 + 4 / α) * Real.exp (α / 2 * x)) := by gcongr
      _ = 4 * K₂ * Real.exp (α / 4) * (1 + 4 / α) * L * Real.exp (α / 2 * x) := by ring
  have hae' : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      |I x - (a' + b' * x)| ≤ K₃ * L * Real.exp (α / 2 * x) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with x hx hx0
    exact (hx hx0).trans (hE x hx0)
  -- calibration of the slope
  have hb := hcal eps he5 ν hν κ hκ0 hκb F hF hFb a' b' (K₃ * L) (α / 2) (by linarith)
    (by positivity) (hν.ae_of_ae_Ioi hae')
  have hL4 : L ≤ 4 * eps := one_add_log_sq_le heps1
  refine ⟨a', b', ?_, ?_⟩
  · calc |b'| ≤ K₅ * (eps + K₃ * L) := hb
      _ ≤ K₅ * (eps + K₃ * (4 * eps)) := by gcongr
      _ = K₅ * (1 + 4 * K₃) * eps := by ring
      _ ≤ max K₃ (K₅ * (1 + 4 * K₃)) * eps := by gcongr; exact le_max_right _ _
  · filter_upwards [hae'] with x hx
    refine hx.trans ?_
    gcongr
    exact le_max_left _ _

/-! ## Step 4: the direct term -/

/-- **Leaf 4A-D from the analytic interfaces** (DT §3; PD §1, §5, §8, §9). -/
theorem directTerm_of_rawDisc (hI : DiscInterp) (hR : RawDisc) : DirectTerm := by
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨κ₀, hκ₀, hcore⟩ := affine_core hI hR hD hθ hvlo hv
  obtain ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, hker⟩ := kernel_coarse hD hθ hvlo hv
  obtain ⟨e₀, he₀1, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  have hb0 : 0 < regB vhi := (regV_pos hvlo).trans_le (regV_le_regB hv)
  set bB := 128 * regB vhi with hbB
  have hbB0 : 0 < bB := by positivity
  refine ⟨min κ₀ κ₁ / bB, by positivity, fun η hη hηD => ?_⟩
  refine ⟨θ / 2, by positivity, fun α ζ hα hαD hζ => ?_⟩
  obtain ⟨Kc, ec, hKc, hec, hcoreα⟩ := hcore α hα hαD
  refine ⟨max (bB * (4 * Kc + Kc * (2 / α))) (bB * K₁),
    max (max ec e₁) (max e₀ (bB * η / ζ + 1)), ?_⟩
  intro eps heps ν hν M ψ hψ
  have hec' : ec ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he1 : e₁ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have he0 : e₀ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have heζ : bB * η / ζ + 1 ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have heps1 : 1 ≤ eps := hec.trans hec'
  have heps0 : 0 < eps := by linarith
  have he2 : eps ≤ eps ^ 2 := by nlinarith
  obtain ⟨-, hCm, -⟩ := hfacts eps he0 ν hν
  set C := lawC eps ν with hCdef
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hCm
  have hCinv : 1 / C ≤ bB / eps ^ 2 := by
    rw [div_le_div_iff₀ hC0 (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hCm
    linarith
  have hM : 0 ≤ M := by
    have h := hψ.2 0 le_rfl
    simpa using (abs_nonneg (ψ 0)).trans h
  set Kf := max (bB * (4 * Kc + Kc * (2 / α))) (bB * K₁) with hKf
  rcases hM.eq_or_lt with hM0 | hMpos
  · -- the vanishing test
    subst hM0
    have hψ0 : ∀ y, 0 ≤ y → ψ y = 0 := fun y hy =>
      abs_eq_zero.1 (le_antisymm (by simpa using hψ.2 y hy) (abs_nonneg _))
    have hz : ∀ x, 0 < x → directKernel eps ν ψ x = 0 := fun x hx =>
      directKernel_eq_zero hν hC0 hψ0 hx.le
    refine ⟨⟨0, ?_⟩, ?_⟩
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      rw [hz x hx]; simp
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      rw [hz x hx]; simp
  · -- the normalized test `F(y) = ψ(y/C)/M`
    set κ := η / C with hκdef
    have hκ0 : 0 ≤ κ := by positivity
    have hκe : κ * eps ^ 2 ≤ min κ₀ κ₁ := by
      calc κ * eps ^ 2 = η * (eps ^ 2 * (1 / C)) := by rw [hκdef]; ring
        _ ≤ η * (eps ^ 2 * (bB / eps ^ 2)) := by gcongr
        _ = η * bB := by field_simp
        _ ≤ min κ₀ κ₁ := by rwa [le_div_iff₀ hbB0] at hηD
    have hκζ : κ ≤ ζ := by
      calc κ = η * (1 / C) := by rw [hκdef]; ring
        _ ≤ η * (bB / eps ^ 2) := by gcongr
        _ ≤ ζ := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            have h1 : bB * η / ζ ≤ eps := by linarith
            rw [div_le_iff₀ hζ] at h1
            nlinarith
    set F : ℝ → ℝ := fun y => ψ (y / C) / M with hFdef
    have hF : Measurable F := (hψ.1.comp (measurable_id.div_const C)).div_const M
    have hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y) := by
      intro y hy
      rw [hFdef, abs_div, abs_of_pos hMpos, div_le_iff₀ hMpos]
      calc |ψ (y / C)| ≤ M * Real.exp (η * (y / C)) := hψ.2 _ (by positivity)
        _ = Real.exp (κ * y) * M := by rw [hκdef]; ring_nf
    have hdk : ∀ x, directKernel eps ν ψ x =
        M * insKernel eps ν (fun g => F (stopSum eps g)) x / C := by
      intro x
      rw [directKernel, ← hCdef, ← insKernel_const_mul]
      congr 2
      funext g
      rw [hFdef]
      field_simp
    obtain ⟨a', b', hb', hae⟩ := hcoreα eps hec' ν hν κ hκ0 (hκe.trans (min_le_left _ _))
      F hF hFb
    obtain ⟨-, hIb, -⟩ := hker eps he1 ν hν κ hκ0 (hκe.trans (min_le_right _ _)) F hF hFb
    set I := insKernel eps ν (fun g => F (stopSum eps g)) with hIdef
    have hL4 : (1 + Real.log eps) ^ 2 ≤ 4 * eps := one_add_log_sq_le heps1
    refine ⟨⟨M * a' / C, ?_⟩, ?_⟩
    · filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx hx0
      have hx0' : 0 < x := hx0
      rw [hdk x]
      have hxe : x ≤ 2 / α * Real.exp (α / 2 * x) := by
        have := le_exp_div (t := x) (show 0 < α / 2 by positivity)
        rw [div_div_eq_mul_div] at this
        calc x ≤ Real.exp (α / 2 * x) * 2 / α := this
          _ = 2 / α * Real.exp (α / 2 * x) := by ring
      have hee : Real.exp (α / 2 * x) ≤ Real.exp (α * x) := Real.exp_le_exp.2 (by nlinarith)
      have hKc0 : 0 ≤ Kc := hKc
      have hI1 : |I x - a'| ≤ Kc * (4 * eps) * Real.exp (α / 2 * x) +
          Kc * eps * (2 / α * Real.exp (α / 2 * x)) := by
        calc |I x - a'| = |(I x - (a' + b' * x)) + b' * x| := by ring_nf
          _ ≤ |I x - (a' + b' * x)| + |b' * x| := abs_add_le _ _
          _ = |I x - (a' + b' * x)| + |b'| * x := by rw [abs_mul, abs_of_pos hx0']
          _ ≤ Kc * (1 + Real.log eps) ^ 2 * Real.exp (α / 2 * x) + Kc * eps * x := by
              gcongr
          _ ≤ Kc * (4 * eps) * Real.exp (α / 2 * x) +
                Kc * eps * (2 / α * Real.exp (α / 2 * x)) := by gcongr
      have hI2 : |I x - a'| ≤ eps * (4 * Kc + Kc * (2 / α)) * Real.exp (α * x) := by
        calc |I x - a'| ≤ eps * (4 * Kc + Kc * (2 / α)) * Real.exp (α / 2 * x) := by
              linarith [hI1]
          _ ≤ eps * (4 * Kc + Kc * (2 / α)) * Real.exp (α * x) := by gcongr
      calc |M * I x / C - M * a' / C| = M * (1 / C) * |I x - a'| := by
            rw [show M * I x / C - M * a' / C = M * (1 / C) * (I x - a') by ring, abs_mul,
              abs_of_nonneg (by positivity)]
        _ ≤ M * (bB / eps ^ 2) * (eps * (4 * Kc + Kc * (2 / α)) * Real.exp (α * x)) := by
            gcongr
        _ = M * (bB * (4 * Kc + Kc * (2 / α)) / eps) * Real.exp (α * x) := by
            field_simp
        _ ≤ M * (Kf / eps) * Real.exp (α * x) := by
            gcongr
            exact le_max_left _ _
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 ≤ x := le_of_lt hx
      rw [hdk x]
      have hk := hIb x hx0
      calc |M * I x / C| = M * (1 / C) * |I x| := by
            rw [show M * I x / C = M * (1 / C) * I x by ring, abs_mul,
              abs_of_nonneg (by positivity)]
        _ ≤ M * (bB / eps ^ 2) * (K₁ * eps ^ 4 * Real.exp (κ * x)) := by gcongr
        _ = M * (bB * K₁ * eps ^ 2) * Real.exp (κ * x) := by field_simp
        _ ≤ M * (Kf * eps ^ 2) * Real.exp (ζ * x) := by
            gcongr
            exact le_max_right _ _

end

end PGM
