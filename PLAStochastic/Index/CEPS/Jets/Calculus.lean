import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import PLAStochastic.ForMathlib.Analysis.Complex.Osgood
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# X8: generic calculus lemmas for the jet functionals

Analysis facts used by the jet package, independent of the CEPS model:

* `iteratedDeriv_integral_of_dominated`: iterated differentiation under the integral sign on an
  open set, for a family `φ k` of successive derivatives with integrable dominating bounds
  (with the companion `integrable_of_dominated_family`);
* `norm_sub_taylor_le_of_ball`: if `f` is holomorphic on `B(0, R)` with `‖f z - f 0‖ ≤ K`, the
  Taylor remainder of order `N` at `|z| ≤ R/4` is at most `2 K (2|z|/R)^{N+1}`;
* `iteratedDeriv_eq_of_norm_sub_le_pow`: two holomorphic functions with
  `‖f z - g z‖ ≤ K |z|^{k+1}` near `0` have the same derivatives at `0` up to order `k`;
* `integrable_of_ball_bound`, `norm_integral_sub_le_of_ball`, `differentiableOn_integral_of_ball`:
  holomorphy of a parametric integral `h ↦ ∫ Ψ a h` on `B(0, R)` from holomorphy of each
  `Ψ a` and an integrable bound `‖Ψ a h - Ψ a 0‖ ≤ B a`;
* `integral_im_eq_zero_of_conj`, `integral_eq_ofReal_re_of_conj`: the line integral of a
  conjugation-symmetric integrand `G (-y) = conj (G y)` is real;
* `iteratedDeriv_inv_sub`, `iteratedDeriv_neg_log_one_sub`: the derivatives
  `∂^m (s - z)⁻¹ = m! / (s - z)^{m+1}` and `∂^{m+1} (-log (1 - ζ))|_{ζ=0} = m!`.
-/

noncomputable section

open MeasureTheory Metric Filter Topology

namespace PGM

/-! ### Iterated differentiation under the integral sign -/

section Dominated

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {φ : ℕ → 𝕜 → α → E}
  {B : ℕ → α → ℝ} {U : Set 𝕜} {N : ℕ}

omit [RCLike 𝕜] [NormedSpace ℝ E] [NormedSpace 𝕜 E] in
/-- The members `φ k x` (`k ≤ N`, `x ∈ U`) of a dominated derivative family are integrable. -/
theorem integrable_of_dominated_family
    (hmeas : ∀ k ≤ N, ∀ x ∈ U, AEStronglyMeasurable (φ k x) μ)
    (hint : ∀ x ∈ U, Integrable (φ 0 x) μ)
    (hbound : ∀ k < N, ∀ a, ∀ x ∈ U, ‖φ (k + 1) x a‖ ≤ B k a)
    (hB : ∀ k < N, Integrable (B k) μ) :
    ∀ k ≤ N, ∀ x ∈ U, Integrable (φ k x) μ := by
  intro k hk x hx
  cases k with
  | zero => exact hint x hx
  | succ j =>
    exact (hB j (by omega)).mono' (hmeas (j + 1) hk x hx)
      (ae_of_all _ fun a => hbound j (by omega) a x hx)

/-- Iterated differentiation under the integral sign on an open set: if `φ (k + 1)` is the
derivative of `φ k` in `x ∈ U`, dominated by an integrable `B k`, then the `N`-th derivative of
`x ↦ ∫ φ 0 x` is `x ↦ ∫ φ N x` on `U`. -/
theorem iteratedDeriv_integral_of_dominated [CompleteSpace E] (hU : IsOpen U)
    (hmeas : ∀ k ≤ N, ∀ x ∈ U, AEStronglyMeasurable (φ k x) μ)
    (hint : ∀ x ∈ U, Integrable (φ 0 x) μ)
    (hderiv : ∀ k < N, ∀ a, ∀ x ∈ U, HasDerivAt (fun x => φ k x a) (φ (k + 1) x a) x)
    (hbound : ∀ k < N, ∀ a, ∀ x ∈ U, ‖φ (k + 1) x a‖ ≤ B k a)
    (hB : ∀ k < N, Integrable (B k) μ) :
    ∀ x ∈ U, iteratedDeriv N (fun x => ∫ a, φ 0 x a ∂μ) x = ∫ a, φ N x a ∂μ := by
  have hI := integrable_of_dominated_family hmeas hint hbound hB
  suffices H : ∀ n ≤ N, ∀ x ∈ U,
      iteratedDeriv n (fun x => ∫ a, φ 0 x a ∂μ) x = ∫ a, φ n x a ∂μ from H N le_rfl
  intro n
  induction n with
  | zero => intro _ x _; simp
  | succ n ih =>
    intro hn x hx
    have hev : iteratedDeriv n (fun x => ∫ a, φ 0 x a ∂μ) =ᶠ[𝓝 x]
        fun y => ∫ a, φ n y a ∂μ := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih (by omega) y hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun y a => φ n y a) (F' := fun y a => φ (n + 1) y a) (bound := B n)
      (hU.mem_nhds hx)
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hmeas n (by omega) y hy)
      (hI n (by omega) x hx) (hmeas (n + 1) hn x hx)
      (ae_of_all _ fun a y hy => hbound n hn a y hy) (hB n hn)
      (ae_of_all _ fun a y hy => hderiv n hn a y hy)
    exact key.2.deriv

end Dominated

/-! ### Taylor remainders and coefficient identification on discs -/

/-- Complex Taylor remainder from a bound on a disc: if `f` is holomorphic on `B(0, R)` and
`‖f z - f 0‖ ≤ K` there, then for `‖z‖ ≤ R / 4` the remainder after the degree-`N` Taylor
polynomial is at most `2 K (2‖z‖/R)^{N+1}`. -/
theorem norm_sub_taylor_le_of_ball {f : ℂ → ℂ} {R K : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hK : ∀ z ∈ ball (0 : ℂ) R, ‖f z - f 0‖ ≤ K)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ R / 4) :
    ‖f z - ∑ k ∈ Finset.range (N + 1), iteratedDeriv k f 0 / (k.factorial : ℂ) * z ^ k‖ ≤
      2 * K * (2 * ‖z‖ / R) ^ (N + 1) := by
  have hK0 : 0 ≤ K := by simpa using hK 0 (mem_ball_self hR)
  have hzR : z ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right]; linarith
  set t : ℕ → ℂ := fun k => iteratedDeriv k f 0 / (k.factorial : ℂ) * z ^ k with ht
  have hsum : HasSum t (f z) := by
    have := Complex.hasSum_taylorSeries_on_ball hf hzR
    have heq : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (z - 0) ^ n • iteratedDeriv n f 0) = t := by
      funext n
      simp only [ht, sub_zero, smul_eq_mul]
      ring
    rw [heq] at this
    exact this
  set q : ℝ := 2 * ‖z‖ / R with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by rw [hq, div_le_iff₀ hR]; linarith
  have hcoef : ∀ k, 1 ≤ k → ‖t k‖ ≤ K * q ^ k := by
    intro k hk
    have hg : DifferentiableOn ℂ (fun w => f w - f 0) (ball 0 R) := hf.sub_const _
    have hD : iteratedDeriv k (fun w => f w - f 0) 0 = iteratedDeriv k f 0 := by
      have : (fun w => f w - f 0) = fun w => (-f 0) + f w := by funext w; ring
      rw [this, iteratedDeriv_const_add (by omega)]
    have hC := norm_iteratedDeriv_le_of_ball k hR hg hK
    rw [hD] at hC
    simp only [ht]
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    calc ‖iteratedDeriv k f 0‖ / k.factorial * ‖z‖ ^ k
        ≤ (k.factorial * K / (R / 2) ^ k) / k.factorial * ‖z‖ ^ k := by gcongr
      _ = K * q ^ k := by rw [hq, div_pow, div_pow]; field_simp; ring
  have htail : HasSum (fun n => t (n + (N + 1))) (f z - ∑ k ∈ Finset.range (N + 1), t k) :=
    (hasSum_nat_add_iff' (N + 1)).mpr hsum
  have hgeom : HasSum (fun n : ℕ => K * q ^ (N + 1) * q ^ n) (K * q ^ (N + 1) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hle := tsum_of_norm_bounded hgeom (fun n => by
    calc ‖t (n + (N + 1))‖ ≤ K * q ^ (n + (N + 1)) := hcoef _ (by omega)
      _ = K * q ^ (N + 1) * q ^ n := by ring)
  rw [htail.tsum_eq] at hle
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  calc ‖f z - ∑ k ∈ Finset.range (N + 1), t k‖ ≤ K * q ^ (N + 1) * (1 - q)⁻¹ := hle
    _ ≤ K * q ^ (N + 1) * 2 := by gcongr
    _ = 2 * K * q ^ (N + 1) := by ring

/-- Taylor coefficients are determined by an `O(‖z‖^{k+1})` difference: if `f, g` are holomorphic
on `B(0, R)` and `‖f z - g z‖ ≤ K ‖z‖^{k+1}` there, then `f⁽ⁱ⁾(0) = g⁽ⁱ⁾(0)` for `i ≤ k`. -/
theorem iteratedDeriv_eq_of_norm_sub_le_pow {f g : ℂ → ℂ} {R K : ℝ} {k : ℕ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (h : ∀ z ∈ ball (0 : ℂ) R, ‖f z - g z‖ ≤ K * ‖z‖ ^ (k + 1)) {i : ℕ} (hi : i ≤ k) :
    iteratedDeriv i f 0 = iteratedDeriv i g 0 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hfc : ContDiffAt ℂ i f 0 :=
    (hf.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds h0)
  have hgc : ContDiffAt ℂ i g 0 :=
    (hg.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds h0)
  rw [← sub_eq_zero, ← iteratedDeriv_sub hfc hgc]
  obtain ⟨j, rfl⟩ : ∃ j, k = i + j := ⟨k - i, by omega⟩
  set c : ℝ := i.factorial * |K| * 2 ^ i with hc
  have hbd : ∀ r, 0 < r → r < R → ‖iteratedDeriv i (f - g) 0‖ ≤ c * r ^ (j + 1) := by
    intro r hr hrR
    have hd : DifferentiableOn ℂ (f - g) (ball 0 r) :=
      (hf.sub hg).mono (ball_subset_ball hrR.le)
    have hM : ∀ z ∈ ball (0 : ℂ) r, ‖(f - g) z‖ ≤ |K| * r ^ (i + j + 1) := by
      intro z hz
      have hz' : ‖z‖ < r := by rwa [mem_ball, dist_zero_right] at hz
      calc ‖(f - g) z‖ = ‖f z - g z‖ := rfl
        _ ≤ K * ‖z‖ ^ (i + j + 1) := h z (ball_subset_ball hrR.le hz)
        _ ≤ |K| * ‖z‖ ^ (i + j + 1) := by gcongr; exact le_abs_self K
        _ ≤ |K| * r ^ (i + j + 1) := by gcongr
    calc ‖iteratedDeriv i (f - g) 0‖ ≤ i.factorial * (|K| * r ^ (i + j + 1)) / (r / 2) ^ i :=
          norm_iteratedDeriv_le_of_ball i hr hd hM
      _ = c * r ^ (j + 1) := by rw [hc, div_pow]; field_simp; ring
  have ht : Tendsto (fun r : ℝ => c * r ^ (j + 1)) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => c * r ^ (j + 1)) (𝓝 0) (𝓝 (c * 0 ^ (j + 1))) :=
      ((continuous_const.mul (continuous_pow (j + 1))).tendsto 0)
    rw [zero_pow (Nat.succ_ne_zero j), mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖iteratedDeriv i (f - g) 0‖ ≤ c * r ^ (j + 1) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr using hbd r hr.1 hr.2
  exact norm_le_zero_iff.mp (ge_of_tendsto ht hev)

/-! ### Holomorphy of parametric integrals -/

section Parametric

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {Ψ : α → ℂ → ℂ} {R : ℝ} {B : α → ℝ}

/-- Integrability of `a ↦ Ψ a h` on the disc from integrability at `0` and a difference bound. -/
theorem integrable_of_ball_bound
    (hmeas : ∀ h ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun a => Ψ a h) μ)
    (hint : Integrable (fun a => Ψ a 0) μ) (hB : Integrable B μ)
    (hbound : ∀ a, ∀ h ∈ ball (0 : ℂ) R, ‖Ψ a h - Ψ a 0‖ ≤ B a) {h : ℂ}
    (hh : h ∈ ball (0 : ℂ) R) : Integrable (fun a => Ψ a h) μ := by
  refine (hint.norm.add hB).mono' (hmeas h hh) (ae_of_all _ fun a => ?_)
  calc ‖Ψ a h‖ = ‖Ψ a 0 + (Ψ a h - Ψ a 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖Ψ a 0‖ + ‖Ψ a h - Ψ a 0‖ := norm_add_le _ _
    _ ≤ ‖Ψ a 0‖ + B a := by gcongr; exact hbound a h hh

/-- The parametric integral moves by at most `∫ B` on the disc. -/
theorem norm_integral_sub_le_of_ball
    (hmeas : ∀ h ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun a => Ψ a h) μ)
    (hint : Integrable (fun a => Ψ a 0) μ) (hB : Integrable B μ)
    (hbound : ∀ a, ∀ h ∈ ball (0 : ℂ) R, ‖Ψ a h - Ψ a 0‖ ≤ B a) {h : ℂ}
    (hh : h ∈ ball (0 : ℂ) R) :
    ‖(∫ a, Ψ a h ∂μ) - ∫ a, Ψ a 0 ∂μ‖ ≤ ∫ a, B a ∂μ := by
  rw [← integral_sub (integrable_of_ball_bound hmeas hint hB hbound hh) hint]
  exact norm_integral_le_of_norm_le hB (ae_of_all _ fun a => hbound a h hh)

/-- Holomorphy of a parametric integral on a disc: if each `Ψ a` is holomorphic on `B(0, R)`,
`a ↦ Ψ a h` is measurable, `Ψ · 0` is integrable and `‖Ψ a h - Ψ a 0‖ ≤ B a` with `B`
integrable, then `h ↦ ∫ Ψ a h` is holomorphic on `B(0, R)`. -/
theorem differentiableOn_integral_of_ball (_hR : 0 < R)
    (hΨ : ∀ a, DifferentiableOn ℂ (Ψ a) (ball 0 R))
    (hmeas : ∀ h ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun a => Ψ a h) μ)
    (hint : Integrable (fun a => Ψ a 0) μ) (hB : Integrable B μ)
    (hbound : ∀ a, ∀ h ∈ ball (0 : ℂ) R, ‖Ψ a h - Ψ a 0‖ ≤ B a) :
    DifferentiableOn ℂ (fun h => ∫ a, Ψ a h ∂μ) (ball 0 R) := by
  intro h₀ hh₀
  have hh₀' : ‖h₀‖ < R := by rwa [mem_ball, dist_zero_right] at hh₀
  set ρ : ℝ := R - ‖h₀‖ with hρ
  have hρ0 : 0 < ρ := by linarith
  have hsubball : ball h₀ ρ ⊆ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    calc ‖w‖ = ‖(w - h₀) + h₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - h₀‖ + ‖h₀‖ := norm_add_le _ _
      _ < R := by linarith
  have hdb : ∀ a, ∀ z ∈ ball h₀ (ρ / 2), ‖deriv (Ψ a) z‖ ≤ 4 * B a / ρ := by
    intro a z hz
    have hd : DifferentiableOn ℂ (fun w => Ψ a w - Ψ a 0) (ball h₀ ρ) :=
      ((hΨ a).mono hsubball).sub_const _
    have := norm_deriv_le_of_ball_half hρ0 hd (fun w hw => hbound a w (hsubball hw)) hz
    rwa [deriv_sub_const] at this
  have hdiff : ∀ a, ∀ z ∈ ball h₀ (ρ / 2), HasDerivAt (Ψ a) (deriv (Ψ a) z) z := by
    intro a z hz
    have hz' : z ∈ ball (0 : ℂ) R := hsubball (ball_subset_ball (by linarith) hz)
    exact ((hΨ a z hz').differentiableAt (isOpen_ball.mem_nhds hz')).hasDerivAt
  obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ (half_pos hρ0)
  have hmem_seq : ∀ n : ℕ, h₀ + ((ρ / 2 / (n + 1) : ℝ) : ℂ) ∈ ball (0 : ℂ) R := by
    intro n
    apply hsubball
    have hpos : 0 < ρ / 2 / ((n : ℝ) + 1) := by positivity
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos]
    calc ρ / 2 / ((n : ℝ) + 1) ≤ ρ / 2 :=
          div_le_self (by positivity) (by linarith [n.cast_nonneg (α := ℝ)])
      _ < ρ := half_lt_self hρ0
  have hF'meas : AEStronglyMeasurable (fun a => deriv (Ψ a) h₀) μ :=
    aestronglyMeasurable_deriv_param (G := Ψ) hne hlim (fun n => hmeas _ (hmem_seq n))
      (hmeas h₀ hh₀) (fun a => (hdiff a h₀ (mem_ball_self (half_pos hρ0))).differentiableAt)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun h a => Ψ a h) (F' := fun z a => deriv (Ψ a) z) (bound := fun a => 4 * B a / ρ)
    (ball_mem_nhds h₀ (half_pos hρ0))
    (Filter.eventually_of_mem (isOpen_ball.mem_nhds hh₀) fun h hh => hmeas h hh)
    (integrable_of_ball_bound hmeas hint hB hbound hh₀) hF'meas
    (ae_of_all _ fun a z hz => hdb a z hz) ((hB.const_mul 4).div_const ρ)
    (ae_of_all _ fun a z hz => hdiff a z hz)
  exact key.2.differentiableAt.differentiableWithinAt

end Parametric

/-! ### Conjugation-symmetric line integrals -/

/-- The integral over `ℝ` of an integrand with `G (-y) = conj (G y)` is real. -/
theorem integral_im_eq_zero_of_conj {G : ℝ → ℂ} (h : ∀ y, G (-y) = (starRingEnd ℂ) (G y)) :
    (∫ y, G y).im = 0 := by
  have h1 : (starRingEnd ℂ) (∫ y, G y) = ∫ y, G y := by
    rw [← integral_conj]
    simp_rw [← h]
    exact integral_neg_eq_self G volume
  exact Complex.conj_eq_iff_im.mp h1

/-- The integral over `ℝ` of an integrand with `G (-y) = conj (G y)` is the real number
`(∫ G).re`. -/
theorem integral_eq_ofReal_re_of_conj {G : ℝ → ℂ} (h : ∀ y, G (-y) = (starRingEnd ℂ) (G y)) :
    ∫ y, G y = (((∫ y, G y).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [integral_im_eq_zero_of_conj h])

/-! ### Two explicit derivatives -/

/-- `∂^m (s - z)⁻¹ = m! / (s - z)^{m+1}` away from `s`. -/
theorem iteratedDeriv_inv_sub (m : ℕ) {s ζ : ℂ} (h : ζ ≠ s) :
    iteratedDeriv m (fun z : ℂ => (s - z)⁻¹) ζ = (m.factorial : ℂ) * ((s - ζ) ^ (m + 1))⁻¹ := by
  induction m generalizing ζ with
  | zero => simp
  | succ m ih =>
    have hev : iteratedDeriv m (fun z : ℂ => (s - z)⁻¹) =ᶠ[𝓝 ζ]
        fun z => (m.factorial : ℂ) * ((s - z) ^ (m + 1))⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds h] with z hz using ih hz
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hne : s - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hd : HasDerivAt (fun z => (s - z) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * (s - ζ) ^ (m + 1 - 1) * (-1)) ζ :=
      ((hasDerivAt_id ζ).const_sub s).pow (m + 1)
    have hd2 := (hd.inv (pow_ne_zero _ hne)).const_mul (m.factorial : ℂ)
    refine hd2.deriv.trans ?_
    rw [Nat.factorial_succ]
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- `∂^{m+1} (-log (1 - ζ))` at `ζ = 0` is `m!`. -/
theorem iteratedDeriv_neg_log_one_sub (m : ℕ) :
    iteratedDeriv (m + 1) (fun ζ : ℂ => -Complex.log (1 - ζ)) 0 = (m.factorial : ℂ) := by
  have hev : deriv (fun ζ : ℂ => -Complex.log (1 - ζ)) =ᶠ[𝓝 0] fun z => (1 - z)⁻¹ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos : (0 : ℂ) ∈ ball (0 : ℂ) 1)]
      with z hz
    have hz' : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
    have hslit : 1 - z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      have hlt : z.re < 1 :=
        (le_abs_self _).trans_lt ((Complex.abs_re_le_norm z).trans_lt hz')
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have := (((hasDerivAt_id z).const_sub 1).clog hslit).neg
    refine this.deriv.trans ?_
    simp [neg_div]
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq,
    iteratedDeriv_inv_sub m (by norm_num : (0 : ℂ) ≠ 1)]
  simp

end PGM
