import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Complex.Basic

/-!
# A quantitative holomorphic inverse with a holomorphic parameter

Let `P ⊆ ℂ` be open, `R > 0`, `a ≠ 0`, and let `f : ℂ → ℂ → ℂ` be jointly holomorphic on
`P × B(0, R)` with `f p 0 = 0` and `‖∂_z f(p, z) - a‖ ≤ ‖a‖/2` on `P × B(0, R)`
(`ParamInvHyp P f a R`). Then for every `p ∈ P`:

* `f p` is injective on `B(0, R)` with `‖z₁ - z₂‖ ≤ (2/‖a‖) ‖f p z₁ - f p z₂‖`
  (`ParamInvHyp.norm_sub_le`);
* every `w` with `‖w‖ < ‖a‖ R / 2` has a (unique) preimage `paramInv f R p w ∈ B(0, R)`, of norm at
  most `2‖w‖/‖a‖` (`ParamInvHyp.apply_paramInv`, `ParamInvHyp.paramInv_eq`,
  `ParamInvHyp.norm_paramInv_le`); existence is the contraction mapping principle for
  `z ↦ z - a⁻¹ (f p z - w)`;
* `(p, w) ↦ paramInv f R p w` is jointly holomorphic on `P × B(0, ‖a‖R/2)`
  (`ParamInvHyp.differentiableOn_paramInv`), and `∂_w paramInv = (∂_z f)⁻¹`
  (`ParamInvHyp.hasDerivAt_paramInv`).

All radii are explicit, so the statement is uniform over any family of maps satisfying the
hypotheses with the same `(a, R)`.
-/

noncomputable section

open Set Metric Filter Topology

namespace PGM

/-- Hypotheses of the quantitative parametric holomorphic inverse. -/
structure ParamInvHyp (P : Set ℂ) (f : ℂ → ℂ → ℂ) (a : ℂ) (R : ℝ) : Prop where
  isOpen : IsOpen P
  pos : 0 < R
  ne : a ≠ 0
  diff : DifferentiableOn ℂ (fun x : ℂ × ℂ => f x.1 x.2) (P ×ˢ ball 0 R)
  zero : ∀ p ∈ P, f p 0 = 0
  deriv_le : ∀ p ∈ P, ∀ z ∈ ball (0 : ℂ) R, ‖deriv (f p) z - a‖ ≤ ‖a‖ / 2

open Classical in
/-- The inverse of `f p` on `B(0, R)` (junk value `0` when there is no preimage). -/
@[irreducible] def paramInv (f : ℂ → ℂ → ℂ) (R : ℝ) (p w : ℂ) : ℂ :=
  if h : ∃ z ∈ ball (0 : ℂ) R, f p z = w then h.choose else 0

namespace ParamInvHyp

variable {P : Set ℂ} {f : ℂ → ℂ → ℂ} {a : ℂ} {R : ℝ}

theorem norm_a_pos (h : ParamInvHyp P f a R) : 0 < ‖a‖ := norm_pos_iff.mpr h.ne

theorem differentiableAt_uncurry (h : ParamInvHyp P f a R) {p z : ℂ} (hp : p ∈ P)
    (hz : z ∈ ball (0 : ℂ) R) : DifferentiableAt ℂ (fun x : ℂ × ℂ => f x.1 x.2) (p, z) :=
  (h.diff (p, z) ⟨hp, hz⟩).differentiableAt
    ((h.isOpen.prod isOpen_ball).mem_nhds ⟨hp, hz⟩)

theorem differentiableAt (h : ParamInvHyp P f a R) {p z : ℂ} (hp : p ∈ P)
    (hz : z ∈ ball (0 : ℂ) R) : DifferentiableAt ℂ (f p) z := by
  have h1 := h.differentiableAt_uncurry hp hz
  have h2 : DifferentiableAt ℂ (fun z : ℂ => ((p, z) : ℂ × ℂ)) z :=
    (differentiableAt_const p).prodMk differentiableAt_id
  exact h1.comp z h2

/-- `z ↦ f p z - a z` is `(‖a‖/2)`-Lipschitz on `B(0, R)`. -/
theorem norm_sub_sub_le (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ ball (0 : ℂ) R) (h₂ : z₂ ∈ ball (0 : ℂ) R) :
    ‖(f p z₁ - a * z₁) - (f p z₂ - a * z₂)‖ ≤ ‖a‖ / 2 * ‖z₁ - z₂‖ := by
  have hd : ∀ z ∈ ball (0 : ℂ) R, DifferentiableAt ℂ (fun z => f p z - a * z) z := fun z hz =>
    (h.differentiableAt hp hz).sub ((differentiableAt_id).const_mul a)
  have hb : ∀ z ∈ ball (0 : ℂ) R, ‖deriv (fun z => f p z - a * z) z‖ ≤ ‖a‖ / 2 := by
    intro z hz
    have hd2 : HasDerivAt (fun z => f p z - a * z) (deriv (f p) z - a * 1) z :=
      (h.differentiableAt hp hz).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)
    rw [hd2.deriv, mul_one]; exact h.deriv_le p hp z hz
  exact (convex_ball (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le hd hb h₂ h₁

/-- Lower Lipschitz bound: `‖z₁ - z₂‖ ≤ (2/‖a‖) ‖f p z₁ - f p z₂‖`. -/
theorem norm_sub_le (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ ball (0 : ℂ) R) (h₂ : z₂ ∈ ball (0 : ℂ) R) :
    ‖z₁ - z₂‖ ≤ 2 / ‖a‖ * ‖f p z₁ - f p z₂‖ := by
  have ha := h.norm_a_pos
  have key := h.norm_sub_sub_le hp h₁ h₂
  have e : (f p z₁ - a * z₁) - (f p z₂ - a * z₂) = (f p z₁ - f p z₂) - a * (z₁ - z₂) := by ring
  rw [e] at key
  have h3 : ‖a‖ * ‖z₁ - z₂‖ ≤ ‖f p z₁ - f p z₂‖ + ‖a‖ / 2 * ‖z₁ - z₂‖ := by
    calc ‖a‖ * ‖z₁ - z₂‖ = ‖a * (z₁ - z₂)‖ := (norm_mul _ _).symm
      _ = ‖(f p z₁ - f p z₂) - ((f p z₁ - f p z₂) - a * (z₁ - z₂))‖ := by ring_nf
      _ ≤ ‖f p z₁ - f p z₂‖ + ‖(f p z₁ - f p z₂) - a * (z₁ - z₂)‖ := _root_.norm_sub_le _ _
      _ ≤ ‖f p z₁ - f p z₂‖ + ‖a‖ / 2 * ‖z₁ - z₂‖ := by gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ ha]
  nlinarith [norm_nonneg (z₁ - z₂)]

/-- Upper Lipschitz bound: `‖f p z₁ - f p z₂‖ ≤ (3‖a‖/2) ‖z₁ - z₂‖`. -/
theorem norm_apply_sub_le (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ ball (0 : ℂ) R) (h₂ : z₂ ∈ ball (0 : ℂ) R) :
    ‖f p z₁ - f p z₂‖ ≤ 3 * ‖a‖ / 2 * ‖z₁ - z₂‖ := by
  have key := h.norm_sub_sub_le hp h₁ h₂
  have e : (f p z₁ - a * z₁) - (f p z₂ - a * z₂) = (f p z₁ - f p z₂) - a * (z₁ - z₂) := by ring
  rw [e] at key
  calc ‖f p z₁ - f p z₂‖ = ‖((f p z₁ - f p z₂) - a * (z₁ - z₂)) + a * (z₁ - z₂)‖ := by ring_nf
    _ ≤ ‖(f p z₁ - f p z₂) - a * (z₁ - z₂)‖ + ‖a * (z₁ - z₂)‖ := norm_add_le _ _
    _ ≤ ‖a‖ / 2 * ‖z₁ - z₂‖ + ‖a‖ * ‖z₁ - z₂‖ := by rw [norm_mul]; gcongr
    _ = 3 * ‖a‖ / 2 * ‖z₁ - z₂‖ := by ring

theorem injOn (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) : InjOn (f p) (ball (0 : ℂ) R) := by
  intro z₁ h₁ z₂ h₂ he
  have := h.norm_sub_le hp h₁ h₂
  rw [he, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- Existence of a preimage (contraction mapping). -/
theorem exists_apply_eq (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) : ∃ z, ‖z‖ ≤ 2 * ‖w‖ / ‖a‖ ∧ f p z = w := by
  have ha := h.norm_a_pos
  set r : ℝ := 2 * ‖w‖ / ‖a‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hrR : r < R := by
    rw [hr, div_lt_iff₀ ha]; linarith
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) R := closedBall_subset_ball hrR
  set T : ℂ → ℂ := fun z => z - a⁻¹ * (f p z - w) with hT
  have hTlip : ∀ z₁ ∈ closedBall (0 : ℂ) r, ∀ z₂ ∈ closedBall (0 : ℂ) r,
      ‖T z₁ - T z₂‖ ≤ 1 / 2 * ‖z₁ - z₂‖ := by
    intro z₁ h₁ z₂ h₂
    have key := h.norm_sub_sub_le hp (hsub h₁) (hsub h₂)
    have e : T z₁ - T z₂ = -a⁻¹ * ((f p z₁ - a * z₁) - (f p z₂ - a * z₂)) := by
      simp only [hT]; field_simp [h.ne]; ring
    rw [e, norm_mul, norm_neg, norm_inv]
    calc ‖a‖⁻¹ * ‖(f p z₁ - a * z₁) - (f p z₂ - a * z₂)‖
        ≤ ‖a‖⁻¹ * (‖a‖ / 2 * ‖z₁ - z₂‖) := by gcongr
      _ = 1 / 2 * ‖z₁ - z₂‖ := by field_simp
  have hT0 : T 0 = a⁻¹ * w := by simp [hT, h.zero p hp]
  have hmaps : MapsTo T (closedBall (0 : ℂ) r) (closedBall (0 : ℂ) r) := by
    intro z hz
    have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self hr0
    have h1 := hTlip z hz 0 h0
    rw [mem_closedBall, dist_zero_right] at hz ⊢
    rw [sub_zero] at h1
    calc ‖T z‖ = ‖(T z - T 0) + T 0‖ := by ring_nf
      _ ≤ ‖T z - T 0‖ + ‖T 0‖ := norm_add_le _ _
      _ ≤ 1 / 2 * ‖z‖ + ‖a⁻¹ * w‖ := by
          rw [← hT0]; exact add_le_add h1 le_rfl
      _ ≤ 1 / 2 * r + r / 2 := by
          rw [norm_mul, norm_inv]
          gcongr
          rw [hr]; field_simp; linarith
      _ = r := by ring
  have hlip : LipschitzOnWith (1 / 2 : NNReal) T (closedBall (0 : ℂ) r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    have := hTlip x hx y hy
    simpa using this
  have hcontr : ContractingWith (1 / 2 : NNReal) (hmaps.restrict T _ _) := by
    refine ⟨?_, hlip.mapsToRestrict hmaps⟩
    rw [← NNReal.coe_lt_coe]; norm_num
  obtain ⟨y, hy, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hcontr (mem_closedBall_self hr0) (edist_ne_top _ _)
  refine ⟨y, by simpa using hy, ?_⟩
  have : a⁻¹ * (f p y - w) = 0 := by
    have hfx : T y = y := hfix
    simp only [hT] at hfx
    linear_combination -hfx
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (inv_eq_zero.mp h0) h.ne
  · exact sub_eq_zero.mp h0

theorem exists_mem_ball (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) : ∃ z ∈ ball (0 : ℂ) R, f p z = w := by
  obtain ⟨z, hz, hfz⟩ := h.exists_apply_eq hp hw
  refine ⟨z, ?_, hfz⟩
  rw [mem_ball, dist_zero_right]
  have ha := h.norm_a_pos
  calc ‖z‖ ≤ 2 * ‖w‖ / ‖a‖ := hz
    _ < R := by rw [div_lt_iff₀ ha]; linarith

theorem paramInv_spec (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) :
    paramInv f R p w ∈ ball (0 : ℂ) R ∧ f p (paramInv f R p w) = w := by
  have hex := h.exists_mem_ball hp hw
  unfold paramInv
  rw [dif_pos hex]
  exact hex.choose_spec

theorem paramInv_mem (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) : paramInv f R p w ∈ ball (0 : ℂ) R :=
  (h.paramInv_spec hp hw).1

theorem apply_paramInv (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) : f p (paramInv f R p w) = w :=
  (h.paramInv_spec hp hw).2

/-- Uniqueness: any preimage in `B(0, R)` is `paramInv`. -/
theorem paramInv_eq (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {w : ℂ} (hfz : f p z = w) : paramInv f R p w = z := by
  have hex : ∃ z ∈ ball (0 : ℂ) R, f p z = w := ⟨z, hz, hfz⟩
  have hs := hex.choose_spec
  unfold paramInv
  rw [dif_pos hex]
  exact h.injOn hp hs.1 hz (hs.2.trans hfz.symm)

theorem paramInv_zero (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) : paramInv f R p 0 = 0 :=
  h.paramInv_eq hp (mem_ball_self h.pos) (h.zero p hp)

theorem norm_paramInv_le (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) : ‖paramInv f R p w‖ ≤ 2 * ‖w‖ / ‖a‖ := by
  have hm := h.paramInv_mem hp hw
  have := h.norm_sub_le hp hm (mem_ball_self h.pos)
  rw [h.apply_paramInv hp hw, h.zero p hp, sub_zero, sub_zero] at this
  calc ‖paramInv f R p w‖ ≤ 2 / ‖a‖ * ‖w‖ := this
    _ = 2 * ‖w‖ / ‖a‖ := by ring

/-- `‖paramInv p w - z‖ ≤ (2/‖a‖) ‖w - f p z‖` for `z ∈ B(0, R)`. -/
theorem norm_paramInv_sub_le (h : ParamInvHyp P f a R) {p : ℂ} (hp : p ∈ P) {w z : ℂ}
    (hw : ‖w‖ < ‖a‖ * R / 2) (hz : z ∈ ball (0 : ℂ) R) :
    ‖paramInv f R p w - z‖ ≤ 2 / ‖a‖ * ‖w - f p z‖ := by
  have := h.norm_sub_le hp (h.paramInv_mem hp hw) hz
  rwa [h.apply_paramInv hp hw] at this

/-- The target domain `P × B(0, ‖a‖R/2)`. -/
theorem isOpen_target (h : ParamInvHyp P f a R) :
    IsOpen (P ×ˢ ball (0 : ℂ) (‖a‖ * R / 2)) := h.isOpen.prod isOpen_ball

theorem continuousAt_paramInv (h : ParamInvHyp P f a R) {p₀ w₀ : ℂ} (hp₀ : p₀ ∈ P)
    (hw₀ : ‖w₀‖ < ‖a‖ * R / 2) :
    ContinuousAt (fun y : ℂ × ℂ => paramInv f R y.1 y.2) (p₀, w₀) := by
  set z₀ := paramInv f R p₀ w₀ with hz₀
  have hz₀m : z₀ ∈ ball (0 : ℂ) R := h.paramInv_mem hp₀ hw₀
  have hfz₀ : f p₀ z₀ = w₀ := h.apply_paramInv hp₀ hw₀
  -- continuity of `p ↦ f p z₀` at `p₀`
  have hcont : ContinuousAt (fun p => f p z₀) p₀ := by
    have h1 := (h.differentiableAt_uncurry hp₀ hz₀m).continuousAt
    have h2 : ContinuousAt (fun p : ℂ => ((p, z₀) : ℂ × ℂ)) p₀ :=
      (continuousAt_id).prodMk continuousAt_const
    exact ContinuousAt.comp (x := p₀) (g := fun x : ℂ × ℂ => f x.1 x.2) h1 h2
  have hmem : ∀ᶠ y : ℂ × ℂ in 𝓝 (p₀, w₀), y ∈ P ×ˢ ball (0 : ℂ) (‖a‖ * R / 2) :=
    h.isOpen_target.mem_nhds ⟨hp₀, by simpa [mem_ball, dist_zero_right] using hw₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun y : ℂ × ℂ => 2 / ‖a‖ * (‖y.2 - w₀‖ + ‖f p₀ z₀ - f y.1 z₀‖))
      (𝓝 (p₀, w₀)) (𝓝 0) := by
    have t1 : Tendsto (fun y : ℂ × ℂ => ‖y.2 - w₀‖) (𝓝 (p₀, w₀)) (𝓝 0) := by
      have : Tendsto (fun y : ℂ × ℂ => y.2) (𝓝 (p₀, w₀)) (𝓝 w₀) := continuous_snd.tendsto _
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp this)
    have t2 : Tendsto (fun y : ℂ × ℂ => ‖f p₀ z₀ - f y.1 z₀‖) (𝓝 (p₀, w₀)) (𝓝 0) := by
      have : Tendsto (fun y : ℂ × ℂ => f y.1 z₀) (𝓝 (p₀, w₀)) (𝓝 (f p₀ z₀)) :=
        hcont.tendsto.comp (continuous_fst.tendsto _)
      have := tendsto_iff_norm_sub_tendsto_zero.mp this
      simpa [norm_sub_rev] using this
    simpa using (t1.add t2).const_mul (2 / ‖a‖)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [hmem] with y hy
  have hyw : ‖y.2‖ < ‖a‖ * R / 2 := by simpa [mem_ball, dist_zero_right] using hy.2
  have := h.norm_paramInv_sub_le hy.1 hyw hz₀m
  calc ‖paramInv f R y.1 y.2 - z₀‖ ≤ 2 / ‖a‖ * ‖y.2 - f y.1 z₀‖ := this
    _ ≤ 2 / ‖a‖ * (‖y.2 - w₀‖ + ‖f p₀ z₀ - f y.1 z₀‖) := by
        gcongr
        rw [← hfz₀]
        calc ‖y.2 - f y.1 z₀‖ = ‖(y.2 - f p₀ z₀) + (f p₀ z₀ - f y.1 z₀)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _

/-- Joint holomorphy of the inverse at a point of the target domain. -/
theorem differentiableAt_paramInv (h : ParamInvHyp P f a R) {p₀ w₀ : ℂ} (hp₀ : p₀ ∈ P)
    (hw₀ : ‖w₀‖ < ‖a‖ * R / 2) :
    DifferentiableAt ℂ (fun y : ℂ × ℂ => paramInv f R y.1 y.2) (p₀, w₀) := by
  set z₀ := paramInv f R p₀ w₀ with hz₀
  have hz₀m : z₀ ∈ ball (0 : ℂ) R := h.paramInv_mem hp₀ hw₀
  set F : ℂ × ℂ → ℂ := fun x => f x.1 x.2 with hF
  have hFd : HasFDerivAt F (fderiv ℂ F (p₀, z₀)) (p₀, z₀) :=
    (h.differentiableAt_uncurry hp₀ hz₀m).hasFDerivAt
  set L := fderiv ℂ F (p₀, z₀) with hL
  set A : ℂ := L (0, 1) with hA
  -- `A = ∂_z f (p₀, z₀)`
  have hAderiv : deriv (f p₀) z₀ = A := by
    have h2 : HasDerivAt (fun z : ℂ => ((p₀, z) : ℂ × ℂ)) ((0 : ℂ), (1 : ℂ)) z₀ :=
      (hasDerivAt_const z₀ p₀).prodMk (hasDerivAt_id z₀)
    have h4 : HasDerivAt (f p₀) (L (0, 1)) z₀ := hFd.comp_hasDerivAt z₀ h2
    exact h4.deriv
  have hAne : A ≠ 0 := by
    intro hA0
    have := h.deriv_le p₀ hp₀ z₀ hz₀m
    rw [hAderiv, hA0, zero_sub, norm_neg] at this
    have ha := h.norm_a_pos
    linarith
  -- the map `Φ (p, z) = (p, f p z)` and its derivative
  set Φ : ℂ × ℂ → ℂ × ℂ := fun x => (x.1, F x) with hΦ
  set Φ' : ℂ × ℂ →L[ℂ] ℂ × ℂ := (ContinuousLinearMap.fst ℂ ℂ ℂ).prod L with hΦ'
  set B : ℂ × ℂ →L[ℂ] ℂ := L.comp ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod 0) with hB
  set Ψ' : ℂ × ℂ →L[ℂ] ℂ × ℂ := (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      (A⁻¹ • (ContinuousLinearMap.snd ℂ ℂ ℂ - B)) with hΨ'
  have hLsplit : ∀ x y : ℂ, L (x, y) = L (x, 0) + y * A := by
    intro x y
    have : ((x, y) : ℂ × ℂ) = (x, 0) + y • (0, 1) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hΦ'app : ∀ x y : ℂ, Φ' (x, y) = (x, L (x, y)) := by
    intro x y; simp [hΦ']
  have hΨ'app : ∀ x y : ℂ, Ψ' (x, y) = (x, A⁻¹ * (y - L (x, 0))) := by
    intro x y; simp [hΨ', hB]
  have h1 : ∀ v, Φ' (Ψ' v) = v := by
    rintro ⟨x, y⟩
    rw [hΨ'app, hΦ'app, hLsplit]
    ext
    · rfl
    · simp only; field_simp; ring
  have h2 : ∀ v, Ψ' (Φ' v) = v := by
    rintro ⟨x, y⟩
    rw [hΦ'app, hΨ'app, hLsplit x y]
    ext
    · rfl
    · simp only; field_simp; ring
  set e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := ContinuousLinearEquiv.equivOfInverse Φ' Ψ' h2 h1 with he
  have hΦd : HasFDerivAt Φ (e : ℂ × ℂ →L[ℂ] ℂ × ℂ) (p₀, z₀) := by
    have : HasFDerivAt Φ Φ' (p₀, z₀) :=
      (hasFDerivAt_fst (p := (p₀, z₀))).prodMk hFd
    exact this
  set Ψ : ℂ × ℂ → ℂ × ℂ := fun y => (y.1, paramInv f R y.1 y.2) with hΨ
  have hΨc : ContinuousAt Ψ (p₀, w₀) :=
    (continuousAt_fst).prodMk (h.continuousAt_paramInv hp₀ hw₀)
  have hΨ0 : Ψ (p₀, w₀) = (p₀, z₀) := rfl
  have hmem : ∀ᶠ y : ℂ × ℂ in 𝓝 (p₀, w₀), y ∈ P ×ˢ ball (0 : ℂ) (‖a‖ * R / 2) :=
    h.isOpen_target.mem_nhds ⟨hp₀, by simpa [mem_ball, dist_zero_right] using hw₀⟩
  have hinv : ∀ᶠ y in 𝓝 (p₀, w₀), Φ (Ψ y) = y := by
    filter_upwards [hmem] with y hy
    have hyw : ‖y.2‖ < ‖a‖ * R / 2 := by simpa [mem_ball, dist_zero_right] using hy.2
    simp only [hΦ, hΨ, hF]
    rw [h.apply_paramInv hy.1 hyw]
  rw [← hΨ0] at hΦd
  have hΨd := HasFDerivAt.of_local_left_inverse hΨc hΦd hinv
  have : DifferentiableAt ℂ (Prod.snd ∘ Ψ) (p₀, w₀) :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp (p₀, w₀) hΨd).differentiableAt
  exact this

theorem differentiableOn_paramInv (h : ParamInvHyp P f a R) :
    DifferentiableOn ℂ (fun y : ℂ × ℂ => paramInv f R y.1 y.2)
      (P ×ˢ ball (0 : ℂ) (‖a‖ * R / 2)) := by
  rintro ⟨p, w⟩ ⟨hp, hw⟩
  have hw' : ‖w‖ < ‖a‖ * R / 2 := by simpa [mem_ball, dist_zero_right] using hw
  exact (h.differentiableAt_paramInv hp hw').differentiableWithinAt

/-- `∂_w paramInv = (∂_z f)⁻¹`. -/
theorem hasDerivAt_paramInv (h : ParamInvHyp P f a R) {p w : ℂ} (hp : p ∈ P)
    (hw : ‖w‖ < ‖a‖ * R / 2) :
    HasDerivAt (paramInv f R p) (deriv (f p) (paramInv f R p w))⁻¹ w := by
  have hm := h.paramInv_mem hp hw
  have hd : HasDerivAt (f p) (deriv (f p) (paramInv f R p w)) (paramInv f R p w) :=
    (h.differentiableAt hp hm).hasDerivAt
  have hne : deriv (f p) (paramInv f R p w) ≠ 0 := by
    intro h0
    have := h.deriv_le p hp _ hm
    rw [h0, zero_sub, norm_neg] at this
    have ha := h.norm_a_pos
    linarith
  have hc : ContinuousAt (paramInv f R p) w := by
    have h1 := h.continuousAt_paramInv hp hw
    have h2 : ContinuousAt (fun w : ℂ => ((p, w) : ℂ × ℂ)) w :=
      continuousAt_const.prodMk continuousAt_id
    exact h1.comp h2
  have hball : ∀ᶠ y in 𝓝 w, ‖y‖ < ‖a‖ * R / 2 := by
    have : IsOpen {y : ℂ | ‖y‖ < ‖a‖ * R / 2} := isOpen_lt continuous_norm continuous_const
    exact this.mem_nhds hw
  refine HasDerivAt.of_local_left_inverse hc hd hne ?_
  filter_upwards [hball] with y hy
  exact h.apply_paramInv hp hy

end ParamInvHyp

end PGM
