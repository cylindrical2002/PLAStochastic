import PLAStochastic.Swing.DenseSampling.Segments.ShrinkingConeSlope
import PLAStochastic.Swing.DenseSampling.Segments.SlopeBoundaryBounds

/-!
# Boundary nonextension forces native durations to vanish

A continuous infeasible cone has a witness consisting of two positive sample
times. These witnesses persist under perturbations of the fitted anchor and
of the recording time and under dense sampling. Thus no compactness assumption
on a sequence of selected slopes is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- One-dimensional interval feasibility has a two-constraint obstruction,
even when the lower or upper ratios are unbounded near zero. -/
theorem exists_crossed_continuous_constraints {f : ℝ → ℝ} {q ε T : ℝ}
    (hT : 0 < T) (hzero : |f 0 - q| ≤ ε)
    (hno : ¬ ∃ a, continuousSlopeFeasible f q ε T a) :
    ∃ t u : Ioc (0 : ℝ) T,
      (f u - q + ε) / (u : ℝ) < (f t - q - ε) / (t : ℝ) := by
  by_contra h
  push Not at h
  let L := range (fun t : Ioc (0 : ℝ) T => (f t - q - ε) / (t : ℝ))
  have hne : L.Nonempty := ⟨_, ⟨⟨T, hT, le_rfl⟩, rfl⟩⟩
  have hb : BddAbove L := by
    refine ⟨(f T - q + ε) / T, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact h t ⟨T, hT, le_rfl⟩
  apply hno
  refine ⟨sSup L, fun t => ?_⟩
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, mul_zero, sub_zero] using hzero
  have hp : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  have hl : (f t - q - ε) / (t : ℝ) ≤ sSup L :=
    le_csSup hb ⟨⟨t, hp, t.property.2⟩, rfl⟩
  have hu : sSup L ≤ (f t - q + ε) / (t : ℝ) := by
    apply csSup_le hne
    rintro _ ⟨u, rfl⟩
    exact h u ⟨t, hp, t.property.2⟩
  have hl' := (div_le_iff₀ hp).mp hl
  have hu' := (le_div_iff₀ hp).mp hu
  apply abs_le.mpr
  constructor <;> linarith

/-- The absolute grid point just below a fixed nonnegative time converges to it. -/
theorem tendsto_mesh_floor_time {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun i => (⌊t / h i⌋₊ : ℝ) * h i) l (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun i => t - h i) l (𝓝 t) by simpa using tendsto_const_nhds.sub hconv)
    tendsto_const_nhds
  · intro i
    have := meshFloor_gap_lt (T := t) (hh i)
    linarith
  · intro i
    exact meshFloor_mul_le ht (hh i)

/-- If the limit anchor admits no positive future fit, every feasible sampled
interval whose start and anchor converge there must have its finish converge
to the same time. This applies also to the EOF interval. -/
theorem tendsto_feasible_grid_finish_of_no_extension (f : C(ℝ, ℝ))
    {σ q₀ ε : ℝ} (hσ : 0 ≤ σ) (hzero : |f σ - q₀| ≤ ε)
    (hno : ∀ T : ℝ, 0 < T → ¬ ∃ a,
      continuousSlopeFeasible (fun t => f (σ + t)) q₀ ε T a)
    {ι : Type*} {l : Filter ι} {h q : ι → ℝ} {s e : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hstart : Tendsto (fun i => (s i : ℝ) * h i) l (𝓝 σ))
    (hanchor : Tendsto q l (𝓝 q₀))
    (hse : ∀ᶠ i in l, s i ≤ e i)
    (hfit : ∀ᶠ i in l, nativePrefixFeasible (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (s i) (e i) (q i)) :
    Tendsto (fun i => (e i : ℝ) * h i) l (𝓝 σ) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [hstart.eventually_const_lt hb, hse] with i hi he
    exact hi.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast he) (hh i).le)
  · intro b hb
    let T := b - σ
    have hT : 0 < T := sub_pos.mpr hb
    obtain ⟨t, u, hcross⟩ := exists_crossed_continuous_constraints hT
      (show |f (σ + 0) - q₀| ≤ ε by simpa using hzero) (hno T hT)
    let kt : ι → ℕ := fun i => ⌊(σ + t) / h i⌋₊
    let ku : ι → ℕ := fun i => ⌊(σ + u) / h i⌋₊
    have htt := tendsto_mesh_floor_time hh hconv (show 0 ≤ σ + (t : ℝ) by linarith [t.property.1])
    have hut := tendsto_mesh_floor_time hh hconv (show 0 ≤ σ + (u : ℝ) by linarith [u.property.1])
    have htd : Tendsto (fun i => (kt i : ℝ) * h i - (s i : ℝ) * h i) l (𝓝 (t : ℝ)) := by
      simpa only [kt, add_sub_cancel_left] using htt.sub hstart
    have hud : Tendsto (fun i => (ku i : ℝ) * h i - (s i : ℝ) * h i) l (𝓝 (u : ℝ)) := by
      simpa only [ku, add_sub_cancel_left] using hut.sub hstart
    have hlow := ((((f.continuous.tendsto (σ + t)).comp htt).sub hanchor).sub_const ε).div
      htd t.property.1.ne'
    have hupp := ((((f.continuous.tendsto (σ + u)).comp hut).sub hanchor).add_const ε).div
      hud u.property.1.ne'
    filter_upwards [hfit, htd.eventually_const_lt t.property.1,
      hud.eventually_const_lt u.property.1, (hupp.prodMk_nhds hlow).eventually
        (isOpen_lt continuous_fst continuous_snd |>.mem_nhds hcross)] with i hi htpos hupos hgap
    by_contra hei
    have heb : b ≤ (e i : ℝ) * h i := le_of_not_gt hei
    have hhi := hh i
    have hkt : s i + 1 ≤ kt i := by
      have hh' : (s i : ℝ) < kt i := by nlinarith
      exact_mod_cast hh'
    have hku : s i + 1 ≤ ku i := by
      have hh' : (s i : ℝ) < ku i := by nlinarith
      exact_mod_cast hh'
    have hkte : kt i ≤ e i := by
      have hb' := meshFloor_mul_le (show 0 ≤ σ + (t : ℝ) by linarith [t.property.1]) (hh i)
      have ht' := t.property.2
      have hh' : (kt i : ℝ) ≤ e i := by dsimp only [kt, T] at *; nlinarith
      exact_mod_cast hh'
    have hkue : ku i ≤ e i := by
      have hb' := meshFloor_mul_le (show 0 ≤ σ + (u : ℝ) by linarith [u.property.1]) (hh i)
      have hu' := u.property.2
      have hh' : (ku i : ℝ) ≤ e i := by dsimp only [ku, T] at *; nlinarith
      exact_mod_cast hh'
    obtain ⟨m, hm⟩ := hi
    have htf := abs_le.mp (hm (kt i) (Finset.mem_Icc.mpr ⟨hkt, hkte⟩))
    have huf := abs_le.mp (hm (ku i) (Finset.mem_Icc.mpr ⟨hku, hkue⟩))
    have hl : (f ((kt i : ℝ) * h i) - q i - ε) /
        ((kt i : ℝ) * h i - (s i : ℝ) * h i) ≤ m := by
      apply (div_le_iff₀ htpos).mpr
      dsimp only at htf
      linarith
    have hu : m ≤ (f ((ku i : ℝ) * h i) - q i + ε) /
        ((ku i : ℝ) * h i - (s i : ℝ) * h i) := by
      apply (le_div_iff₀ hupos).mpr
      dsimp only at huf
      linarith
    exact (lt_of_lt_of_le hgap hl).not_ge hu

/-- The duration itself tends to zero, without an additional endpoint premise. -/
theorem tendsto_feasible_grid_duration_of_no_extension (f : C(ℝ, ℝ))
    {σ q₀ ε : ℝ} (hσ : 0 ≤ σ) (hzero : |f σ - q₀| ≤ ε)
    (hno : ∀ T : ℝ, 0 < T → ¬ ∃ a,
      continuousSlopeFeasible (fun t => f (σ + t)) q₀ ε T a)
    {ι : Type*} {l : Filter ι} {h q : ι → ℝ} {s e : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hstart : Tendsto (fun i => (s i : ℝ) * h i) l (𝓝 σ))
    (hanchor : Tendsto q l (𝓝 q₀)) (hse : ∀ᶠ i in l, s i ≤ e i)
    (hfit : ∀ᶠ i in l, nativePrefixFeasible (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (s i) (e i) (q i)) :
    Tendsto (fun i => (e i : ℝ) * h i - (s i : ℝ) * h i) l (𝓝 0) := by
  simpa only [sub_self] using (tendsto_feasible_grid_finish_of_no_extension f hσ hzero hno
    hh hconv hstart hanchor hse hfit).sub hstart

/-- The proved strong Markov oscillation excludes every boundary anchor after
the actual lifetime, in the real continuous-path convention used by native grids. -/
theorem brownian_boundary_no_extension_real_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ q : ℝ,
      |processPath B ω (anchoredProcessLifetime B ε ω).toReal - q| = ε →
      ∀ T : ℝ, 0 < T → ¬ ∃ a,
        continuousSlopeFeasible
          (fun t => processPath B ω ((anchoredProcessLifetime B ε ω).toReal + t)) q ε T a := by
  filter_upwards [hB.cont, anchoredProcessLifetime_tolerance_ae_ne_top hB hε,
    brownian_boundary_anchor_no_fit_after_lifetime_ae hB hε] with ω hc hf hosc
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (anchoredProcessLifetime B ε ω).untopD 0 = σ := by rw [← hσ]; rfl
  have hr : (anchoredProcessLifetime B ε ω).toReal = (σ : ℝ) := by rw [← hσ]; rfl
  intro q hq T hT
  rintro ⟨a, ha⟩
  obtain ⟨hp, hn⟩ := hosc a ⟨T, hT.le⟩ hT
  rw [hr, processPath_apply_of_continuous hc] at hq
  rcases eq_or_eq_neg_of_abs_eq hq with hq | hq
  · obtain ⟨t, ht, htT, hbad⟩ := hn
    have hgood := ha ⟨t, t.property, htT.le⟩
    change |processPath B ω ((anchoredProcessLifetime B ε ω).toReal + (t : ℝ)) - q -
      a * (t : ℝ)| ≤ ε at hgood
    rw [hr, ← NNReal.coe_add, processPath_apply_of_continuous hc] at hgood
    rw [hu] at hbad
    have hq' : q = B σ ω - ε := by linarith
    rw [hq'] at hgood
    exact hbad.not_ge hgood
  · obtain ⟨t, ht, htT, hbad⟩ := hp
    have hgood := ha ⟨t, t.property, htT.le⟩
    change |processPath B ω ((anchoredProcessLifetime B ε ω).toReal + (t : ℝ)) - q -
      a * (t : ℝ)| ≤ ε at hgood
    rw [hr, ← NNReal.coe_add, processPath_apply_of_continuous hc] at hgood
    rw [hu] at hbad
    have hq' : q = B σ ω + ε := by linarith
    rw [hq'] at hgood
    exact hbad.not_ge hgood

end SwingRepair
