import PLAStochastic.Brownian.Killed.Semigroup

/-! # Joint width, time and spatial continuity of the actual Dirichlet heat series -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A summable majorant on any compact positive-width range and positive-time half-line. -/
def heatWidthBound (l u δ : ℝ) (a b n : ℕ) : ℝ :=
  (2/l*(Real.pi/l)^(a+b))*
    (((n : ℝ)+1)^(a+b)*Real.exp (-((n : ℝ)+1)*(heatScale u*δ)))

theorem summable_heatWidthBound {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ)
    (l : ℝ) (a b : ℕ) : Summable (heatWidthBound l u δ a b) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul (a+b) (mul_pos (heatScale_pos hu) hδ))
  convert! h.mul_left (2/l*(Real.pi/l)^(a+b)) using 1
  funext n
  simp only [heatWidthBound, Nat.cast_add, Nat.cast_one, neg_mul, mul_comm]
  congr 3
  ring

theorem heatSpatialMode_width_bound {l u r δ t : ℝ}
    (hl : 0 < l) (hlr : l ≤ r) (hru : r ≤ u) (hδ : 0 ≤ δ) (ht : δ ≤ t)
    (a b n : ℕ) (x z : ℝ) :
    ‖heatSpatialMode r a b n t x z‖ ≤ heatWidthBound l u δ a b n := by
  have hr : 0 < r := hl.trans_le hlr
  have hu : 0 < u := hr.trans_le hru
  apply (heatSpatialMode_bound hr hδ ht a b n x z).trans
  have hA : 2/r*(Real.pi/r)^(a+b) ≤ 2/l*(Real.pi/l)^(a+b) := by gcongr
  have hs : heatScale u ≤ heatScale r := by unfold heatScale; gcongr
  have hn : 0 ≤ (n : ℝ)+1 := by positivity
  have hexp : Real.exp (-((n : ℝ)+1)*(heatScale r*δ)) ≤
      Real.exp (-((n : ℝ)+1)*(heatScale u*δ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs hδ) hn]
  unfold heatSpatialBound heatWidthBound
  exact mul_le_mul hA (mul_le_mul_of_nonneg_left hexp (pow_nonneg hn _))
    (mul_nonneg (pow_nonneg hn _) (Real.exp_nonneg _)) (by positivity)

/-- Width/time region; spatial positions are unrestricted. -/
def heatWidthRegion (l u δ : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc l u ∧ δ ≤ p.2.1}

theorem tendstoUniformlyOn_heatSpatialSeries_width {l u δ : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hδ : 0 < δ) (a b : ℕ) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℝ × ℝ × ℝ) => ∑ n ∈ Finset.range N,
        heatSpatialMode p.1 a b n p.2.1 p.2.2.1 p.2.2.2)
      (fun p => heatSpatialSeries p.1 a b p.2.1 p.2.2.1 p.2.2.2)
      atTop (heatWidthRegion l u δ) :=
  tendstoUniformlyOn_tsum_nat (summable_heatWidthBound (hl.trans_le hlu) hδ l a b)
    (fun n p hp => heatSpatialMode_width_bound hl hp.1.1 hp.1.2 hδ.le hp.2 a b n p.2.2.1 p.2.2.2)

/-- Joint continuity on every region with width and time bounded away from zero. -/
theorem continuousOn_heatSpatialSeries_width {l u δ : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hδ : 0 < δ) (a b : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ × ℝ =>
      heatSpatialSeries p.1 a b p.2.1 p.2.2.1 p.2.2.2) (heatWidthRegion l u δ) := by
  apply continuousOn_tsum _ (summable_heatWidthBound (hl.trans_le hlu) hδ l a b)
    (fun n p hp => heatSpatialMode_width_bound hl hp.1.1 hp.1.2 hδ.le hp.2 a b n p.2.2.1 p.2.2.2)
  intro n p hp
  have hr : p.1 ≠ 0 := (hl.trans_le hp.1.1).ne'
  dsimp only [heatSpatialMode, heatFrequency]
  fun_prop

/-- All space derivatives depend jointly continuously on width, time and both positions. -/
theorem continuousAt_heatSpatialSeries_joint {p : ℝ × ℝ × ℝ × ℝ}
    (hr : 0 < p.1) (ht : 0 < p.2.1) (a b : ℕ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ =>
      heatSpatialSeries q.1 a b q.2.1 q.2.2.1 q.2.2.2) p := by
  apply (continuousOn_heatSpatialSeries_width (show 0 < p.1/2 by positivity)
    (show p.1/2 ≤ 2*p.1 by linarith) (show 0 < p.2.1/2 by positivity) a b).continuousAt
  have hw : ∀ᶠ q : ℝ × ℝ × ℝ × ℝ in 𝓝 p, q.1 ∈ Icc (p.1/2) (2*p.1) :=
    continuous_fst.continuousAt.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have htime : ∀ᶠ q : ℝ × ℝ × ℝ × ℝ in 𝓝 p, p.2.1/2 ≤ q.2.1 :=
    (continuous_fst.comp continuous_snd).continuousAt.eventually (Ici_mem_nhds (by change p.2.1/2 < p.2.1; linarith))
  exact hw.and htime

/-- A convenient compositional interface retaining simultaneous width and endpoint changes. -/
theorem tendsto_heatSpatialSeries_joint {ι : Type*} {l : Filter ι}
    {r t x z : ι → ℝ} {r₀ t₀ x₀ z₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (ht : Tendsto t l (𝓝 t₀))
    (hx : Tendsto x l (𝓝 x₀)) (hz : Tendsto z l (𝓝 z₀))
    (hr₀ : 0 < r₀) (ht₀ : 0 < t₀) (a b : ℕ) :
    Tendsto (fun i => heatSpatialSeries (r i) a b (t i) (x i) (z i)) l
      (𝓝 (heatSpatialSeries r₀ a b t₀ x₀ z₀)) :=
  (continuousAt_heatSpatialSeries_joint (p := (r₀,t₀,x₀,z₀)) hr₀ ht₀ a b).tendsto.comp
    (hr.prodMk_nhds (ht.prodMk_nhds (hx.prodMk_nhds hz)))

end BrownianAffine
