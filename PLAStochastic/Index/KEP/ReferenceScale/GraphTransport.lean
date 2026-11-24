import PLAStochastic.Index.KEP.ReferenceScale.TailDerivative

/-!
# Material transport on a graph with two exterior tails

The graph is the actual pair of compact killed-tail integrals. Either tail may
have zero length. The logarithmic-slope weak derivative retains both outward
fluxes. `KepTailDynamics` bundles proved one-step identities, not a regularity
or graph-derivative assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

structure KepTailDynamics (σ : ℝ) where
  step : ℝ → ℝ → ℝ
  spatial : ℝ → ℝ → ℝ
  slope : ℝ → ℝ → ℝ
  continuous_step : Continuous (Function.uncurry step)
  continuous_spatial : Continuous (Function.uncurry spatial)
  continuous_slope : Continuous (Function.uncurry slope)
  spatial_derivative : ∀ s t, HasDerivAt (step s) (spatial s t) t
  slope_derivative : ∀ s t, HasDerivAt (fun r => step r t) (slope s t) s
  ward : ∀ s t, slope s t = -step s t + (σ - t) * spatial s t

def kepLogTailDynamics {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t, HasDerivAt f (f' t) t) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    KepTailDynamics σ where
  step := kepLogStep f σ
  spatial := kepLogStepFirst f' σ
  slope := kepLogStepSlope f f' σ
  continuous_step := continuous_kepLogStep hf σ
  continuous_spatial := continuous_kepLogStepFirst hf' σ
  continuous_slope := continuous_kepLogStepSlope hf hf' σ
  spatial_derivative := hasDerivAt_kepLogStep_right hd σ
  slope_derivative := hasDerivAt_kepLogStep_slope hd σ
  ward := kepLogStepSlope_eq hσ

def kepReferenceTailDynamics {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : KepTailDynamics σ :=
  kepLogTailDynamics
    (continuous_iff_continuousAt.mpr fun t =>
      ((kepReferenceDensity_classical heps hj).2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t =>
      ((kepReferenceDensity_classical heps hj).2.2.1 t).continuousAt)
    (kepReferenceDensity_classical heps hj).2.1
    (by rcases hσ with rfl | rfl <;> norm_num)

theorem continuous_kepTailFluxTest
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {p : ℝ → ℝ → ℝ} (hp : Continuous (Function.uncurry p))
    {τ : X → ℝ} (hτ : Continuous τ) {Φ : X → ℝ → ℝ}
    (hΦ : Continuous (Function.uncurry Φ)) (w σ : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun t => kepTailFluxTest p w σ (τ t) n x (Φ t)) := by
  cases n with
  | zero => exact continuous_const
  | succ n =>
    have hB : Continuous (fun t : X × ℝ => kepBridgeTransportFlux p w σ
        (τ t.1) n x t.2) :=
      (continuous_kepBridgeTransportFlux hp w σ n).comp
        ((hτ.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have hK (y : ℝ) : Continuous (fun t : X => kepFixedBridge p w (τ t) n x y) :=
      (continuous_kepFixedBridge hp w n).comp
        (hτ.prodMk (continuous_const.prodMk continuous_const))
    have hφ (y : ℝ) : Continuous (fun t : X => Φ t y) :=
      hΦ.comp (continuous_id.prodMk continuous_const)
    exact (((continuous_integral_Ioc_of_continuous (hB.mul hΦ) 0 w).neg.sub
      (((hK w).const_mul _).mul (hφ w))).add
        (((hK 0).const_mul _).mul (hφ 0)))

def kepTailPairTest (pA pB : ℝ → ℝ → ℝ) (w s : ℝ) (i r : ℕ) (xA xB : ℝ)
    (Φ : ℝ → ℝ → ℝ) : ℝ :=
  kepTailTest pA w s i xA (fun u => kepTailTest pB w s r xB (Φ u))

def kepTailPairFlux (pA pB : ℝ → ℝ → ℝ) (w σA σB s : ℝ)
    (i r : ℕ) (xA xB : ℝ) (Φ : ℝ → ℝ → ℝ) : ℝ :=
  kepTailFluxTest pA w σA s i xA (fun u => kepTailTest pB w s r xB (Φ u)) +
    kepTailTest pA w s i xA (fun u => kepTailFluxTest pB w σB s r xB (Φ u))

theorem continuous_kepTailPairTest {pA pB : ℝ → ℝ → ℝ}
    (hA : Continuous (Function.uncurry pA)) (hB : Continuous (Function.uncurry pB))
    {Φ : ℝ → ℝ → ℝ → ℝ}
    (hΦ : Continuous (fun t : ℝ × ℝ × ℝ => Φ t.1 t.2.1 t.2.2))
    (w : ℝ) (i r : ℕ) (xA xB : ℝ) :
    Continuous (fun s => kepTailPairTest pA pB w s i r xA xB (Φ s)) := by
  exact continuous_kepTailTest hA continuous_id
    (Φ := fun s u => kepTailTest pB w s r xB (Φ s u))
    (continuous_kepTailTest hB continuous_fst (Φ := fun t v => Φ t.1 t.2 v)
      (hΦ.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.prodMk continuous_snd))) w r xB) w i xA

theorem continuous_kepTailPairFlux {pA pB : ℝ → ℝ → ℝ}
    (hA : Continuous (Function.uncurry pA)) (hB : Continuous (Function.uncurry pB))
    {Φ : ℝ → ℝ → ℝ → ℝ}
    (hΦ : Continuous (fun t : ℝ × ℝ × ℝ => Φ t.1 t.2.1 t.2.2))
    (w σA σB : ℝ) (i r : ℕ) (xA xB : ℝ) :
    Continuous (fun s => kepTailPairFlux pA pB w σA σB s i r xA xB (Φ s)) := by
  have hΦ' := hΦ.comp (continuous_fst.fst.prodMk
    (continuous_fst.snd.prodMk continuous_snd))
  exact (continuous_kepTailFluxTest hA continuous_id
    (Φ := fun s u => kepTailTest pB w s r xB (Φ s u))
    (continuous_kepTailTest hB continuous_fst (Φ := fun t v => Φ t.1 t.2 v)
      hΦ' w r xB) w σA i xA).add
    (continuous_kepTailTest hA continuous_id
      (Φ := fun s u => kepTailFluxTest pB w σB s r xB (Φ s u))
      (continuous_kepTailFluxTest hB continuous_fst (Φ := fun t v => Φ t.1 t.2 v)
        hΦ' w σB r xB) w i xA)

set_option backward.isDefEq.respectTransparency.types false in
/-- The derivative of a genuine two-tail graph. Both tail fluxes are retained,
including zero-step suffixes when either tail is pinned at its final step. -/
theorem hasDerivAt_kepTailPairTest_transport {σA σB : ℝ}
    (A : KepTailDynamics σA) (B : KepTailDynamics σB)
    {Φ Φs Φu Φv : ℝ → ℝ → ℝ → ℝ}
    (hΦ : Continuous (fun t : ℝ × ℝ × ℝ => Φ t.1 t.2.1 t.2.2))
    (hΦs : Continuous (fun t : ℝ × ℝ × ℝ => Φs t.1 t.2.1 t.2.2))
    (hΦu : Continuous (fun t : ℝ × ℝ × ℝ => Φu t.1 t.2.1 t.2.2))
    (hΦv : Continuous (fun t : ℝ × ℝ × ℝ => Φv t.1 t.2.1 t.2.2))
    (hds : ∀ s u v, HasDerivAt (fun t => Φ t u v) (Φs s u v) s)
    (hdu : ∀ s u v, HasDerivAt (fun t => Φ s t v) (Φu s u v) u)
    (hdv : ∀ s u v, HasDerivAt (Φ s u) (Φv s u v) v)
    {w : ℝ} (hw : 0 ≤ w) (s : ℝ) (i r : ℕ) (xA xB : ℝ) :
    HasDerivAt (fun t => kepTailPairTest A.step B.step w t i r xA xB (Φ t))
      (kepTailPairTest A.step B.step w s i r xA xB
        (fun u v => Φs s u v + (u - xA - (i : ℝ) * σA) * Φu s u v +
          (v - xB - (r : ℝ) * σB) * Φv s u v) +
        kepTailPairFlux A.step B.step w σA σB s i r xA xB (Φ s)) s := by
  let Ψ : ℝ → ℝ → ℝ := fun t u => kepTailTest B.step w t r xB (Φ t u)
  let Ψs : ℝ → ℝ → ℝ := fun t u => kepTailTest B.step w t r xB
    (fun v => Φs t u v + (v - xB - (r : ℝ) * σB) * Φv t u v) +
      kepTailFluxTest B.step w σB t r xB (Φ t u)
  let Ψu : ℝ → ℝ → ℝ := fun t u => kepTailTest B.step w t r xB (Φu t u)
  have hΨ : Continuous (Function.uncurry Ψ) :=
    continuous_kepTailTest B.continuous_step continuous_fst (Φ := fun t v => Φ t.1 t.2 v)
      (hΦ.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.prodMk continuous_snd))) w r xB
  have hΨs : Continuous (Function.uncurry Ψs) := by
    apply Continuous.add
    · apply continuous_kepTailTest B.continuous_step continuous_fst
      exact (hΦs.add (((continuous_snd.snd.sub continuous_const).sub
        continuous_const).mul hΦv)).comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
    · exact continuous_kepTailFluxTest B.continuous_step continuous_fst
        (Φ := fun t v => Φ t.1 t.2 v)
        (hΦ.comp (continuous_fst.fst.prodMk
          (continuous_fst.snd.prodMk continuous_snd))) w σB r xB
  have hΨu : Continuous (Function.uncurry Ψu) :=
    continuous_kepTailTest B.continuous_step continuous_fst (Φ := fun t v => Φu t.1 t.2 v)
      (hΦu.comp (continuous_fst.fst.prodMk
        (continuous_fst.snd.prodMk continuous_snd))) w r xB
  have hΨds (t u : ℝ) : HasDerivAt (fun z => Ψ z u) (Ψs t u) t := by
    apply hasDerivAt_kepTailTest_transport B.continuous_step B.continuous_spatial
      B.continuous_slope B.spatial_derivative B.slope_derivative B.ward
      (Φ := fun z v => Φ z u v) (Φs := fun z v => Φs z u v) (Φy := fun z v => Φv z u v)
      (hΦ.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      (hΦs.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      (hΦv.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      (fun z v => hds z u v) (fun z v => hdv z u v) hw t r xB
  have hΨdu (t u : ℝ) : HasDerivAt (Ψ t) (Ψu t u) u := by
    exact hasDerivAt_kepTailTest_parameter B.continuous_step
      (Φ := fun z v => Φ t z v) (Φ' := fun z v => Φu t z v)
      (hΦ.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd)))
      (hΦu.comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd)))
      (fun z v => hdu t z v) w t r xB u
  have hh := hasDerivAt_kepTailTest_transport A.continuous_step A.continuous_spatial
    A.continuous_slope A.spatial_derivative A.slope_derivative A.ward
    hΨ hΨs hΨu hΨds hΨdu hw s i xA
  let H : ℝ → ℝ → ℝ := fun u v => Φs s u v +
    (u - xA - (i : ℝ) * σA) * Φu s u v + (v - xB - (r : ℝ) * σB) * Φv s u v
  have hH : Continuous (Function.uncurry H) := by
    exact ((hΦs.comp (continuous_const.prodMk continuous_id)).add
      (((continuous_fst.sub continuous_const).sub continuous_const).mul
        (hΦu.comp (continuous_const.prodMk continuous_id)))).add
      (((continuous_snd.sub continuous_const).sub continuous_const).mul
        (hΦv.comp (continuous_const.prodMk continuous_id)))
  have hlinear (u : ℝ) : Ψs s u + (u - xA - (i : ℝ) * σA) * Ψu s u =
      kepTailTest B.step w s r xB (H u) + kepTailFluxTest B.step w σB s r xB (Φ s u) := by
    have h1 : Continuous (fun v => Φs s u v +
        (v - xB - (r : ℝ) * σB) * Φv s u v) := by
      have hs : Continuous (Φs s u) :=
        hΦs.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      have hv : Continuous (Φv s u) :=
        hΦv.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      fun_prop
    have h2 : Continuous (fun v => (u - xA - (i : ℝ) * σA) * Φu s u v) := by
      have hu : Continuous (Φu s u) :=
        hΦu.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      fun_prop
    have he : kepTailTest B.step w s r xB (H u) =
        kepTailTest B.step w s r xB (fun v => Φs s u v +
          (v - xB - (r : ℝ) * σB) * Φv s u v) +
            (u - xA - (i : ℝ) * σA) * Ψu s u := by
      calc
        _ = kepTailTest B.step w s r xB
            ((fun v => Φs s u v + (v - xB - (r : ℝ) * σB) * Φv s u v) +
              (fun v => (u - xA - (i : ℝ) * σA) * Φu s u v)) := by
          apply kepTailTest_congr
          intro v
          dsimp [H]
          ring
        _ = _ := by
          rw [kepTailTest_add B.continuous_step w s r xB h1 h2,
            kepTailTest_const_mul]
    dsimp only [Ψs]
    rw [he]
    ring
  have he := kepTailTest_congr A.step w s i xA hlinear
  rw [he] at hh
  have hinner : Continuous (fun u => kepTailTest B.step w s r xB (H u)) :=
    continuous_kepTailTest B.continuous_step continuous_const hH w r xB
  have hflux : Continuous (fun u => kepTailFluxTest B.step w σB s r xB (Φ s u)) :=
    continuous_kepTailFluxTest B.continuous_step continuous_const (Φ := fun u v => Φ s u v)
      (hΦ.comp (continuous_const.prodMk continuous_id)) w σB r xB
  have hadd := kepTailTest_add A.continuous_step w s i xA hinner hflux
  change (kepTailTest A.step w s i xA fun u =>
    kepTailTest B.step w s r xB (H u) + kepTailFluxTest B.step w σB s r xB (Φ s u)) = _ at hadd
  rw [hadd] at hh
  convert hh using 1 <;> first | rfl | (dsimp [kepTailPairTest, kepTailPairFlux, Ψ, H]; ring)

end

end PGM
