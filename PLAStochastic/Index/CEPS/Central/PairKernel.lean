import PLAStochastic.Index.CEPS.Central.Identification
import PLAStochastic.Index.CEPS.Central.NewtonBranch
import PLAStochastic.ForMathlib.Analysis.Complex.MixedPartialDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetTimeOperator
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv

/-! # The exact-root central time-operator pair kernel

The descended bridge and entrance give a complete time-operator pair that is jointly
analytic in `(q, λ, z, b)` at the merged reference origin. At every non-merger point of a
reference ball, its scale Taylor coefficients of order at most `N` coincide with those of the
finite Newton complete pair; the frequency derivative is transferred by commuting the genuine
partial derivatives with the scale coefficients. -/

noncomputable section
open Complex Set Filter Topology Asymptotics PowerSeries
namespace PGM

variable {d N : ℕ} {η : (Fin d → ℂ) × ℂ → ℂ} {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ}

/-- The exact-root central complete time-operator pair in `(q, λ, z, b)`. -/
def cepsCentralPairKernel (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) (x : CepsCentralBase d) : ℂ :=
  exp ((x.2.2.2 * x.2.2.1) * (1 + x.2.2.2 * x.2.1)) *
    cepsCentralDescended d N η Θ (cepsCentralEntrance d N) x ^ 2 *
      (-(1 / (1 + x.2.2.2 * x.2.1)) *
          deriv (fun w => cepsCentralDescended d N η Θ (cepsCentralBridge d N)
            (x.1, x.2.1, w, x.2.2.2)) x.2.2.1 -
        x.2.2.2 * cepsCentralDescended d N η Θ (cepsCentralBridge d N) x)

/-- Frequency derivatives of jointly analytic central germs are jointly analytic. -/
theorem analyticAt_central_frequency_deriv {G : CepsCentralBase d → ℂ} {x₁ : CepsCentralBase d}
    (hG : AnalyticAt ℂ G x₁) :
    AnalyticAt ℂ (fun x : CepsCentralBase d =>
      deriv (fun w => G (x.1, x.2.1, w, x.2.2.2)) x.2.2.1) x₁ := by
  let A := ((Fin d → ℂ) × ℂ × ℂ) × ℂ
  have hm : AnalyticAt ℂ (fun v : A => ((v.1.1, v.1.2.1, v.2, v.1.2.2) : CepsCentralBase d))
      ((x₁.1, x₁.2.1, x₁.2.2.2), x₁.2.2.1) := by
    have h1 : AnalyticAt ℂ (fun v : A => v.1.1) ((x₁.1, x₁.2.1, x₁.2.2.2), x₁.2.2.1) :=
      analyticAt_fst.comp analyticAt_fst
    have h2 : AnalyticAt ℂ (fun v : A => v.1.2.1) ((x₁.1, x₁.2.1, x₁.2.2.2), x₁.2.2.1) :=
      analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
    have h3 : AnalyticAt ℂ (fun v : A => v.2) ((x₁.1, x₁.2.1, x₁.2.2.2), x₁.2.2.1) :=
      analyticAt_snd
    have h4 : AnalyticAt ℂ (fun v : A => v.1.2.2) ((x₁.1, x₁.2.1, x₁.2.2.2), x₁.2.2.1) :=
      analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
    exact h1.prod (h2.prod (h3.prod h4))
  have hΦ := hG.comp_of_eq hm rfl
  simp only [Function.comp_def] at hΦ
  have hd := hΦ.deriv_snd
  have hn : AnalyticAt ℂ (fun x : CepsCentralBase d => ((x.1, x.2.1, x.2.2.2), x.2.2.1)) x₁ := by
    have h1 : AnalyticAt ℂ (fun x : CepsCentralBase d => x.1) x₁ := analyticAt_fst
    have h2 : AnalyticAt ℂ (fun x : CepsCentralBase d => x.2.1) x₁ :=
      analyticAt_fst.comp analyticAt_snd
    have h3 : AnalyticAt ℂ (fun x : CepsCentralBase d => x.2.2.2) x₁ :=
      analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
    have h4 : AnalyticAt ℂ (fun x : CepsCentralBase d => x.2.2.1) x₁ :=
      analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
    exact (h1.prod (h2.prod h3)).prod h4
  have h := hd.comp_of_eq hn rfl
  simp only [Function.comp_def] at h
  exact h

theorem cepsCentralPairKernel_analyticAt {x₁ : CepsCentralBase d}
    (hE : AnalyticAt ℂ (cepsCentralDescended d N η Θ (cepsCentralEntrance d N)) x₁)
    (hB : AnalyticAt ℂ (cepsCentralDescended d N η Θ (cepsCentralBridge d N)) x₁)
    (hw : 1 + x₁.2.2.2 * x₁.2.1 ≠ 0) :
    AnalyticAt ℂ (cepsCentralPairKernel d N η Θ) x₁ := by
  have hl : AnalyticAt ℂ (fun x : CepsCentralBase d => x.2.1) x₁ :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun x : CepsCentralBase d => x.2.2.1) x₁ :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have hb : AnalyticAt ℂ (fun x : CepsCentralBase d => x.2.2.2) x₁ :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  have hW : AnalyticAt ℂ (fun x : CepsCentralBase d => 1 + x.2.2.2 * x.2.1) x₁ :=
    (analyticAt_const (v := (1 : ℂ))).add (hb.mul hl)
  have hD := analyticAt_central_frequency_deriv hB
  have hS : AnalyticAt ℂ (fun x : CepsCentralBase d => -(1 / (1 + x.2.2.2 * x.2.1))) x₁ :=
    ((analyticAt_const (v := (1 : ℂ))).div hW hw).neg
  exact ((((hb.mul hz).mul hW).cexp).mul (hE.pow 2)).mul ((hS.mul hD).sub (hb.mul hB))

/-! ## Node-symmetric kernels along the analytic Newton branch -/

/-- A node kernel along the two Newton iterations of the analytic branch, in `(b, w)`. -/
def cepsCentralBranchKernel (d N : ℕ) (F : CepsCentralBase d → ℂ → ℂ → ℂ)
    (q : Fin d → ℂ) (lam z : ℂ) (v : ℂ × ℂ) : ℂ :=
  F (q, lam, v.2, v.1)
    (cepsCentralNewton d N q lam v.2
      (cepsCentralBranchRoot (cepsComplexJetPad d q (cepsJetCode (.inl 0))) lam z v.2) N v.1)
    (cepsCentralNewton d N q lam v.2
      (-2 * lam / cepsComplexJetPad d q (cepsJetCode (.inl 0)) -
        cepsCentralBranchRoot (cepsComplexJetPad d q (cepsJetCode (.inl 0))) lam z v.2) N v.1)

theorem cepsCentralBranchKernel_analyticAt {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    {q : Fin d → ℂ} (lam : ℝ) (z : ℂ)
    (hV : cepsComplexJetPad d q (cepsJetCode (.inl 0)) ≠ 0)
    (hm : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    (hF : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => F X.1 X.2.1 X.2.2)
      ((q, (lam : ℂ), z, 0), cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1,
        cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1))) :
    AnalyticAt ℂ (cepsCentralBranchKernel d N F q lam z) (0, z) := by
  set V := cepsComplexJetPad d q (cepsJetCode (.inl 0)) with hVdef
  let ρ : ℂ → ℂ := cepsCentralBranchRoot V lam z
  have hρ : AnalyticAt ℂ (fun v : ℂ × ℂ => ρ v.2) (0, z) :=
    (cepsCentralBranchRoot_analyticAt V lam z).comp_of_eq analyticAt_snd rfl
  have hρ' : AnalyticAt ℂ (fun v : ℂ × ℂ => -2 * (lam : ℂ) / V - ρ v.2) (0, z) :=
    analyticAt_const.sub hρ
  have hgap : (lam : ℂ) + V * ρ z ≠ 0 := cepsCentralBranchRoot_gap_ne hV hm
  have hgap' : (lam : ℂ) + V * (-2 * (lam : ℂ) / V - ρ z) ≠ 0 := by
    have e : (lam : ℂ) + V * (-2 * (lam : ℂ) / V - ρ z) = -((lam : ℂ) + V * ρ z) := by
      field_simp
      ring
    rw [e]
    exact neg_ne_zero.mpr hgap
  have hN₁ := cepsCentralNewton_analyticAt (N := N) (e₀ := ((0 : ℂ), z))
    (q := fun _ : ℂ × ℂ => q) (lam := fun _ => (lam : ℂ)) (w := fun v => v.2)
    (β := fun v => ρ v.2) (b := fun v => v.1) analyticAt_const analyticAt_const analyticAt_snd
    hρ analyticAt_fst hgap N
  have hN₂ := cepsCentralNewton_analyticAt (N := N) (e₀ := ((0 : ℂ), z))
    (q := fun _ : ℂ × ℂ => q) (lam := fun _ => (lam : ℂ)) (w := fun v => v.2)
    (β := fun v => -2 * (lam : ℂ) / V - ρ v.2) (b := fun v => v.1) analyticAt_const
    analyticAt_const analyticAt_snd hρ' analyticAt_fst hgap' N
  have hbase : AnalyticAt ℂ (fun v : ℂ × ℂ => ((q, (lam : ℂ), v.2, v.1) : CepsCentralBase d))
      (0, z) :=
    analyticAt_const.prod (analyticAt_const.prod (analyticAt_snd.prod analyticAt_fst))
  have hroot : ρ z ^ 2 * (V / 2) + (lam : ℂ) * ρ z = z := cepsCentralBranchRoot_root hV hm z
  have hroot' : (-2 * (lam : ℂ) / V - ρ z) ^ 2 * (V / 2) + lam * (-2 * (lam : ℂ) / V - ρ z) =
      z := by
    have e : (-2 * (lam : ℂ) / V - ρ z) ^ 2 * (V / 2) + lam * (-2 * (lam : ℂ) / V - ρ z) =
        ρ z ^ 2 * (V / 2) + lam * ρ z := by
      field_simp
      ring
    rw [e]
    exact hroot
  have hs₁ : ρ z = cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1 :=
    cepsCentralBranchRoot_self q lam z
  have hs₂ : -2 * (lam : ℂ) / V - ρ z = cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1) :=
    cepsCentralBranchRoot_partner_self q lam z
  have hval : (fun v : ℂ × ℂ => (((q, (lam : ℂ), v.2, v.1) : CepsCentralBase d),
      cepsCentralNewton d N q lam v.2 (ρ v.2) N v.1,
      cepsCentralNewton d N q lam v.2 (-2 * (lam : ℂ) / V - ρ v.2) N v.1)) (0, z) =
      ((q, (lam : ℂ), z, 0), cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1,
        cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1)) := by
    simp only [cepsCentralNewton_zero_of_root hroot, cepsCentralNewton_zero_of_root hroot']
    rw [hs₂, hs₁]
  have h := hF.comp_of_eq (hbase.prod (hN₁.prod hN₂)) hval
  simp only [Function.comp_def] at h
  exact h

theorem cepsCentralBranchKernel_eq {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hsym : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁) (q : Fin d → ℂ) (lam : ℝ) {z : ℂ}
    (hm : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    (w b : ℂ) :
    F (q, lam, w, b) (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w 1 N b)
        (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w (-1) N b) =
      cepsCentralBranchKernel d N F q lam z (b, w) :=
  cepsCentral_rootModel_symm_eq_branch hsym q lam hm w b

theorem cepsCentralBranchKernel_coeff_eventually {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hsym : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁)
    {q : Fin d → ℂ} (hq : CepsCentralMorseData d N η Θ q) (lam : ℝ) (z : ℂ)
    (hm : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    (hF : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => F X.1 X.2.1 X.2.2)
      ((q, (lam : ℂ), z, 0), cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1,
        cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1))) :
    ∀ᶠ w in 𝓝 z, ∀ j ≤ N,
      coeff j (complexTaylorSeries (fun b => cepsCentralBranchKernel d N F q lam z (b, w)) 0) =
        coeff j (complexTaylorSeries
          (fun b => cepsCentralDescended d N η Θ F (q, (lam : ℂ), w, b)) 0) := by
  set V := cepsComplexJetPad d q (cepsJetCode (.inl 0)) with hVdef
  have hV : V ≠ 0 := hq.hV
  let ρ : ℂ → ℂ := cepsCentralBranchRoot V lam z
  have hρc : ContinuousAt ρ z := (cepsCentralBranchRoot_analyticAt V lam z).continuousAt
  have hgapev : ∀ᶠ w in 𝓝 z, (lam : ℂ) + V * ρ w ≠ 0 :=
    (continuousAt_const.add (continuousAt_const.mul hρc)).eventually_ne
      (cepsCentralBranchRoot_gap_ne hV hm)
  have hcurve : ContinuousAt (fun w : ℂ => (((q, (lam : ℂ), w, 0) : CepsCentralBase d), ρ w,
      -2 * (lam : ℂ) / V - ρ w)) z := by
    have h0 : ContinuousAt (fun w : ℂ => ((q, (lam : ℂ), w, 0) : CepsCentralBase d)) z := by
      fun_prop
    exact h0.prodMk (hρc.prodMk (continuousAt_const.sub hρc))
  have hs₁ : ρ z = cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1 :=
    cepsCentralBranchRoot_self q lam z
  have hs₂ : -2 * (lam : ℂ) / V - ρ z = cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1) :=
    cepsCentralBranchRoot_partner_self q lam z
  have hval : ((((q, (lam : ℂ), z, 0) : CepsCentralBase d), ρ z,
      -2 * (lam : ℂ) / V - ρ z) : CepsCentralBase d × ℂ × ℂ) =
      ((q, (lam : ℂ), z, 0), cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1,
        cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1)) := by
    rw [hs₂, hs₁]
  have ht := hcurve.tendsto
  rw [hval] at ht
  filter_upwards [hgapev, ht.eventually hF.eventually_analyticAt] with w hgap hFw
  exact cepsCentralNewton_coeff_eq_descended hsym hq (cepsCentralBranchRoot_root hV hm w) hgap hFw

/-! ## Scale coefficients of the complete pair -/

theorem exists_open_differentiableOn_of_analyticAt {f : ℂ × ℂ → ℂ} {x : ℂ × ℂ}
    (hf : AnalyticAt ℂ f x) : ∃ U : Set (ℂ × ℂ), IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ f U := by
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp hf.eventually_analyticAt
  exact ⟨U, hUo, hxU, fun y hy => (hU hy).differentiableAt.differentiableWithinAt⟩

/-- Frequency derivatives preserve agreement of scale coefficients on a frequency
neighborhood. -/
theorem complexTaylorSeries_coeff_deriv_snd_eq {F G : ℂ × ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F (0, z)) (hG : AnalyticAt ℂ G (0, z)) (n : ℕ)
    (he : ∀ᶠ w in 𝓝 z, coeff n (complexTaylorSeries (fun b => F (b, w)) 0) =
      coeff n (complexTaylorSeries (fun b => G (b, w)) 0)) :
    coeff n (complexTaylorSeries (fun b => deriv (fun w => F (b, w)) z) 0) =
      coeff n (complexTaylorSeries (fun b => deriv (fun w => G (b, w)) z) 0) := by
  obtain ⟨U, hU, hxU, hFU⟩ := exists_open_differentiableOn_of_analyticAt hF
  obtain ⟨U', hU', hxU', hGU⟩ := exists_open_differentiableOn_of_analyticAt hG
  rw [← deriv_complexTaylorSeries_coeff_snd hU hFU n hxU,
    ← deriv_complexTaylorSeries_coeff_snd hU' hGU n hxU', Filter.EventuallyEq.deriv_eq he]

theorem analyticAt_deriv_snd_slice {F : ℂ × ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F (0, z)) :
    AnalyticAt ℂ (fun b => deriv (fun w => F (b, w)) z) 0 := by
  have hd := hF.deriv_snd
  have h := hd.comp_of_eq (x := (0 : ℂ)) (f := fun b : ℂ => (b, z))
    (analyticAt_id.prod analyticAt_const) rfl
  simp only [Function.comp_def] at h
  exact h

theorem analyticAt_slice_fst {F : ℂ × ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F (0, z)) :
    AnalyticAt ℂ (fun b => F (b, z)) 0 := by
  have h := hF.comp_of_eq (x := (0 : ℂ)) (f := fun b : ℂ => (b, z))
    (analyticAt_id.prod analyticAt_const) rfl
  simp only [Function.comp_def] at h
  exact h

set_option maxHeartbeats 1600000 in
/-- At a non-merger point the finite Newton complete pair and the exact-root central pair
have the same scale Taylor coefficients up to order `N`. -/
theorem cepsCentralPairKernel_coeff_eq {q : Fin d → ℂ} (hq : CepsCentralMorseData d N η Θ q)
    (lam : ℝ) (z : ℂ)
    (hm : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    (hFB : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralBridge d N X.1 X.2.1 X.2.2)
      ((q, (lam : ℂ), z, 0), cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1,
        cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1)))
    (hFE : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralEntrance d N X.1 X.2.1 X.2.2)
      ((q, (lam : ℂ), z, 0), cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1,
        cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1)))
    (hDB : AnalyticAt ℂ (cepsCentralDescended d N η Θ (cepsCentralBridge d N))
      (q, (lam : ℂ), z, 0))
    (hDE : AnalyticAt ℂ (cepsCentralDescended d N η Θ (cepsCentralEntrance d N))
      (q, (lam : ℂ), z, 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries
        (fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b) 0) =
      coeff j (complexTaylorSeries (fun b => cepsCentralPairKernel d N η Θ (q, (lam : ℂ), z, b)) 0) := by
  have hV : cepsComplexJetPad d q (cepsJetCode (.inl 0)) ≠ 0 := hq.hV
  let KB := cepsCentralBranchKernel d N (cepsCentralBridge d N) q lam z
  let KE := cepsCentralBranchKernel d N (cepsCentralEntrance d N) q lam z
  let GB : ℂ × ℂ → ℂ := fun v => cepsCentralDescended d N η Θ (cepsCentralBridge d N)
    (q, (lam : ℂ), v.2, v.1)
  let GE : ℂ × ℂ → ℂ := fun v => cepsCentralDescended d N η Θ (cepsCentralEntrance d N)
    (q, (lam : ℂ), v.2, v.1)
  have hKB : AnalyticAt ℂ KB (0, z) := cepsCentralBranchKernel_analyticAt lam z hV hm hFB
  have hKE : AnalyticAt ℂ KE (0, z) := cepsCentralBranchKernel_analyticAt lam z hV hm hFE
  have hcurve : AnalyticAt ℂ (fun v : ℂ × ℂ => ((q, (lam : ℂ), v.2, v.1) : CepsCentralBase d))
      (0, z) :=
    analyticAt_const.prod (analyticAt_const.prod (analyticAt_snd.prod analyticAt_fst))
  have hGB : AnalyticAt ℂ GB (0, z) := by
    have h := hDB.comp_of_eq hcurve rfl
    simp only [Function.comp_def] at h
    exact h
  have hGE : AnalyticAt ℂ GE (0, z) := by
    have h := hDE.comp_of_eq hcurve rfl
    simp only [Function.comp_def] at h
    exact h
  have hEB : ∀ w b, cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam w b =
      KB (b, w) := by
    intro w b
    rw [cepsComplexKernelBridgeJetModel_eq_central]
    exact cepsCentralBranchKernel_eq (fun x a₁ a₂ => cepsCentralBridge_swap x a₁ a₂) q lam hm w b
  have hEE : ∀ w b, cepsComplexKernelEntranceJetModel (cepsComplexJetPad d q) N lam w b =
      KE (b, w) := by
    intro w b
    rw [cepsComplexKernelEntranceJetModel_eq_central]
    exact cepsCentralBranchKernel_eq (fun x a₁ a₂ => cepsCentralEntrance_swap x a₁ a₂) q lam hm w b
  have hcB := cepsCentralBranchKernel_coeff_eventually
    (fun x a₁ a₂ => cepsCentralBridge_swap x a₁ a₂) hq lam z hm hFB
  have hcE := cepsCentralBranchKernel_coeff_eventually
    (fun x a₁ a₂ => cepsCentralEntrance_swap x a₁ a₂) hq lam z hm hFE
  -- the six scale curves
  have hAN : (fun b => cepsComplexKernelEntranceJetModel (cepsComplexJetPad d q) N lam z b) =
      fun b => KE (b, z) := funext fun b => hEE z b
  have hUN : (fun b => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam z b) =
      fun b => KB (b, z) := funext fun b => hEB z b
  have hVN : (fun b => deriv (fun w => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q)
      N lam w b) z) = fun b => deriv (fun w => KB (b, w)) z := by
    funext b
    congr 1
    funext w
    exact hEB w b
  have heA : ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => KE (b, z)) 0) =
      coeff j (complexTaylorSeries (fun b => GE (b, z)) 0) := hcE.self_of_nhds
  have heU : ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => KB (b, z)) 0) =
      coeff j (complexTaylorSeries (fun b => GB (b, z)) 0) := hcB.self_of_nhds
  have heV : ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => deriv (fun w => KB (b, w)) z) 0) =
      coeff j (complexTaylorSeries (fun b => deriv (fun w => GB (b, w)) z) 0) := by
    intro j hj
    apply complexTaylorSeries_coeff_deriv_snd_eq hKB hGB j
    filter_upwards [hcB] with w hw
    exact hw j hj
  have h := complexTaylorSeries_coeff_eq_completePair (analyticAt_slice_fst hKE)
    (analyticAt_slice_fst hGE) (analyticAt_slice_fst hKB) (analyticAt_slice_fst hGB)
    (analyticAt_deriv_snd_slice hKB) (analyticAt_deriv_snd_slice hGB) N lam z heA heU heV
  intro j hj
  have hj' := h j hj
  have hL : (fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b) =
      fun b => exp ((b * z) * (1 + b * lam)) * KE (b, z) ^ 2 *
        (-(1 / (1 + b * lam)) * deriv (fun w => KB (b, w)) z - b * KB (b, z)) := by
    funext b
    rw [cepsComplexKernelPairJetModel, congrFun hAN b, congrFun hUN b, congrFun hVN b]
  rw [hL]
  exact hj'

/-! ## The central pair kernel -/

theorem tendsto_cepsCentral_baseRoot (p₀ : Fin d → ℂ)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) (sgn : ℂ) :
    Tendsto (fun x : CepsCentralBase d =>
      -x.2.1 / cepsComplexJetPad d x.1 (cepsJetCode (.inl 0)) +
        sgn * Complex.sqrt (2 / cepsComplexJetPad d x.1 (cepsJetCode (.inl 0))) *
          Complex.sqrt (x.2.2.1 + x.2.1 ^ 2 / (2 * cepsComplexJetPad d x.1 (cepsJetCode (.inl 0)))))
      (𝓝 (p₀, 0, 0, 0)) (𝓝 0) := by
  let V : CepsCentralBase d → ℂ := fun x => cepsComplexJetPad d x.1 (cepsJetCode (.inl 0))
  have hVc : Continuous V := (cepsComplexJetPad_continuous d _).comp continuous_fst
  have hl : Continuous (fun x : CepsCentralBase d => x.2.1) := continuous_fst.comp continuous_snd
  have hz : Continuous (fun x : CepsCentralBase d => x.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have h1 : Tendsto (fun x : CepsCentralBase d => -x.2.1 / V x) (𝓝 (p₀, 0, 0, 0)) (𝓝 0) := by
    have hc : ContinuousAt (fun x : CepsCentralBase d => -x.2.1 / V x) (p₀, 0, 0, 0) :=
      hl.neg.continuousAt.div hVc.continuousAt hV
    simpa using hc.tendsto
  have hm : Tendsto (fun x : CepsCentralBase d => x.2.2.1 + x.2.1 ^ 2 / (2 * V x))
      (𝓝 (p₀, 0, 0, 0)) (𝓝 0) := by
    have hc : ContinuousAt (fun x : CepsCentralBase d => x.2.2.1 + x.2.1 ^ 2 / (2 * V x))
        (p₀, 0, 0, 0) :=
      hz.continuousAt.add ((hl.pow 2).continuousAt.div
        (continuousAt_const.mul hVc.continuousAt) (mul_ne_zero two_ne_zero hV))
    simpa using hc.tendsto
  have hr : Tendsto (fun x : CepsCentralBase d => ‖2 / V x‖) (𝓝 (p₀, 0, 0, 0))
      (𝓝 ‖2 / V (p₀, 0, 0, 0)‖) :=
    ((continuousAt_const.div hVc.continuousAt hV).norm).tendsto
  have h2 : Tendsto (fun x : CepsCentralBase d => sgn * Complex.sqrt (2 / V x) *
      Complex.sqrt (x.2.2.1 + x.2.1 ^ 2 / (2 * V x))) (𝓝 (p₀, 0, 0, 0)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have he : (fun x : CepsCentralBase d => ‖sgn * Complex.sqrt (2 / V x) *
        Complex.sqrt (x.2.2.1 + x.2.1 ^ 2 / (2 * V x))‖) = fun x =>
        ‖sgn‖ * Real.sqrt ‖2 / V x‖ * Real.sqrt ‖x.2.2.1 + x.2.1 ^ 2 / (2 * V x)‖ := by
      funext x
      rw [norm_mul, norm_mul, norm_sqrt, norm_sqrt]
    rw [he]
    have hA : Tendsto (fun x : CepsCentralBase d => ‖sgn‖ * Real.sqrt ‖2 / V x‖)
        (𝓝 (p₀, 0, 0, 0)) (𝓝 (‖sgn‖ * Real.sqrt ‖2 / V (p₀, 0, 0, 0)‖)) :=
      tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto _).comp hr)
    have hB : Tendsto (fun x : CepsCentralBase d => Real.sqrt ‖x.2.2.1 + x.2.1 ^ 2 / (2 * V x)‖)
        (𝓝 (p₀, 0, 0, 0)) (𝓝 0) := by
      have h0 : Tendsto (fun x : CepsCentralBase d => ‖x.2.2.1 + x.2.1 ^ 2 / (2 * V x)‖)
          (𝓝 (p₀, 0, 0, 0)) (𝓝 0) := by
        simpa using hm.norm
      have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
      simpa [Function.comp_def] using h1
    simpa using hA.mul hB
  simpa using h1.add h2

/-- The exact-root central kernel for an arbitrary complex reference input with nonzero
variance. -/
theorem cepsCentralPairKernel_exists_of_ne (d N : ℕ) (p₀ : Fin d → ℂ)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : (Fin d → ℂ) × ℂ × ℂ × ℂ → ℂ,
      AnalyticAt ℂ H (p₀, 0, 0, 0) ∧
      ∀ (q : Fin d → ℂ) (lam : ℝ) (z : ℂ),
        (q, (lam : ℂ), z, (0 : ℂ)) ∈ Metric.ball (p₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) ρ →
        z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0 →
        ∀ n ≤ N, iteratedDeriv n
            (fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b) 0 =
          iteratedDeriv n (fun b => H (q, (lam : ℂ), z, b)) 0 := by
  obtain ⟨η, Θ, hdata⟩ := exists_cepsCentralMorseData d N p₀ hV
  have hFB := cepsCentralBridge_analyticAt_origin (N := N) p₀ hV
  have hFE := cepsCentralEntrance_analyticAt_origin (N := N) p₀ hV
  have hDB := cepsCentralDescended_analyticAt (N := N) hdata.hη hdata.hΘ hFB
    (fun x a₁ a₂ => cepsCentralBridge_swap x a₁ a₂)
  have hDE := cepsCentralDescended_analyticAt (N := N) hdata.hη hdata.hΘ hFE
    (fun x a₁ a₂ => cepsCentralEntrance_swap x a₁ a₂)
  let β : ℂ → CepsCentralBase d → ℂ := fun sgn x =>
    -x.2.1 / cepsComplexJetPad d x.1 (cepsJetCode (.inl 0)) +
      sgn * Complex.sqrt (2 / cepsComplexJetPad d x.1 (cepsJetCode (.inl 0))) *
        Complex.sqrt (x.2.2.1 + x.2.1 ^ 2 / (2 * cepsComplexJetPad d x.1 (cepsJetCode (.inl 0))))
  have hslice : Continuous (fun x : CepsCentralBase d =>
      ((x.1, x.2.1, x.2.2.1, 0) : CepsCentralBase d)) := by fun_prop
  have hT : Tendsto (fun x : CepsCentralBase d =>
      (((x.1, x.2.1, x.2.2.1, 0) : CepsCentralBase d), β 1 x, β (-1) x))
      (𝓝 (p₀, 0, 0, 0)) (𝓝 ((p₀, 0, 0, 0), 0, 0)) :=
    (hslice.tendsto (p₀, 0, 0, 0)).prodMk_nhds ((tendsto_cepsCentral_baseRoot p₀ hV 1).prodMk_nhds
      (tendsto_cepsCentral_baseRoot p₀ hV (-1)))
  have hT₂ := hslice.tendsto (p₀, 0, 0, 0)
  have hM : ∀ᶠ x in 𝓝 ((p₀, 0, 0, 0) : CepsCentralBase d), CepsCentralMorseData d N η Θ x.1 :=
    (continuous_fst.tendsto ((p₀, 0, 0, 0) : CepsCentralBase d)).eventually hdata.eventually
  have hgood := hM.and ((hT.eventually hFB.eventually_analyticAt).and
    ((hT.eventually hFE.eventually_analyticAt).and ((hT₂.eventually hDB.eventually_analyticAt).and
      (hT₂.eventually hDE.eventually_analyticAt))))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hgood
  refine ⟨ε, hε, cepsCentralPairKernel d N η Θ,
    cepsCentralPairKernel_analyticAt hDE hDB (by simp), ?_⟩
  intro q lam z hmem hm n hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := hball hmem
  have hc := cepsCentralPairKernel_coeff_eq h1 lam z hm h2 h3 h4 h5 n hn
  simp only [complexTaylorSeries, coeff_mk] at hc
  exact mul_left_cancel₀ (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))) hc

/-- **Central exact-root kernel.** For a real reference vector of positive variance there is
an exact-root central complete time-operator pair kernel, jointly analytic at the merged
origin, whose scale Taylor coefficients up to order `N` equal those of the finite Newton
complete pair at every non-merger point of a reference ball. -/
theorem cepsCentralPairKernel_exists (d N : ℕ) (p₀ : Fin d → ℝ)
    (hV : 0 < (cepsComplexJetPad d (fun i => (p₀ i : ℂ)) (cepsJetCode (.inl 0))).re) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : (Fin d → ℂ) × ℂ × ℂ × ℂ → ℂ,
      AnalyticAt ℂ H ((fun i => (p₀ i : ℂ)), 0, 0, 0) ∧
      ∀ (q : Fin d → ℂ) (lam : ℝ) (z : ℂ),
        (q, (lam : ℂ), z, (0 : ℂ)) ∈
            Metric.ball ((fun i => (p₀ i : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)) ρ →
        z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0 →
        ∀ n ≤ N, iteratedDeriv n
            (fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b) 0 =
          iteratedDeriv n (fun b => H (q, (lam : ℂ), z, b)) 0 := by
  have hne : cepsComplexJetPad d (fun i => (p₀ i : ℂ)) (cepsJetCode (.inl 0)) ≠ 0 := by
    intro h
    rw [h, zero_re] at hV
    exact lt_irrefl 0 hV
  exact cepsCentralPairKernel_exists_of_ne d N _ hne

end PGM
