import PLAStochastic.Index.CEPS.Central.NodeKernel

/-! # Joint analyticity of the central node kernels at the merged origin

At zero scale the spatial unit is the quadratic `V ξ² / 2`, so the quotient is the constant
`V / 2`, the kernel `G` is a nonzero multiple of `exp (-ξ)` and the divided denominator at
the merged nodes is nonzero. Moving divided differences of local germs then give genuine
joint analyticity of the bridge and entrance in all base parameters and both nodes. -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

variable {d N : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cepsCentralBase_coords_analyticAt {e₀ : E} {x : E → CepsCentralBase d}
    (hx : AnalyticAt ℂ x e₀) :
    (∀ i, AnalyticAt ℂ (fun e => cepsComplexJetPad d (x e).1 i) e₀) ∧
      AnalyticAt ℂ (fun e => (x e).2.1) e₀ ∧ AnalyticAt ℂ (fun e => (x e).2.2.1) e₀ ∧
        AnalyticAt ℂ (fun e => (x e).2.2.2) e₀ := by
  have hq : AnalyticAt ℂ (fun e => (x e).1) e₀ := analyticAt_fst.comp hx
  refine ⟨fun i => (cepsComplexJetPad_analyticAt d i _).comp hq,
    analyticAt_fst.comp (analyticAt_snd.comp hx),
    analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp hx)),
    analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp hx))⟩

theorem cepsCentralSpatial_analyticAt {e₀ : E} {x : E → CepsCentralBase d} {ξ : E → ℂ}
    (hx : AnalyticAt ℂ x e₀) (hξ : AnalyticAt ℂ ξ e₀) :
    AnalyticAt ℂ (fun e => cepsCentralSpatial d N (x e) (ξ e)) e₀ := by
  obtain ⟨hpi, hl, hw, hb⟩ := cepsCentralBase_coords_analyticAt hx
  have hP := cepsCgfComplexJetPolynomial_analyticAt hpi (hb.mul hξ) N
  have hT : AnalyticAt ℂ (fun e => ξ e ^ 2 * cepsCgfComplexJetPolynomial
      (cepsComplexJetPad d (x e).1) N ((x e).2.2.2 * ξ e) + (x e).2.1 * ξ e -
        (x e).2.2.1 * (1 + (x e).2.2.2 * (x e).2.1)) e₀ :=
    (((hξ.pow 2).mul hP).add (hl.mul hξ)).sub (hw.mul ((analyticAt_const (v := (1 : ℂ))).add (hb.mul hl)))
  exact (quadraticExpUnit_joint_analyticAt _).comp (x := e₀)
    (f := fun e => ((x e).2.2.2, ξ e ^ 2 * cepsCgfComplexJetPolynomial
      (cepsComplexJetPad d (x e).1) N ((x e).2.2.2 * ξ e) + (x e).2.1 * ξ e -
        (x e).2.2.1 * (1 + (x e).2.2.2 * (x e).2.1))) (hb.prod hT)

theorem cepsCentralG_analyticAt_of {e₀ : E} {x : E → CepsCentralBase d} {a₁ a₂ ξ : E → ℂ}
    (hx : AnalyticAt ℂ x e₀) (hξ : AnalyticAt ℂ ξ e₀)
    (hQ : AnalyticAt ℂ (fun e => cepsCentralQuotient d N (x e) (a₁ e) (a₂ e) (ξ e)) e₀) :
    AnalyticAt ℂ (fun e => cepsCentralG d N (x e) (a₁ e) (a₂ e) (ξ e)) e₀ := by
  obtain ⟨hpi, hl, hw, hb⟩ := cepsCentralBase_coords_analyticAt hx
  have hC := cepsCanonComplexJetPolynomial_analyticAt hpi (hb.mul hl)
    (((hb.pow 2).mul hw).mul ((analyticAt_const (v := (1 : ℂ))).add (hb.mul hl))) (hb.mul hξ) N
  exact ((hξ.neg.mul ((analyticAt_const (v := (1 : ℂ))).add (hb.mul hl))).cexp).mul
    (hQ.mul ((analyticAt_const.mul hC).cexp))

theorem cepsCentralQuotient_analyticAt_zero (x₁ : CepsCentralBase d) :
    AnalyticAt ℂ (fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ =>
      cepsCentralQuotient d N Y.1.1 Y.1.2.1 Y.1.2.2 Y.2) ((x₁, 0, 0), 0) := by
  have h1 : AnalyticAt ℂ (fun v : ((CepsCentralBase d × ℂ × ℂ) × ℂ) × ℂ => v.1.1.1)
      (((x₁, 0, 0), 0), 0) := analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hf : AnalyticAt ℂ (fun v : ((CepsCentralBase d × ℂ × ℂ) × ℂ) × ℂ =>
      cepsCentralSpatial d N v.1.1.1 v.2) (((x₁, 0, 0), 0), 0) :=
    cepsCentralSpatial_analyticAt h1 analyticAt_snd
  have ha : AnalyticAt ℂ (fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ => Y.1.2.1) ((x₁, 0, 0), 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hb : AnalyticAt ℂ (fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ => Y.1.2.2) ((x₁, 0, 0), 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have hc : AnalyticAt ℂ (fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ => Y.2) ((x₁, 0, 0), 0) :=
    analyticAt_snd
  have h := analyticAt_moving_second_dslope_local_zero hf ha hb hc rfl rfl rfl
  exact h

theorem cepsCentralG_analyticAt_zero (x₁ : CepsCentralBase d) :
    AnalyticAt ℂ (fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ =>
      cepsCentralG d N Y.1.1 Y.1.2.1 Y.1.2.2 Y.2) ((x₁, 0, 0), 0) := by
  have h1 : AnalyticAt ℂ (fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ => Y.1.1) ((x₁, 0, 0), 0) :=
    analyticAt_fst.comp analyticAt_fst
  have h := cepsCentralG_analyticAt_of (N := N) (a₁ := fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ => Y.1.2.1)
    (a₂ := fun Y : (CepsCentralBase d × ℂ × ℂ) × ℂ => Y.1.2.2) h1 analyticAt_snd
    (cepsCentralQuotient_analyticAt_zero x₁)
  exact h

theorem cepsCentralDen_analyticAt_zero (x₁ : CepsCentralBase d) :
    AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralDen d N X.1 X.2.1 X.2.2) (x₁, 0, 0) := by
  have ha : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.2.2) (x₁, 0, 0) :=
    analyticAt_snd.comp analyticAt_snd
  have hb : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.2.1) (x₁, 0, 0) :=
    analyticAt_fst.comp analyticAt_snd
  have h := analyticAt_moving_dslope_local_zero (cepsCentralG_analyticAt_zero (N := N) x₁)
    ha hb rfl rfl
  exact h

theorem cepsCentralEntranceSlope_analyticAt_zero (x₁ : CepsCentralBase d)
    (h : x₁.2.2.2 * x₁.2.2.1 = 0) :
    AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralEntranceSlope d N X.1 X.2.1 X.2.2) (x₁, 0, 0) := by
  have hx : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.1) (x₁, 0, 0) := analyticAt_fst
  obtain ⟨-, -, hw, hb⟩ := cepsCentralBase_coords_analyticAt hx
  have ha : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.2.2) (x₁, 0, 0) :=
    analyticAt_snd.comp analyticAt_snd
  have hb' : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.2.1) (x₁, 0, 0) :=
    analyticAt_fst.comp analyticAt_snd
  have hc : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.1.2.2.2 * X.1.2.2.1)
      (x₁, 0, 0) := hb.mul hw
  have h' := analyticAt_moving_second_dslope_local_zero
    (cepsCentralG_analyticAt_zero (N := N) x₁) ha hb' hc rfl rfl h
  exact h'

/-! ## Values at zero scale and the merged origin -/

theorem cepsCentralSpatial_zero_scale (q : Fin d → ℂ) (lam w : ℂ) :
    cepsCentralSpatial d N (q, lam, w, 0) = fun ξ =>
      cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2 * ξ ^ 2 + lam * ξ + -w := by
  funext ξ
  simp only [cepsCentralSpatial, quadraticExpUnit_zero, zero_mul,
    cepsCgfComplexJetPolynomial_zero, add_zero, mul_one]
  ring

theorem cepsCentralQuotient_zero_scale (q : Fin d → ℂ) (lam w a₁ a₂ ξ : ℂ) :
    cepsCentralQuotient d N (q, lam, w, 0) a₁ a₂ ξ =
      cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2 := by
  rw [cepsCentralQuotient, cepsCentralSpatial_zero_scale, cepsNormal_second_dslope_quadratic]

/-- The zero-scale kernel constant `V / 2 · exp (-2 K₀)`. -/
def cepsCentralZeroConstant (d N : ℕ) (q : Fin d → ℂ) : ℂ :=
  cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2 *
    exp (-2 * cepsCanonComplexJetPolynomial (cepsComplexJetPad d q) N 0 0 0)

theorem cepsCentralG_zero_scale (q : Fin d → ℂ) (lam w a₁ a₂ : ℂ) :
    cepsCentralG d N (q, lam, w, 0) a₁ a₂ = fun ξ =>
      exp (-ξ) * cepsCentralZeroConstant d N q := by
  funext ξ
  simp only [cepsCentralG, cepsCentralQuotient_zero_scale, cepsCentralZeroConstant, zero_mul,
    add_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

theorem cepsCentralZeroConstant_ne_zero {q : Fin d → ℂ}
    (hV : cepsComplexJetPad d q (cepsJetCode (.inl 0)) ≠ 0) :
    cepsCentralZeroConstant d N q ≠ 0 :=
  mul_ne_zero (div_ne_zero hV two_ne_zero) (exp_ne_zero _)

theorem cepsCentralDen_origin (p₀ : Fin d → ℂ) :
    cepsCentralDen d N (p₀, 0, 0, 0) 0 0 = -cepsCentralZeroConstant d N p₀ := by
  rw [cepsCentralDen, cepsCentralG_zero_scale, dslope_same]
  have h : HasDerivAt (fun ξ : ℂ => exp (-ξ) * cepsCentralZeroConstant d N p₀)
      (exp (-0) * (-1) * cepsCentralZeroConstant d N p₀) 0 :=
    ((hasDerivAt_id (0 : ℂ)).neg.cexp).mul_const _
  rw [h.deriv]
  simp

/-! ## The bridge and entrance germs at the merged origin -/

theorem cepsCentralBridge_analyticAt_origin (p₀ : Fin d → ℂ)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => cepsCentralBridge d N X.1 X.2.1 X.2.2)
      ((p₀, 0, 0, 0), 0, 0) := by
  let X₀ : CepsCentralBase d × ℂ × ℂ := ((p₀, 0, 0, 0), 0, 0)
  have hG := cepsCentralG_analyticAt_zero (N := N) (p₀, (0 : ℂ), (0 : ℂ), (0 : ℂ))
  have hG₁ : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralG d N X.1 X.2.1 X.2.2 X.2.1) X₀ :=
    hG.comp_of_eq (analyticAt_id.prod (analyticAt_fst.comp analyticAt_snd)) rfl
  have hG₂ : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralG d N X.1 X.2.1 X.2.2 X.2.2) X₀ :=
    hG.comp_of_eq (analyticAt_id.prod (analyticAt_snd.comp analyticAt_snd)) rfl
  have hD := cepsCentralDen_analyticAt_zero (N := N) (p₀, (0 : ℂ), (0 : ℂ), (0 : ℂ))
  have hD₀ : cepsCentralDen d N X₀.1 X₀.2.1 X₀.2.2 ≠ 0 := by
    change cepsCentralDen d N (p₀, 0, 0, 0) 0 0 ≠ 0
    rw [cepsCentralDen_origin]
    exact neg_ne_zero.mpr (cepsCentralZeroConstant_ne_zero hV)
  exact (hG₁.neg.mul hG₂).div hD hD₀

theorem cepsCentralEntrance_analyticAt_origin (p₀ : Fin d → ℂ)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralEntrance d N X.1 X.2.1 X.2.2) ((p₀, 0, 0, 0), 0, 0) := by
  have hx : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => X.1) ((p₀, 0, 0, 0), 0, 0) :=
    analyticAt_fst
  obtain ⟨hpi, hl, hw, hb⟩ := cepsCentralBase_coords_analyticAt hx
  have hC : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCanonComplexJetPolynomial (cepsComplexJetPad d X.1.1) N (X.1.2.2.2 * X.1.2.1)
        (X.1.2.2.2 ^ 2 * X.1.2.2.1 * (1 + X.1.2.2.2 * X.1.2.1)) (X.1.2.2.2 ^ 2 * X.1.2.2.1))
      ((p₀, 0, 0, 0), 0, 0) :=
    cepsCanonComplexJetPolynomial_analyticAt hpi (hb.mul hl)
      (((hb.pow 2).mul hw).mul ((analyticAt_const (v := (1 : ℂ))).add (hb.mul hl)))
      ((hb.pow 2).mul hw) N
  have hS := cepsCentralEntranceSlope_analyticAt_zero (N := N)
    (p₀, (0 : ℂ), (0 : ℂ), (0 : ℂ)) (by simp)
  have hQ₀ := cepsCentralQuotient_analyticAt_zero (N := N) (p₀, (0 : ℂ), (0 : ℂ), (0 : ℂ))
  have hm : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => (X, X.1.2.2.2 * X.1.2.2.1))
      ((p₀, 0, 0, 0), 0, 0) := analyticAt_id.prod (hb.mul hw)
  have h0 : (fun X : CepsCentralBase d × ℂ × ℂ => (X, X.1.2.2.2 * X.1.2.2.1))
      ((p₀, 0, 0, 0), 0, 0) = (((p₀, 0, 0, 0), 0, 0), 0) := by
    simp only [mul_zero]
  have hQ' := hQ₀.comp_of_eq hm h0
  simp only [Function.comp_def] at hQ'
  have hQ : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralQuotient d N X.1 X.2.1 X.2.2 (X.1.2.2.2 * X.1.2.2.1)) ((p₀, 0, 0, 0), 0, 0) :=
    hQ'
  have hD := cepsCentralDen_analyticAt_zero (N := N) (p₀, (0 : ℂ), (0 : ℂ), (0 : ℂ))
  have hne : cepsCentralQuotient d N (p₀, 0, 0, 0) 0 0 (0 * 0) *
      cepsCentralDen d N (p₀, 0, 0, 0) 0 0 ≠ 0 := by
    rw [cepsCentralQuotient_zero_scale, cepsCentralDen_origin]
    exact mul_ne_zero (div_ne_zero hV two_ne_zero)
      (neg_ne_zero.mpr (cepsCentralZeroConstant_ne_zero hV))
  have hnum : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      -exp (cepsCanonComplexJetPolynomial (cepsComplexJetPad d X.1.1) N (X.1.2.2.2 * X.1.2.1)
        (X.1.2.2.2 ^ 2 * X.1.2.2.1 * (1 + X.1.2.2.2 * X.1.2.1)) (X.1.2.2.2 ^ 2 * X.1.2.2.1)) *
        cepsCentralEntranceSlope d N X.1 X.2.1 X.2.2) ((p₀, 0, 0, 0), 0, 0) :=
    hC.cexp.neg.mul hS
  have hden : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ =>
      cepsCentralQuotient d N X.1 X.2.1 X.2.2 (X.1.2.2.2 * X.1.2.2.1) *
        cepsCentralDen d N X.1 X.2.1 X.2.2) ((p₀, 0, 0, 0), 0, 0) := hQ.mul hD
  exact hnum.div hden hne

end PGM
