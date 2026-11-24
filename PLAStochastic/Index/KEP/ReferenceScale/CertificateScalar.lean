import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeSecond

/-!
# The actual compact certificate scalar and its two derivatives

The logarithmic coarea scalar is `d κ K`. Its second derivative is expressed
by the true Ward formula, with second spatial derivatives only on the original
bridge and first derivatives on each internal pin. These are derivatives of
the fixed finite integrals, without additional regularity certificates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepFixedBridgeSlopeSecondWard (p p' p'' q : ℝ → ℝ → ℝ)
    (w σ s : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  let c := (n + 1 : ℕ) * σ + x - y
  kepFixedBridge p w s n x y - 3 * c * kepFixedBridgeRight p p' w s n x y +
    c ^ 2 * kepFixedBridgeRight p p'' w s n x y +
    kepBridgeTransportFlux p w σ s n x y - c * kepBridgeFluxRight p p' w σ s n x y -
    kepBridgeFluxSlope p q w σ s n x y

theorem continuous_kepBridgeFluxRight_slope {p p' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (w σ : ℝ) (n : ℕ) (x y : ℝ) :
    Continuous (fun s => kepBridgeFluxRight p p' w σ s n x y) := by
  have hk (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridge p w s m u v) :=
    (continuous_kepFixedBridge hp w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hr (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridgeRight p p' w s m u v) :=
    (continuous_kepFixedBridgeRight hp hp' w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  unfold kepBridgeFluxRight
  exact continuous_finsetSum _ fun l _ =>
    (((hk l x w).const_mul _).mul (hr (n - 1 - l) w y)).sub
      (((hk l x 0).const_mul _).mul (hr (n - 1 - l) 0 y))

theorem continuous_kepBridgeFluxSlope_slope {p q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hq : Continuous (Function.uncurry q))
    (w σ : ℝ) (n : ℕ) (x y : ℝ) :
    Continuous (fun s => kepBridgeFluxSlope p q w σ s n x y) := by
  have hk (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridge p w s m u v) :=
    (continuous_kepFixedBridge hp w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hqk (m : ℕ) (u v : ℝ) : Continuous (fun s => kepFixedBridgeSlope p q w s m u v) :=
    (continuous_kepFixedBridgeSlope hp hq w m).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  unfold kepBridgeFluxSlope
  exact continuous_finsetSum _ fun l _ =>
    ((((hqk l x w).mul (hk (n - 1 - l) w y)).add
      ((hk l x w).mul (hqk (n - 1 - l) w y))).const_mul _).sub
      ((((hqk l x 0).mul (hk (n - 1 - l) 0 y)).add
        ((hk l x 0).mul (hqk (n - 1 - l) 0 y))).const_mul _)

theorem continuous_kepFixedBridgeSlopeSecondWard {p p' p'' q : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hp'' : Continuous (Function.uncurry p'')) (hq : Continuous (Function.uncurry q))
    (w σ : ℝ) (n : ℕ) (x y : ℝ) :
    Continuous (fun s => kepFixedBridgeSlopeSecondWard p p' p'' q w σ s n x y) := by
  have hk := (continuous_kepFixedBridge hp w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const)) (f := fun s : ℝ =>
      (s, x, y))
  have hr := (continuous_kepFixedBridgeRight hp hp' w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const)) (f := fun s : ℝ =>
      (s, x, y))
  have hrr := (continuous_kepFixedBridgeRight hp hp'' w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const)) (f := fun s : ℝ =>
      (s, x, y))
  have hb := (continuous_kepBridgeTransportFlux hp w σ n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const)) (f := fun s : ℝ =>
      (s, x, y))
  exact (((hk.sub (hr.const_mul _)).add (hrr.const_mul _)).add hb).sub
    ((continuous_kepBridgeFluxRight_slope hp hp' w σ n x y).const_mul _) |>.sub
      (continuous_kepBridgeFluxSlope_slope hp hq w σ n x y)

def kepCertificateScalar (p : ℝ → ℝ → ℝ) (w d : ℝ) (n : ℕ) (κ : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * κ s * kepFixedBridge p w s n 0 w

def kepCertificateScalarFirst (p q : ℝ → ℝ → ℝ) (w d : ℝ) (n : ℕ)
    (κ κ' : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * (κ' s * kepFixedBridge p w s n 0 w + κ s * kepFixedBridgeSlope p q w s n 0 w)

def kepCertificateScalarSecond (p p' p'' q : ℝ → ℝ → ℝ) (w d : ℝ) (n : ℕ)
    (κ κ' κ'' : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * (κ'' s * kepFixedBridge p w s n 0 w +
    2 * κ' s * kepFixedBridgeSlope p q w s n 0 w +
    κ s * kepFixedBridgeSlopeSecondWard p p' p'' q w 1 s n 0 w)

/-- All bridge regularity is supplied by the actual reference Gamma law. -/
theorem kepReference_certificateScalar_C2 {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {κ κ' κ'' : ℝ → ℝ} (hκ : Continuous κ) (hκ' : Continuous κ') (hκ'' : Continuous κ'')
    (hdκ : ∀ s, HasDerivAt κ (κ' s) s) (hddκ : ∀ s, HasDerivAt κ' (κ'' s) s)
    {w : ℝ} (hw : 0 ≤ w) (d : ℝ) (n : ℕ) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let p := kepLogStep f 1
    let p' := kepLogStepFirst f' 1
    let p'' := kepLogStepSecond f'' 1
    let q := kepLogStepSlope f f' 1
    let R := kepCertificateScalar p w d n κ
    let R' := kepCertificateScalarFirst p q w d n κ κ'
    let R'' := kepCertificateScalarSecond p p' p'' q w d n κ κ' κ''
    Continuous R ∧ Continuous R' ∧ Continuous R'' ∧
      (∀ s, HasDerivAt R (R' s) s) ∧ (∀ s, HasDerivAt R' (R'' s) s) := by
  have hc := kepReferenceDensity_classical heps hj
  have hf := continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt
  have hf' := continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let p := kepLogStep f 1
  let p' := kepLogStepFirst f' 1
  let p'' := kepLogStepSecond f'' 1
  let q := kepLogStepSlope f f' 1
  have hp := continuous_kepLogStep hf 1
  have hp' := continuous_kepLogStepFirst hf' 1
  have hp'' := continuous_kepLogStepSecond hc.2.2.2.1 1
  have hq := continuous_kepLogStepSlope hf hf' 1
  have hk : Continuous (fun s => kepFixedBridge p w s n 0 w) :=
    (continuous_kepFixedBridge hp w n).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hks : Continuous (fun s => kepFixedBridgeSlope p q w s n 0 w) :=
    (continuous_kepFixedBridgeSlope hp hq w n).comp
      (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hkss := continuous_kepFixedBridgeSlopeSecondWard hp hp' hp'' hq w 1 n 0 w
  refine ⟨(hκ.const_mul d).mul hk,
    ((hκ'.mul hk).add (hκ.mul hks)).const_mul d,
    (((hκ''.mul hk).add ((hκ'.const_mul 2).mul hks)).add (hκ.mul hkss)).const_mul d,
    ?_, ?_⟩
  · intro s
    convert (((hdκ s).const_mul d).mul
      (hasDerivAt_kepFixedBridge_slope hp hq (hasDerivAt_kepLogStep_slope hc.2.1 1)
        w s n 0 w)) using 1 <;> first | rfl | (unfold kepCertificateScalarFirst; ring)
  · intro s
    have hkd := hasDerivAt_kepFixedBridge_slope hp hq
      (hasDerivAt_kepLogStep_slope hc.2.1 1) w s n 0 w
    have hksd := hasDerivAt_kepLogBridgeSlope_second_ward hf hf' hc.2.2.2.1
      hc.2.1 hc.2.2.1 (by norm_num : (1 : ℝ) ^ 2 = 1) hw s n 0 w
    convert ((((hddκ s).mul hkd).add ((hdκ s).mul hksd)).const_mul d) using 1 <;>
      first | rfl | (unfold kepCertificateScalarSecond kepFixedBridgeSlopeSecondWard; ring)

end

end PGM
