import PLAStochastic.Index.CEPS.Normal.RootDifferential

/-!
# Half-line total derivative from the root equation and abstract transport

The hypotheses are joint real differentiability in drift, complex
differentiability in discount/space, the root equations, and the transport
identity at the two needed space points. No derivative of the desired
primitive or desired occupation pair is assumed.
-/

noncomputable section
open Complex Filter Topology
namespace PGM

def cepsNormalHalfPrimitive (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ)
    (d : ℝ → ℂ → ℂ → ℂ) (L : ℂ → ℂ → ℂ → ℂ) (μ : ℝ) (q t w : ℂ) : ℂ :=
  (B μ q - t) * cepsNormalRootSlope ψ B μ q / d μ q t ^ 2 *
    exp (2 * L μ q t - 2 * L μ q (B μ q) - (B μ q - t) * (w * (1 + (μ : ℂ))))

def cepsNormalHalfPairComponents (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ)
    (d : ℝ → ℂ → ℂ → ℂ) (L : ℂ → ℂ → ℂ → ℂ) (μ : ℝ) (q t w : ℂ) : ℂ :=
  let l := w * (1 + (μ : ℂ))
  exp (t * l) * (exp (L μ q t) * (B μ q - t) / d μ q t) ^ 2 *
    (-deriv (fun q' => cepsNormalRootSlope ψ B μ q' * exp (-B μ q' * l - 2 * L μ q' (B μ q'))) q -
      w * (cepsNormalRootSlope ψ B μ q * exp (-B μ q * l - 2 * L μ q (B μ q))))

/-- C-8 away from `ψ' = 0` and `d = 0`, with the root and factor path jets
derived from their defining equations. `Qcurve' = t` covers marked discount
`t(1+μ)`; `t = 0` and constant `Qcurve` give the unmarked (F10).
-/
theorem cepsNormal_halfPair_of_transport
    (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ) (d : ℝ → ℂ → ℂ → ℂ)
    (L : ℂ → ℂ → ℂ → ℂ) (Qcurve : ℝ → ℂ)
    {μ : ℝ} {t w b' bq p₂ e aₜ bₜ cₜ aᵦ bᵦ cᵦ : ℂ}
    (hB : HasDerivAt (fun x : ℝ => B x (Qcurve x)) b' μ)
    (hBq : HasDerivAt (B μ) bq (Qcurve μ))
    (hψ : HasDerivAt ψ (deriv ψ (B μ (Qcurve μ))) (B μ (Qcurve μ)))
    (hψ' : HasDerivAt (deriv ψ) p₂ (B μ (Qcurve μ)))
    (hQ : HasDerivAt Qcurve t μ)
    (hroot : ∀ᶠ (x : ℝ) in 𝓝 μ, ψ (B x (Qcurve x)) + (x : ℂ) * B x (Qcurve x) = Qcurve x)
    (hrootq : ∀ᶠ (q' : ℂ) in 𝓝 (Qcurve μ), ψ (B μ q') + (μ : ℂ) * B μ q' = q')
    (hp : cepsNormalRootSlope ψ B μ (Qcurve μ) ≠ 0)
    (hd : HasDerivAt (fun x : ℝ => d x (Qcurve x) t) 0 μ)
    (hd0 : d μ (Qcurve μ) t ≠ 0)
    (hLt : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential aₜ bₜ cₜ) (μ, (Qcurve μ, t)))
    (hLb : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential aᵦ bᵦ cᵦ) (μ, (Qcurve μ, B μ (Qcurve μ))))
    (hLqz : HasFDerivAt (fun x : ℂ × ℂ => L μ x.1 x.2)
      (cepsNormalFactorQZDifferential bᵦ cᵦ) (Qcurve μ, B μ (Qcurve μ)))
    (htransportₜ : aₜ + t * bₜ = e) (htransportᵦ : aᵦ + B μ (Qcurve μ) * bᵦ = e) :
    HasDerivAt (fun x : ℝ => cepsNormalHalfPrimitive ψ B d L x (Qcurve x) t w)
      (cepsNormalHalfPairComponents ψ B d L μ (Qcurve μ) t w) μ := by
  obtain ⟨hBd, hPd, hBqd, hPqd⟩ := cepsNormal_root_jets ψ B Qcurve
    hB hBq hψ hψ' hQ hroot hrootq hp
  obtain ⟨hTd, hCd⟩ := cepsNormal_marked_factor_jets L
    (Q := Qcurve) (B := fun x => B x (Qcurve x))
    (p := cepsNormalRootSlope ψ B μ (Qcurve μ))
    hQ hBd hp hLt hLb htransportₜ htransportᵦ
  have hCqd := cepsNormal_factor_q_jet L (B := B μ) hLqz hBqd
  exact cepsNormal_halfPair_totalDerivative B (cepsNormalRootSlope ψ B) d L Qcurve μ
    t w p₂ (bᵦ + cᵦ / cepsNormalRootSlope ψ B μ (Qcurve μ)) e
    hBd hPd hTd hCd hd hBqd hPqd hCqd hp hd0

/-- Identification with the original abstract-data half-line pair (C15). -/
theorem cepsNormalHalfPairAt_eq_components
    (A : ℂ → ℂ → CepsNormalData) (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ)
    (d : ℝ → ℂ → ℂ → ℂ) (L : ℂ → ℂ → ℂ → ℂ)
    (hB : ∀ (μ : ℝ) q, (A μ q).βp = B μ q)
    (hP : ∀ (μ : ℝ) q, (A μ q).ψp = cepsNormalRootSlope ψ B μ q)
    (hd : ∀ (μ : ℝ) q t, (A μ q).d t = d μ q t)
    (μ : ℝ) (q t w : ℂ) :
    cepsNormalHalfPairAt A L μ q t w = cepsNormalHalfPairComponents ψ B d L μ q t w := by
  simp only [cepsNormalHalfPairAt, cepsNormalHalfPairComponents,
    CepsNormalData.halfEntrance, CepsNormalData.halfBridge, hB, hP, hd]

/-- The cancelled primitive agrees with `𝒦/(β₊-t)` wherever that quotient is defined. -/
theorem cepsNormalHalfPrimitive_eq_quotient
    (a : CepsNormalData) (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ)
    (d : ℝ → ℂ → ℂ → ℂ) (L : ℂ → ℂ → ℂ → ℂ)
    (μ : ℝ) (q t w : ℂ) (hB : a.βp = B μ q)
    (hP : a.ψp = cepsNormalRootSlope ψ B μ q) (hd : a.d t = d μ q t)
    (hBt : B μ q - t ≠ 0) :
    cepsNormalHalfPrimitive ψ B d L μ q t w =
      a.primitiveNumerator L μ q t (w * (1 + (μ : ℂ))) / (a.βp - t) := by
  rw [CepsNormalData.primitiveNumerator_eq, hB, hP, hd]
  unfold cepsNormalHalfPrimitive
  rw [exp_sub]
  field_simp
  rw [mul_assoc (cepsNormalRootSlope ψ B μ q), ← exp_add, add_neg_cancel, exp_zero, mul_one]

end PGM
