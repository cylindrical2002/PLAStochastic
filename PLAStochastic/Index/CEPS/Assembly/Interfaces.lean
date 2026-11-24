import PLAStochastic.Index.CEPS.Family.Defs

/-!
# Track F: the analytic interfaces of the one-layer family expansion

The one-layer family interface `CepsOneLayerFamily` is reduced (in `Assembly.OneLayer`) to the
bundle `CepsTransformInterfaces` stated here. With `h = ε⁻¹` and
`φ_ν(u) = ∫ e^{iux} d(Φ_ε ν)` the bundle consists of

* **T1-mid** (`CepsT1Mid`): the mid-band bound
  `|φ_ν(u)| ≤ K (1+|u|)^d e^{-c√|u|} + K ε^d e^{-cε}` on `U ≤ |u| ≤ ε^{1+δ}`;
* **T1-low** (`CepsT1Low`): `φ_ν(u) = ∑_{k ≤ P} h^k Φ_k(u; J ν) + O(h^{P+1} (1+|u|)^d)` on
  `|u| ≤ (A log ε)²`, for every `P` and `A`;
* **T3** (`CepsT3`): `Φ_0(u; p) = φ_Λ(u)` (independent of `p`), a stretched-exponential bound
  of `φ_Λ`, and finite-order Taylor expansions of `Φ_k` (`k ≥ 1`) and of `c_k` in the finitely
  many jet coordinates `p_i`, `i < dim k`, around `p₀ = J Λ`;
* **T5** (`CepsT5`): `lawC ε ν / ε² = ∑_{k ≤ P} h^k c_k(J ν) + O(h^{P+1})`;
* **JF** (`CepsJF`): along every family expanding in the weighted Sobolev size, each jet
  `J_i(ν_ε)` has a scalar expansion whose `n`-th coefficient is a universal function of
  `g 1, …, g n`.

T1-low, T1-mid and T5 are uniform over the class `CepsInputClass`: a fixed `RegLaw` class and
a weighted Sobolev ball of some radius around the reference density. The high band T2 is
already proved (`norm_charFun_lawPhi_le_of_cepsSobolev`). The quantifier choices are explained
in `research/2026-10-02-lean-ceps/track-F.md`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The characteristic function of the actual normalised one-layer output `Φ_ε ν`. -/
def cepsOutChar (eps : ℝ) (ν : ProbabilityMeasure ℝ) (u : ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * u * x) ∂(lawPhi eps ν : Measure ℝ)

/-- The characteristic function of the reference law `Λ`. -/
def cepsLambdaChar (u : ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * u * x) ∂(cepsLambda : Measure ℝ)

/-- The input class of T1 and T5: a regular law whose density lies in the exponentially
weighted `W^{m,1}` ball of radius `r` around the density of `Λ`. The reference field keeps the
weight inside the envelope of `Λ`; beyond it the Bochner size of `f - f_Λ` would vanish by
convention and the ball condition would be void. -/
structure CepsInputClass (D θ vlo vhi : ℝ) (m : ℕ) (η r : ℝ) (ν : ProbabilityMeasure ℝ) :
    Prop where
  reg : RegLaw D θ vlo vhi ν
  reference : CepsSobolevClass m η cepsLambdaDensity
  density : ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ CepsSobolevClass m η f ∧
    (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    cepsSobolev m η (fun x => f x - cepsLambdaDensity x) ≤ r

/-- The stretched-exponential frequency weight `(1+|u|)^d e^{-c√|u|}`. -/
def cepsStretchedWeight (c : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)

theorem cepsStretchedWeight_nonneg (c : ℝ) (d : ℕ) (u : ℝ) : 0 ≤ cepsStretchedWeight c d u := by
  unfold cepsStretchedWeight
  positivity

/-- Multi-indices of the Taylor box of order `N` in `d` coordinates. A box truncation of a
Taylor series differs from the total-degree truncation by monomials of degree `> N`. -/
def cepsTaylorBox (d N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (N + 1)

/-- The monomial `y^α = ∏ᵢ yᵢ^{αᵢ}`. -/
def cepsMonomial {d : ℕ} (y : Fin d → ℝ) (α : Fin d → ℕ) : ℝ :=
  ∏ i, y i ^ α i

/-- The data of the jet representation: the jet map `J`, the transform coefficients `Φ_k`,
the scalar coefficients `c_k`, the number of jet coordinates read at order `k`, the Taylor
coefficients of `Φ_k` and `c_k` at `J Λ`, and the jet expansion coefficients of JF. -/
structure CepsJetData where
  /-- The jet map `J`. -/
  jet : ProbabilityMeasure ℝ → ℕ → ℝ
  /-- `Φ_k(u; p)`: the `k`-th coefficient of the output characteristic function. -/
  phi : ℕ → ℝ → (ℕ → ℝ) → ℂ
  /-- `c_k(p)`: the `k`-th coefficient of `lawC / ε²`. -/
  scal : ℕ → (ℕ → ℝ) → ℝ
  /-- `Φ_k` and `c_k` read only the jet coordinates `i < dim k` (near `J Λ`). -/
  dim : ℕ → ℕ
  /-- Taylor coefficients of `Φ_k` at `J Λ`. -/
  phiTaylor : (k : ℕ) → (Fin (dim k) → ℕ) → ℝ → ℂ
  /-- Taylor coefficients of `c_k` at `J Λ`. -/
  scalTaylor : (k : ℕ) → (Fin (dim k) → ℕ) → ℝ
  /-- `jetCoeff i n g`: the `n`-th coefficient of `J_i` along a family with density
  coefficients `g`. -/
  jetCoeff : ℕ → ℕ → (ℕ → ℝ → ℝ) → ℝ

namespace CepsJetData

variable (J : CepsJetData)

/-- The reference jets `p₀ = J Λ`. -/
def ref : ℕ → ℝ := J.jet cepsLambda

/-- The displacement `p_i - p₀_i` of the coordinates read at order `k`. -/
def disp (k : ℕ) (p : ℕ → ℝ) : Fin (J.dim k) → ℝ := fun i => p i - J.ref i

/-- The size `∑ᵢ |p_i - p₀_i|` of the displacement at order `k`. -/
def dispSize (k : ℕ) (p : ℕ → ℝ) : ℝ := ∑ i, |J.disp k p i|

/-- The Taylor polynomial of order `N` of `Φ_k(u; ·)` at `J Λ`. -/
def phiTaylorPoly (k N : ℕ) (u : ℝ) (p : ℕ → ℝ) : ℂ :=
  ∑ α ∈ cepsTaylorBox (J.dim k) N, J.phiTaylor k α u * (cepsMonomial (J.disp k p) α : ℂ)

/-- The Taylor polynomial of order `N` of `c_k` at `J Λ`. -/
def scalTaylorPoly (k N : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ α ∈ cepsTaylorBox (J.dim k) N, J.scalTaylor k α * cepsMonomial (J.disp k p) α

end CepsJetData

/-- **T1-mid.** One mid-band exponent `δ` and one derivative budget serve every regular class
and every input weight. -/
def CepsT1Mid : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
    0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ c U K eps₀ : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ u : ℝ, U ≤ |u| → |u| ≤ eps ^ (1 + δ) →
          ‖cepsOutChar eps ν u‖ ≤ K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) +
            K * eps ^ d * Real.exp (-c * eps)

/-- **T1-low.** The low-frequency expansion of the output characteristic function through the
jets of the input, uniformly over the class. -/
def CepsT1Low (J : CepsJetData) : Prop :=
  ∀ P : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
    0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η → ∀ A : ℝ, 0 < A →
    ∃ r : ℝ, 0 < r ∧ ∃ K eps₀ : ℝ, ∃ d : ℕ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ u : ℝ, |u| ≤ (A * Real.log eps) ^ 2 →
          ‖cepsOutChar eps ν u -
              ∑ k ∈ Finset.range (P + 1), ((eps⁻¹) ^ k : ℝ) • J.phi k u (J.jet ν)‖ ≤
            K * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d

/-- **T3.** The order-zero coefficient is the characteristic function of `Λ` for every jet
vector; it decays stretched-exponentially; the higher coefficients and all scalar
coefficients have finite-order Taylor expansions in the jet coordinates read at their order.
All constants may depend on the order, the multi-index and the Taylor order. -/
structure CepsT3 (J : CepsJetData) : Prop where
  phi_zero : ∀ u p, J.phi 0 u p = cepsLambdaChar u
  lambdaChar_bound : ∃ K c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ u, ‖cepsLambdaChar u‖ ≤
    K * cepsStretchedWeight c d u
  phiTaylor_bound : ∀ k : ℕ, 1 ≤ k → ∀ α : Fin (J.dim k) → ℕ,
    ∃ K c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ u, ‖J.phiTaylor k α u‖ ≤ K * cepsStretchedWeight c d u
  phi_remainder : ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ, ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ d : ℕ,
    ∀ (u : ℝ) (p : ℕ → ℝ), (∀ i, |J.disp k p i| ≤ ρ) →
      ‖J.phi k u p - J.phiTaylorPoly k N u p‖ ≤
        K * cepsStretchedWeight c d u * J.dispSize k p ^ (N + 1)
  scal_remainder : ∀ k N : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧
    ∀ p : ℕ → ℝ, (∀ i, |J.disp k p i| ≤ ρ) →
      |J.scal k p - J.scalTaylorPoly k N p| ≤ K * J.dispSize k p ^ (N + 1)

/-- **T5.** The scalar expansion of the mean segment length through the jets of the input. -/
def CepsT5 (J : CepsJetData) : Prop :=
  ∀ P : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
    0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
    ∃ r : ℝ, 0 < r ∧ ∃ K eps₀ : ℝ, ∀ eps : ℝ, eps₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        |lawC eps ν / eps ^ 2 - ∑ k ∈ Finset.range (P + 1), (eps⁻¹) ^ k * J.scal k (J.jet ν)| ≤
          K * (eps⁻¹) ^ (P + 1)

/-- **JF.** Jets along expanding families: the `n`-th coefficient is universal and depends only
on the density coefficients `g 1, …, g n`. -/
structure CepsJF (J : CepsJetData) : Prop where
  triangular : ∀ (i n : ℕ) (g g' : ℕ → ℝ → ℝ), (∀ j, 1 ≤ j → j ≤ n → g j = g' j) →
    J.jetCoeff i n g = J.jetCoeff i n g'
  expansion : ∀ i P : ℕ, ∃ m : ℕ, ∀ (ν : ℝ → ProbabilityMeasure ℝ) (g : ℕ → ℝ → ℝ) (η : ℝ),
    CepsEventuallyRegular ν → 0 < η → CepsFamilyExpansion ν m η P g →
      HasInverseExpansionAtOrder (fun eps => J.jet (ν eps) i) (fun n => J.jetCoeff i n g) P

/-- **The remaining analytic interfaces of the one-layer family expansion.** Together with the
proved high band T2 and orbit closure they give `CepsOneLayerFamily`
(`cepsOneLayerFamily_of_interfaces`). -/
def CepsTransformInterfaces : Prop :=
  CepsT1Mid ∧ ∃ J : CepsJetData, CepsT1Low J ∧ CepsT3 J ∧ CepsT5 J ∧ CepsJF J

end

end PGM
