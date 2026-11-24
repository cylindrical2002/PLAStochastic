import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance

/-!
# WP4: functionals, influences and interface predicates of the joint response (J)

Objects of `research/2026-09-28-gep-closure/joint-response.md` (JR), realised on the canonical
iid space `iidLaw ν` of `PLAStochastic/Index/GEP/LayerLaw/Defs.lean`.  Gaps are indexed from `0`, so `{t < T}` depends on
`g 0, …, g (t-1)` (`isStoppingRule_gapSegLen`).

**Functionals** (the three rows of (J)):
* `lawA eps ν = log v(ν) + log C_ε(ν)`;
* `lawV eps ν = v(Φ_ε ν)`;
* `outFn eps ν ψ = ∫ φ_ψ d(Φ_ε ν)`, where `φ_ψ(y) = ∫_{(0,y)} ψ` (`testFn`) and the test
  derivative `ψ` satisfies `OutTest η M ψ`: `|ψ x| ≤ M e^{ηx}` on `x ≥ 0`.

**Influences** (one inserted gap, `Function.update g i x`):
* `lawJC eps ν x = ∑_k ∑_{i<k} P(T > k | g_i = x)` (kernel-bv §8);
* `insKernel eps ν F x = ∑_i E[F(g with g_i := x); i < T(g)]` (PD (33); the event `i < T` does
  not read `g_i`);
* `outIns`, `outKappa`, `outJ = outIns - κ_φ J_C / C` (PD §8.3), `directKernel = H_φ`
  (direct-endpoint §3, PD §8.3: `H_φ = I_{φ'(·/C)} / C`);
* `lawJA = J_C / C + (x-1)² / v`, `lawJV = outJ psiVar` (the test `φ(y) = y² - 2y`; on mean-one
  paths `v(Φ ν) = ∫ φ dΦν + 1`).

**Derivatives** are a.e. objects.  `AEPrimitive J j` says that `J` agrees a.e. on `(0,∞)` with
the locally absolutely continuous function `c + ∫_0^x j`; `j` is then unique a.e.  The boundary
kernel `B_φ` of IL §1/§6 is specified this way (`IsBdryKernel`): it is the density with
`outIns = c + ∫ (H_φ + B_φ)`, i.e. JR (ID) before normalisation.

**Interface shapes**: `KernelApproxLip R L ρ j` is the (AL) shape on `(0,R)`; `KernelTail N ζ j`
is the (TAIL) shape; `InflDecomp η ε K J` is JR (R): `J' = a + 2 q x + r`, `|q| ≤ K`,
`|r| ≤ ε e^{ηx}` a.e.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ## The mixture path `ν_s = (1 - s) ν₀ + s ν₁` (JR §5) -/

/-- The mixing parameter clamped to `[0,1]`. -/
def mixParam (s : ℝ) : ℝ := max 0 (min 1 s)

theorem mixParam_nonneg (s : ℝ) : 0 ≤ mixParam s := le_max_left _ _

theorem mixParam_le_one (s : ℝ) : mixParam s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem mixParam_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : mixParam s = s := by
  rw [mixParam, min_eq_right hs.2, max_eq_right hs.1]

/-- The mixture `(1 - s) ν₀ + s ν₁`, with `s` clamped to `[0,1]`. -/
def mixPM (ν₀ ν₁ : ProbabilityMeasure ℝ) (s : ℝ) : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal (1 - mixParam s) • (ν₀ : Measure ℝ) +
      ENNReal.ofReal (mixParam s) • (ν₁ : Measure ℝ), by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add (by linarith [mixParam_le_one s]) (mixParam_nonneg s)]
    simp⟩

theorem coe_mixPM (ν₀ ν₁ : ProbabilityMeasure ℝ) (s : ℝ) :
    (mixPM ν₀ ν₁ s : Measure ℝ) = ENNReal.ofReal (1 - mixParam s) • (ν₀ : Measure ℝ) +
      ENNReal.ofReal (mixParam s) • (ν₁ : Measure ℝ) := rfl

/-! ## The three functionals of (J) -/

/-- Row 1 of (J): `A(ν) = log v(ν) + log C_ε(ν)`. -/
def lawA (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ℝ :=
  Real.log (lawVar ν) + Real.log (lawC eps ν)

/-- Row 2 of (J): `V(ν) = v(Φ_ε ν)`. -/
def lawV (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ℝ := lawVar (lawPhi eps ν)

/-- The test function with derivative `ψ` and `φ(0) = 0`: `φ_ψ(y) = ∫_{(0,y)} ψ`
(zero for `y ≤ 0`). -/
def testFn (ψ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in Ioo 0 y, ψ t

/-- Row 3 of (J): the output test `F_φ(ν) = ∫ φ_ψ d(Φ_ε ν)`. -/
def outFn (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ∫ y, testFn ψ y ∂(lawPhi eps ν : Measure ℝ)

/-- Admissible test derivatives of weight `η` and size `M`: `|φ'(x)| ≤ M e^{ηx}` for `x ≥ 0`.
JR §1 uses `M = 1`; the size `M` makes the interfaces homogeneous (all kernels are linear in
`ψ`), which covers the variance test `psiVar`. -/
def OutTest (η M : ℝ) (ψ : ℝ → ℝ) : Prop :=
  Measurable ψ ∧ ∀ x, 0 ≤ x → |ψ x| ≤ M * Real.exp (η * x)

/-! ## One-gap influences on the canonical space -/

/-- `J_C(x) = ∑_{k ≥ 1} ∑_{i < k} P(T > k | g_i = x)` (kernel-bv §8, with gaps indexed from `0`).
The conditional probability is realised by inserting `x` at coordinate `i`. -/
def lawJC (eps : ℝ) (ν : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, ∑ i ∈ Finset.range k,
    (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}

/-- The one-gap insertion kernel of a functional `F` of the stopped path (PD (33)):
`I_F(x) = ∑_i E[F(g with g_i := x); i < T(g)]`.  Since `{i < T}` reads only `g 0, …, g (i-1)`,
this is `∑_t ∑_{i<t} E[F 1_{T=t} | g_i = x]`. -/
def insKernel (eps : ℝ) (ν : ProbabilityMeasure ℝ) (F : (ℕ → ℝ) → ℝ) (x : ℝ) : ℝ :=
  ∑' i : ℕ, ∫ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
    (fun g => F (Function.update g i x)) g ∂(iidLaw ν)

/-- The raw (fixed base scale `C`) insertion kernel of the output test `φ_ψ(S_T / C)`. -/
def outIns (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  insKernel eps ν (fun g => testFn ψ (stopSum eps g / lawC eps ν)) x

/-- The normalisation coefficient `κ_φ = E[Y φ'(Y)]`, `Y ~ Φ_ε ν`. -/
def outKappa (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) : ℝ :=
  ∫ y, y * ψ y ∂(lawPhi eps ν : Measure ℝ)

/-- The full influence of the normalised output test: `J_φ = I_φ - κ_φ J_C / C` (PD §8.3). -/
def outJ (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  outIns eps ν ψ x - outKappa eps ν ψ * (lawJC eps ν x / lawC eps ν)

/-- The direct term `H_φ(x) = C⁻¹ ∑_i E[φ'(S_T / C)(g_i := x); i < T]`
(direct-endpoint-response §3; PD §8.3, `H_φ = I_F / C`). -/
def directKernel (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  insKernel eps ν (fun g => ψ (stopSum eps g / lawC eps ν)) x / lawC eps ν

/-- The influence of `A = log v + log C`: `J_A = J_C / C + (x - 1)² / v` (PD §5, JR (P)). -/
def lawJA (eps : ℝ) (ν : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  lawJC eps ν x / lawC eps ν + (x - 1) ^ 2 / lawVar ν

/-- The test derivative of the variance row: `φ(y) = y² - 2y`, so that
`v(Φ ν) = ∫ φ dΦν + 1` when `Φ ν` has mean one. -/
def psiVar (y : ℝ) : ℝ := 2 * y - 2

/-- The influence of `V = v(Φ_ε ν)`. -/
def lawJV (eps : ℝ) (ν : ProbabilityMeasure ℝ) (x : ℝ) : ℝ := outJ eps ν psiVar x

/-! ## Interface shapes -/

/-- `J` agrees a.e. on `(0,∞)` with the locally absolutely continuous `c + ∫_0^x j`. -/
def AEPrimitive (J j : ℝ → ℝ) : Prop :=
  (∀ R : ℝ, IntervalIntegrable j volume 0 R) ∧
    ∃ c : ℝ, ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), J x = c + ∫ t in (0 : ℝ)..x, j t

/-- `B` is a boundary kernel of the output test `ψ` at `ν`: `I_φ = c + ∫ (H_φ + B)`
(JR (ID) at fixed base scale; IL §1, §6).  `B` is unique a.e. -/
def IsBdryKernel (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ B : ℝ → ℝ) : Prop :=
  AEPrimitive (outIns eps ν ψ) (fun x => directKernel eps ν ψ x + B x)

/-- The (AL) shape on `(0,R)`: `j = G + r` with `Lip G ≤ L` on `[0,R]` and `|r| ≤ ρ` a.e. -/
def KernelApproxLip (R L ρ : ℝ) (j : ℝ → ℝ) : Prop :=
  ∃ G : ℝ → ℝ, (∀ x ∈ Icc 0 R, ∀ y ∈ Icc 0 R, |G x - G y| ≤ L * |x - y|) ∧
    ∀ᵐ x ∂(volume.restrict (Ioo 0 R)), |j x - G x| ≤ ρ

/-- The (TAIL) shape: `|j x| ≤ N e^{ζx}` a.e. on `(0,∞)`. -/
def KernelTail (N ζ : ℝ) (j : ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), |j x| ≤ N * Real.exp (ζ * x)

/-- JR (R): `J' = a + 2 q x + r` with `|q| ≤ K` and `|r| ≤ ε e^{ηx}` a.e. on `(0,∞)`. -/
def InflDecomp (η ε K : ℝ) (J : ℝ → ℝ) : Prop :=
  ∃ a q : ℝ, ∃ r : ℝ → ℝ, |q| ≤ K ∧ AEPrimitive J (fun t => a + 2 * q * t + r t) ∧
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |r t| ≤ ε * Real.exp (η * t)

/-- The fixed quadratic calibration direction of JR (Q): `ω = ½(1_{(0,1]} - 2·1_{(1,2]} +
1_{(2,3]})`, with `∫ ω = ∫ x ω = 0` and `∫ x² ω = 1`. -/
def quadDir (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ)) x -
    (Ioc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) x +
    (Ioc (2 : ℝ) 3).indicator (fun _ => (1 / 2 : ℝ)) x

/-! ## The interface of the reduction (JR §5) -/

/-- Score differentiation along the mixture path: `s ↦ F(ν_s)` is continuous on `[0,1]` and
has derivative `∫ J_{ν_s} d(ν₁ - ν₀)` on `(0,1)` (JR §5, IL §8 (mix)). -/
def MixDiff (F : ProbabilityMeasure ℝ → ℝ) (J : ProbabilityMeasure ℝ → ℝ → ℝ)
    (ν₀ ν₁ : ProbabilityMeasure ℝ) : Prop :=
  ContinuousOn (fun s => F (mixPM ν₀ ν₁ s)) (Icc 0 1) ∧
    ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s => F (mixPM ν₀ ν₁ s))
      ((∫ x, J (mixPM ν₀ ν₁ s) x ∂(ν₁ : Measure ℝ)) -
        ∫ x, J (mixPM ν₀ ν₁ s) x ∂(ν₀ : Measure ℝ)) s

/-- **Leaf 4A-S (score calculus).**  The three functionals of (J) are differentiable along
mixture paths of the class with the influences `lawJA`, `lawJV`, `outJ`, for all output
tests of some weight `η₀ > 0`, and continuous at the endpoints. -/
def ScoreCalculus : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ η₀ e0 : ℝ, 0 < η₀ ∧ ∀ eps, e0 ≤ eps → ∀ ν₀ ν₁ : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν₀ → RegLaw D θ vlo vhi ν₁ →
        MixDiff (lawA eps) (lawJA eps) ν₀ ν₁ ∧ MixDiff (lawV eps) (lawJV eps) ν₀ ν₁ ∧
        ∀ M ψ, OutTest η₀ M ψ →
          MixDiff (fun ν => outFn eps ν ψ) (fun ν x => outJ eps ν ψ x) ν₀ ν₁

/-- JR (R) on the class: for every small weight `η` there are `K` and `ε_e → 0` such that
`J_A' = a + r`, `J_V' = a + r` and `J_φ' = a + 2 q x + r` with `|q| ≤ K M`, `|r| ≤ ε_e M e^{ηx}`,
for all laws of the class and all tests `OutTest η M ψ`.  Proved from the leaves in
`PLAStochastic/Index/GEP/Response/InfluenceDecomposition.lean`. -/
def InfluenceDecomp : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ ηm : ℝ, 0 < ηm ∧ ∀ η, 0 < η → η ≤ ηm →
      ∃ K e0 : ℝ, ∃ ε : ℝ → ℝ, 0 ≤ K ∧ (∀ e, 0 ≤ ε e) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν →
          InflDecomp η (ε eps) 0 (lawJA eps ν) ∧ InflDecomp η (ε eps) 0 (lawJV eps ν) ∧
          ∀ M ψ, OutTest η M ψ → InflDecomp η (M * ε eps) (M * K) (outJ eps ν ψ)

/-! ## The leaves of the derivative layer (JR §2–4) -/

/-- **Leaf 4B-C** (IL (AL), (TAIL); kernel-bv §8; input-flux-kernel (IF); JR (ID) for `J_C`).
`J_C / C` has an a.e. derivative `j`; on `(0, b log ε)` it is `G + r` with
`Lip G ≤ K √ε (log ε)^P`, `|r| ≤ K/ε`; globally `|j| ≤ K ε^{P₀} e^{ζx}`.  `P₀` is fixed before
`b, ζ` (IL line 26). -/
def KernelC : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ P₀ : ℕ, ∀ b ζ : ℝ, 0 < b → 0 < ζ → ∃ (P : ℕ) (K e0 : ℝ),
      ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν → ∃ j : ℝ → ℝ,
        AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j ∧
        KernelApproxLip (b * Real.log eps) (K * Real.sqrt eps * Real.log eps ^ P) (K / eps) j ∧
        KernelTail (K * eps ^ P₀) ζ j

/-- **Leaf 4B-φ** (IL §6–7; JR (ID) at fixed base scale).  For output weights `η ≤ ηB`, every
test has a boundary kernel `B_φ` with the same (AL) and (TAIL) shapes, homogeneous in `M`. -/
def KernelPhi : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ η, 0 < η → η ≤ ηB →
      ∃ P₀ : ℕ, ∀ b ζ : ℝ, 0 < b → 0 < ζ → ∃ (P : ℕ) (K e0 : ℝ),
        ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν → ∀ M ψ, OutTest η M ψ →
          ∃ B : ℝ → ℝ, IsBdryKernel eps ν ψ B ∧
            KernelApproxLip (b * Real.log eps) (M * (K * Real.sqrt eps * Real.log eps ^ P))
              (M * (K / eps)) B ∧
            KernelTail (M * (K * eps ^ P₀)) ζ B

/-- **Leaf 4A-D** (JR (D); direct-endpoint-response §3; PD §8 (25), (33)–(35)).
`H_φ = a + O(ε⁻¹ e^{αx})` for every small input weight `α`, and the coarse tail
`|H_φ| ≤ K ε² e^{ζx}` (PD (34) with `C ≍ ε²`). -/
def DirectTerm : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ ηD : ℝ, 0 < ηD ∧ ∀ η, 0 < η → η ≤ ηD →
      ∃ αD : ℝ, 0 < αD ∧ ∀ α ζ : ℝ, 0 < α → α ≤ αD → 0 < ζ → ∃ K e0 : ℝ,
        ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν → ∀ M ψ, OutTest η M ψ →
          (∃ a : ℝ, ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
            |directKernel eps ν ψ x - a| ≤ M * (K / eps) * Real.exp (α * x)) ∧
          KernelTail (M * (K * eps ^ 2)) ζ (directKernel eps ν ψ)

/-- **Leaf 4A-P** (JR (P); PD §3, §5, §6, §9, using (U)).  With a rate `ε^{-β}`, `β > 1/2`
(the sources give `log³ε/ε`): `J_A`, `J_V` minus an affine function and `J_φ` minus a
quadratic are `O(ε^{-β} e^{αx})` a.e., for every small input weight `α`; the compensating
coefficients are polynomial in `ε` (JR §4, paragraph before (T)). -/
def PointwiseSmall : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ β : ℝ, 1 / 2 < β ∧ ∃ P₁ : ℕ, ∃ ηP : ℝ, 0 < ηP ∧ ∃ αP : ℝ, 0 < αP ∧
      ∀ α, 0 < α → α ≤ αP → ∃ K e0 : ℝ,
        ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν →
          (∃ l₀ l₁ : ℝ, |l₁| ≤ K * eps ^ P₁ ∧ ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
            |lawJA eps ν x - (l₀ + l₁ * x)| ≤ K * eps ^ (-β) * Real.exp (α * x)) ∧
          (∃ l₀ l₁ : ℝ, |l₁| ≤ K * eps ^ P₁ ∧ ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
            |lawJV eps ν x - (l₀ + l₁ * x)| ≤ K * eps ^ (-β) * Real.exp (α * x)) ∧
          ∀ M ψ, OutTest ηP M ψ → ∃ l₀ l₁ l₂ : ℝ, |l₁| + |l₂| ≤ M * (K * eps ^ P₁) ∧
            ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
              |outJ eps ν ψ x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤
                M * (K * eps ^ (-β)) * Real.exp (α * x)

/-- **Leaf 4A-Q** (JR (Q) input; PD §7 (23) and PD §8.3 (35), using (U)): the response of the
output test to the fixed two-moment direction `quadDir` is `O(M)`. -/
def QuadResponse : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ ηQ : ℝ, 0 < ηQ ∧ ∃ K e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν →
      ∀ M ψ, OutTest ηQ M ψ → |∫ x, outJ eps ν ψ x * quadDir x| ≤ M * K

/-- **Leaf 4A-κ** (JR §3, "系数有统一界"; PD (38)): `|E[Y φ'(Y)]| ≤ K M`. -/
def KappaBound : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ ηk : ℝ, 0 < ηk ∧ ∃ K e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν, RegLaw D θ vlo vhi ν →
      ∀ M ψ, OutTest ηk M ψ → |outKappa eps ν ψ| ≤ M * K

end

end PGM
