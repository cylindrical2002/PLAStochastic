import PLAStochastic.Index.CEPS.ZeroOrder.Main
import PLAStochastic.Index.CEPS.Jets.JF

/-!
# The single remaining kernel-jet premise of P-CEPS

`CepsKernelJetRepresentation` is the only input still needed for the unconditional all-order
expansion of `gepC ε / ε²` (`Final.Main`). It consists of

* the three normal premises of `Glue/Defs` for the fixed normal transform `cepsNormalGn` and its
  slope `cepsNormalDn` (`CepsNormalMeanExpansion`, `CepsNormalLowExpansion`,
  `CepsNormalCoeffReg`), read through the X8 jets `cepsJetLaw`;
* a finite Taylor representation of the mean coefficients `Cs k` and of the low-band
  coefficients `Gk j` (with every frequency derivative) in finitely many X8 jet coordinates
  around the reference jets `cepsJetLaw cepsLambda`, in the box form of `CepsT3`.

Everything else (S-9, T1-mid, the fixed-window Taylor bound, C-16, JF, the WP11a glue and the
Taylor composition through `cepsLowCoeff`) is proved. The premises only read `J.jet`; they are
stated for the jet-only data `cepsKernelJetBase`.
-/

namespace PGM

noncomputable section

/-- Jet-only data: the X8 jet map and JF coefficients. The other fields are not read by the
normal premises of `Glue/Defs`. -/
def cepsKernelJetBase : CepsJetData where
  jet := cepsJetLaw
  phi := fun _ _ _ => 0
  scal := fun _ _ => 0
  dim := fun _ => 0
  phiTaylor := fun _ _ _ => 0
  scalTaylor := fun _ _ => 0
  jetCoeff := cepsJetCoeff

/-- **The remaining kernel-jet premise (C-14).** There are mean coefficients `Cs k p` and
low-band coefficients `Gk j p y = Ĝ_j(iy; p)` such that

1. `-∂_z Ĝ(b, 0) = ∑ bᵏ Cs k (J ν) + O(h^{P+1})`, `Ĝ(b, iy) = ∑ bʲ Gk j (J ν) y + O(…)` on
   `|y| ≤ R ε²` and the `Gk j (J ν)` are `C^{N+1}` with polynomial bounds, uniformly over the
   input class (`Glue/Defs`, for `cepsNormalDn`, `cepsNormalGn`, `J = cepsJetLaw`);
2. every `Cs k` has, in some finite number `d` of X8 coordinates, Taylor coefficients `T α`
   with box remainders `K |p - p₀|^{N+1}` near `p₀ = cepsJetLaw cepsLambda`;
3. every `Gk j` has smooth Taylor coefficient functions `T α` whose derivatives decay
   stretched-exponentially, and for every frequency derivative order `m` the box Taylor
   remainder of `∂_yᵐ Gk j p y` is `K (1+|y|)ᵉ e^{-c√|y|} |p - p₀|^{N+1}`. -/
def CepsKernelJetRepresentation : Prop :=
  ∃ (Cs : ℕ → (ℕ → ℝ) → ℝ) (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ),
    CepsNormalMeanExpansion cepsKernelJetBase cepsNormalDn Cs ∧
    CepsNormalLowExpansion cepsKernelJetBase cepsNormalGn Gk ∧
    CepsNormalCoeffReg cepsKernelJetBase Gk ∧
    (∀ k : ℕ, ∃ d : ℕ, ∃ T : (Fin d → ℕ) → ℝ, ∀ N : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧
      ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ ρ) →
        |Cs k p - ∑ α ∈ cepsTaylorBox d N,
            T α * cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α| ≤
          K * (∑ i : Fin d, |p i - cepsJetLaw cepsLambda i|) ^ (N + 1)) ∧
    (∀ j : ℕ, ∃ d : ℕ, ∃ T : (Fin d → ℕ) → ℝ → ℂ,
      (∀ (α : Fin d → ℕ) (n : ℕ), ContDiff ℝ n (T α)) ∧
      (∀ (α : Fin d → ℕ) (m : ℕ), ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y : ℝ,
        ‖iteratedDeriv m (T α) y‖ ≤ K * cepsStretchedWeight c e y) ∧
      ∀ m N : ℕ, ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (y : ℝ) (p : ℕ → ℝ),
        (∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ ρ) →
          ‖iteratedDeriv m (Gk j p) y - ∑ α ∈ cepsTaylorBox d N, iteratedDeriv m (T α) y *
              (cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α : ℂ)‖ ≤
            K * cepsStretchedWeight c e y *
              (∑ i : Fin d, |p i - cepsJetLaw cepsLambda i|) ^ (N + 1))

end

end PGM
