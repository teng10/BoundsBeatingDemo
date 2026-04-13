/-
# Formalization of Bounds for Low-Weight Pauli Propagation

This file formalizes the definitions and statements from
"Bounds Beating: Pauli Weight Truncation Errors" (Teng, after Angrisani et al. 2025).

## Mathematical Setup

We work with n-qubit systems, where the Hilbert space is ℂ^{2^n}.
Matrices are of type `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`.
-/

import Mathlib

/- notation from lean-quantumInfo -/
abbrev Qubit := Fin 2
notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

noncomputable section

open scoped BigOperators
open Matrix Complex MeasureTheory ProbabilityTheory

/-! ## Basic Types -/

/-- The type of complex matrices for an n-qubit system (dimension 2^n × 2^n). -/
abbrev QMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

instance instMeasurableSpaceQMatrix (n : ℕ) : MeasurableSpace (QMatrix n) :=
  inferInstanceAs (MeasurableSpace (Fin (2 ^ n) → Fin (2 ^ n) → ℂ))

/-! ## Single-Qubit Pauli Matrices -/

def pauliI : Matrix Qubit Qubit ℂ :=
!![1, 0;
   0, 1]

def pauliX : Matrix Qubit Qubit ℂ :=
!![0, 1;
   1, 0]

def pauliZ : Matrix Qubit Qubit ℂ :=
!![1,  0;
   0, -1]

def pauliY : Matrix Qubit Qubit ℂ :=
!![0, -Complex.I;
   Complex.I, 0]

/-- Map from `Fin 4` to the corresponding single-qubit Pauli matrix.
    0 ↦ I, 1 ↦ X, 2 ↦ Y, 3 ↦ Z. -/
def singlePauli : Fin 4 → Matrix Qubit Qubit ℂ
  | ⟨0, _⟩ => pauliI
  | ⟨1, _⟩ => pauliX
  | ⟨2, _⟩ => pauliY
  | ⟨3, _⟩ => pauliZ

/-! ## Pauli Strings and Weight -/

/-- A Pauli string on n qubits: assigns a Pauli index (0=I, 1=X, 2=Y, 3=Z)
    to each qubit. -/
abbrev PauliString (n : ℕ) := Fin n → Fin 4

/-- The weight of a Pauli string is the number of non-identity entries.
    This counts the number of qubits on which the Pauli operator acts
    non-trivially. -/
def pauliWeight {n : ℕ} (σ : PauliString n) : ℕ :=
  (Finset.univ.filter (fun i => σ i ≠ 0)).card

/-! ## n-Qubit Pauli Matrices via Kronecker Product -/

/-- Equivalence between `Fin (2^(n+1))` and `Qubit × Fin (2^n)`. -/
def fin2PowSuccEquiv (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Qubit × Fin (2 ^ n) :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

/-- The n-qubit (unnormalized) Pauli matrix corresponding to a Pauli string.
    These satisfy Tr(P_σ P_τ) = 2^n δ_{σ,τ}. -/
def nQubitPauli : (n : ℕ) → PauliString n → QMatrix n
  | 0, _ => 1
  | n + 1, σ =>
    let A := singlePauli (σ 0)
    let B := nQubitPauli n (σ ∘ Fin.succ)
    Matrix.reindex (fin2PowSuccEquiv n).symm (fin2PowSuccEquiv n).symm
      (A.kroneckerMap (· * ·) B)

/-! ## Pauli Group and Normalized Basis (blueprint: leanok) -/

/-- The n-qubit Pauli group 𝒫_n, consisting of all n-fold tensor products
    of {I, X, Y, Z}. The weight |P| is the number of non-identity factors.
    We represent it as the type of Pauli strings together with the map
    to matrices. -/
structure PauliGroup (n : ℕ) where
  /-- The underlying Pauli string -/
  str : PauliString n
  deriving DecidableEq

/-- The weight of a Pauli group element. -/
def PauliGroup.weight {n : ℕ} (P : PauliGroup n) : ℕ :=
  pauliWeight P.str

/-- The matrix representation of a Pauli group element. -/
def PauliGroup.toMatrix {n : ℕ} (P : PauliGroup n) : QMatrix n :=
  nQubitPauli n P.str

/-- The normalized Pauli basis: P̃_σ = P_σ / √(2^n).
    Its elements satisfy Tr(s · t) = δ_{s,t}. -/
def normalizedPauliBasis (n : ℕ) (σ : PauliString n) : QMatrix n :=
  ((Real.sqrt (2 ^ n : ℝ) : ℂ)⁻¹) • nQubitPauli n σ

/-! ## Pauli Norm (blueprint: leanok) -/

/-- The Pauli coefficient of O with respect to Pauli string σ:
    a_σ = Tr(P̃_σ · O) for the normalized basis. -/
def pauliCoeff (n : ℕ) (O : QMatrix n) (σ : PauliString n) : ℂ :=
  Matrix.trace (normalizedPauliBasis n σ * O)

/-- The squared normalized Pauli 2-norm:
    ‖O‖²_{Pauli,2} = ∑_σ |a_σ|² = 2^{-n} · Tr(O† O). -/
def pauliNormSq (n : ℕ) (O : QMatrix n) : ℝ :=
  ∑ σ : PauliString n, ‖pauliCoeff n O σ‖ ^ 2

/-- The normalized Pauli 2-norm:
    ‖O‖_{Pauli,2} = (∑_σ |a_σ|²)^{1/2} = 2^{-n/2} · ‖O‖₂. -/
def pauliNorm (n : ℕ) (O : QMatrix n) : ℝ :=
  Real.sqrt (pauliNormSq n O)

/-! ## Density Matrix and Unitarity Predicates -/

/-- A matrix is a valid quantum state (density matrix). -/
def IsDensityMatrix {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ.IsHermitian ∧
  (∀ v : Fin d → ℂ, 0 ≤ RCLike.re (dotProduct (star v) (ρ.mulVec v))) ∧
  Matrix.trace ρ = 1

/-- A matrix is unitary if U U† = I and U† U = I. -/
def IsUnitaryMatrix {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1

/-! ## Locally Scrambling (blueprint: leanok) -/

/-- The Pauli mixing condition for a single random layer U_j:
    For every non-identity Pauli P and every density matrix ρ,
      𝔼_ω[|Tr(P · U_j(ω) ρ U_j(ω)†)|²] ≤ (2/3)^{|P|}. -/
def PauliMixingCondition {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n) : Prop :=
  ∀ (σ : PauliString n), pauliWeight σ ≠ 0 →
  ∀ (ρ : QMatrix n), IsDensityMatrix ρ →
    ∫ ω, ‖Matrix.trace (nQubitPauli n σ * Uj ω * ρ * (Uj ω).conjTranspose)‖ ^ 2 ∂μ
      ≤ ((2 : ℝ) / 3) ^ pauliWeight σ

/-- The orthogonality condition for a single random layer U_j:
    For distinct Pauli strings σ ≠ τ,
      𝔼_ω[Tr(P_σ · U_j A U_j†) · Tr(P_τ · U_j A U_j†)] = 0. -/
def OrthogonalityCondition {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n) : Prop :=
  ∀ (σ τ : PauliString n), σ ≠ τ →
  ∀ (A : QMatrix n),
    ∫ ω, (Matrix.trace (nQubitPauli n σ * Uj ω * A * (Uj ω).conjTranspose) *
           Matrix.trace (nQubitPauli n τ * Uj ω * A * (Uj ω).conjTranspose)).re ∂μ = 0

/-- A random unitary layer is locally scrambling if its distribution is
    invariant under conjugation by independent single-qubit Clifford gates.
    This implies both orthogonality and Pauli mixing. -/
def LocallyScrambling {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n) : Prop :=
  PauliMixingCondition μ Uj ∧ OrthogonalityCondition μ Uj

/-! ## Circuit Measurability -/

structure CircuitMeasurability {n L : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (U : Fin L → Ω → QMatrix n) : Prop where
  layer_measurable : ∀ j, Measurable (U j)
  layer_unitary : ∀ j, ∀ᵐ ω ∂μ, IsUnitaryMatrix (U j ω)

/-! ## Weight Truncation and Circuit Composition -/

/-- Weight truncation: project an observable onto Pauli components of weight ≤ k. -/
def weightTruncate (n : ℕ) (k : ℕ) (O : QMatrix n) : QMatrix n :=
  ∑ σ : PauliString n,
    if pauliWeight σ ≤ k then pauliCoeff n O σ • normalizedPauliBasis n σ else 0

/-- Conjugation by a unitary (Heisenberg-picture evolution): U† · O · U. -/
def conjAction {n : ℕ} (U : QMatrix n) (O : QMatrix n) : QMatrix n :=
  U.conjTranspose * O * U

/-- Evolve through a unitary layer and weight-truncate: O ↦ Π_k(U† O U). -/
def evolveAndTruncate (n : ℕ) (k : ℕ) (U : QMatrix n) (O : QMatrix n) : QMatrix n :=
  weightTruncate n k (conjAction U O)

/-! ## Truncated Observable (blueprint: leanok) -/

/-- The truncated observable sequence. Given a circuit U = U_L ⋯ U_1,
    define O_{L+1} := O and recursively
      O_j := ∑_{|s|≤k} Tr[U_{j+1}† O_{j+1} U_{j+1} · s] · s.
    The weight-k truncated observable is O^(k)_U := O_1. -/
def truncatedObservable (n : ℕ) (L : ℕ) (k : ℕ) (U : Fin L → QMatrix n)
    (O : QMatrix n) : QMatrix n :=
  let layers := ((List.finRange L).reverse.map U)
  layers.foldr (evolveAndTruncate n k) O

/-! ## Truncated Estimator (blueprint: leanok) -/

/-- The composite circuit unitary U = U_{L-1} ⋯ U₀. -/
def compositeUnitary {n : ℕ} (L : ℕ) (U : Fin L → QMatrix n) : QMatrix n :=
  (List.finRange L).foldr (fun j acc => U j * acc) 1

/-- The exact expectation value f_U(O) = Tr(O · U ρ U†). -/
def circuitExpVal (n : ℕ) (L : ℕ) (U : Fin L → QMatrix n) (O : QMatrix n)
    (ρ : QMatrix n) : ℂ :=
  let Ufull := compositeUnitary L U
  Matrix.trace (O * Ufull * ρ * Ufull.conjTranspose)

/-- The truncated estimator f̃^(k)_U(O) = Tr(O^(k)_U · ρ).
    The true expectation is f_U(O) = Tr(O · U ρ U†). -/
def truncatedEstimator (n : ℕ) (L : ℕ) (k : ℕ) (U : Fin L → QMatrix n)
    (O : QMatrix n) (ρ : QMatrix n) : ℂ :=
  Matrix.trace (truncatedObservable n L k U O * ρ)

/-! ## Lemmas (blueprint: leanok) -/

/-- **Pauli orthogonality**: Under local scrambling, for P ≠ Q,
    𝔼_{U_j}[U_j†⊗² (P ⊗ Q) U_j⊗²] = 0. -/
lemma pauliOrthogonality {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n)
    (hScrambling : LocallyScrambling μ Uj)
    (σ τ : PauliString n) (hne : σ ≠ τ)
    (A : QMatrix n) :
    ∫ ω, (Matrix.trace (nQubitPauli n σ * Uj ω * A * (Uj ω).conjTranspose) *
           Matrix.trace (nQubitPauli n τ * Uj ω * A * (Uj ω).conjTranspose)).re ∂μ = 0 := by
  exact hScrambling.2 σ τ hne A

/-- **Pauli mixing inequality**: Under local scrambling, for non-identity P,
    𝔼_{U_j}[Tr(P U_j ρ U_j†)²] ≤ (2/3)^{|P|}. -/
lemma pauliMixing {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n)
    (hScrambling : LocallyScrambling μ Uj)
    (σ : PauliString n) (hw : pauliWeight σ ≠ 0)
    (ρ : QMatrix n) (hρ : IsDensityMatrix ρ) :
    ∫ ω, ‖Matrix.trace (nQubitPauli n σ * Uj ω * ρ * (Uj ω).conjTranspose)‖ ^ 2 ∂μ
      ≤ ((2 : ℝ) / 3) ^ pauliWeight σ := by
  exact hScrambling.1 σ hw ρ hρ

/-! ## Main Theorem (blueprint: leanok) -/

/-- **Theorem 1 (MSE bound — depth-independent)**.
    Let U = U_L ⋯ U_1 be drawn from an L-layered locally scrambling circuit.
    For any k ≥ 0, any observable O, and any state ρ:
      𝔼_U[(f_U(O) − f̃^(k)_U(O))²] ≤ (2/3)^{k+1} · ‖O‖²_{Pauli,2}.
    The bound is independent of the circuit depth L. -/
theorem mseBound
    (n : ℕ) (hn : n ≥ 1) (L : ℕ) (hL : L ≥ 1) (k : ℕ)
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure μ]
    (U : Fin L → Ω → QMatrix n)
    (hMeas : CircuitMeasurability μ U)
    (hIndep : @iIndepFun Ω (Fin L) _ (fun _ => QMatrix n)
      (fun _ => instMeasurableSpaceQMatrix n) U μ)
    (hScrambling : ∀ j, LocallyScrambling μ (U j))
    (O : QMatrix n) (hO : O.IsHermitian)
    (ρ : QMatrix n) (hρ : IsDensityMatrix ρ)
    (hIntegrable : MeasureTheory.Integrable
      (fun ω => ‖circuitExpVal n L (fun j => U j ω) O ρ -
                  truncatedEstimator n L k (fun j => U j ω) O ρ‖ ^ 2) μ) :
    ∫ ω, ‖circuitExpVal n L (fun j => U j ω) O ρ -
          truncatedEstimator n L k (fun j => U j ω) O ρ‖ ^ 2 ∂μ
      ≤ ((2 : ℝ) / 3) ^ (k + 1) * pauliNormSq n O := by
  sorry

end
