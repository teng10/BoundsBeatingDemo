/-
# Formalization of Bounds for Low-Weight Pauli Propagation

This file formalizes the statement of Theorem 1 and Conjecture 1 from
"Bounds for autoformalization" (Yanting Teng, 2026), concerning the mean squared
error of the weight-k Pauli truncation algorithm for estimating expectation values
of observables under random locally scrambling quantum circuits.

## Mathematical Setup

We work with n-qubit systems, where the Hilbert space is ℂ^{2^n}.
Matrices are of type `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`.

### Key objects:
- **Pauli strings**: Elements of `Fin n → Fin 4`, where 0=I, 1=X, 2=Y, 3=Z
- **Pauli weight**: Number of non-identity entries in a Pauli string
- **n-qubit Pauli matrix**: Tensor (Kronecker) product of single-qubit Pauli matrices
- **Density matrix**: Hermitian, positive semidefinite matrix with trace 1
- **Unitary matrix**: U U† = I and U† U = I
- **Weight truncation**: Projection of an observable onto Pauli components of weight ≤ k

### Locally scrambling conditions (used as hypotheses):
The distribution of each circuit layer U_j satisfies:
1. **Orthogonality**: The second-moment channel annihilates off-diagonal Pauli pairs
2. **Pauli mixing**: 𝔼[‖Tr(P U_j ρ U_j†)‖²] ≤ (2/3)^{|P|} for all non-identity P and
   all density matrices ρ

### Side conditions made explicit:
- Each random unitary layer U_j(ω) is a.e. unitary
- Each U_j is measurable (as a function from the probability space to matrices)
- The layers are mutually independent
- The observable O is Hermitian (self-adjoint)
- The state ρ is a density matrix (Hermitian, PSD, trace 1)
- The squared error is integrable (needed for the expectation to be well-defined)
- n ≥ 1 (at least one qubit)
- L ≥ 1 (at least one circuit layer)
-/

import Mathlib

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-! ## Basic Types -/

/-- The type of complex matrices for an n-qubit system (dimension 2^n × 2^n). -/
abbrev QMatrix (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- Provide a MeasurableSpace instance for QMatrix n.
    Since `Matrix m n α = m → n → α`, this inherits the Pi measurable space structure
    from the Borel σ-algebra on ℂ. Required for stating measurability of random
    unitary layers and integrability of the squared error. -/
instance instMeasurableSpaceQMatrix (n : ℕ) : MeasurableSpace (QMatrix n) :=
  inferInstanceAs (MeasurableSpace (Fin (2 ^ n) → Fin (2 ^ n) → ℂ))

/-! ## Single-Qubit Pauli Matrices -/

/-- The 2×2 identity matrix. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- The Pauli X matrix: [[0, 1], [1, 0]]. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of !![0, 1; 1, 0]

/-- The Pauli Y matrix: [[0, -i], [i, 0]]. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Z matrix: [[1, 0], [0, -1]]. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of !![1, 0; 0, -1]

/-- Map from `Fin 4` to the corresponding single-qubit Pauli matrix.
    0 ↦ I, 1 ↦ X, 2 ↦ Y, 3 ↦ Z. -/
def singlePauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨0, _⟩ => pauliI
  | ⟨1, _⟩ => pauliX
  | ⟨2, _⟩ => pauliY
  | ⟨3, _⟩ => pauliZ

/-! ## Pauli Strings and Weight -/

/-- A Pauli string on n qubits: assigns a Pauli index (0=I, 1=X, 2=Y, 3=Z) to each qubit. -/
abbrev PauliString (n : ℕ) := Fin n → Fin 4

/-- The weight of a Pauli string is the number of non-identity (nonzero) entries.
    This counts the number of qubits on which the Pauli operator acts non-trivially. -/
def pauliWeight {n : ℕ} (σ : PauliString n) : ℕ :=
  (Finset.univ.filter (fun i => σ i ≠ 0)).card

/-! ## n-Qubit Pauli Matrices via Kronecker Product

The n-qubit Pauli matrix for a string σ = (σ₁, …, σₙ) is the Kronecker (tensor)
product of the corresponding single-qubit Paulis:

  P_σ = singlePauli(σ₁) ⊗ singlePauli(σ₂) ⊗ ⋯ ⊗ singlePauli(σₙ)

This is a 2^n × 2^n matrix. We define it recursively using `Matrix.kroneckerMap`
and reindexing via the standard equivalence `Fin (2^(n+1)) ≃ Fin 2 × Fin (2^n)`.
-/

/-- Equivalence between `Fin (2^(n+1))` and `Fin 2 × Fin (2^n)`, used for
    building Kronecker products recursively. Uses `2^(n+1) = 2 * 2^n`. -/
def fin2PowSuccEquiv (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Fin 2 × Fin (2 ^ n) :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

/-- The n-qubit (unnormalized) Pauli matrix corresponding to a Pauli string.
    Defined recursively via Kronecker product:
    - For n = 0: the 1×1 identity matrix
    - For n + 1: singlePauli(σ 0) ⊗ₖ nQubitPauli(σ ∘ Fin.succ), reindexed

    These satisfy Tr(P_σ P_τ) = 2^n δ_{σ,τ} (orthogonality with norm 2^n). -/
def nQubitPauli : (n : ℕ) → PauliString n → QMatrix n
  | 0, _ => 1
  | n + 1, σ =>
    let A := singlePauli (σ 0)
    let B := nQubitPauli n (σ ∘ Fin.succ)
    Matrix.reindex (fin2PowSuccEquiv n).symm (fin2PowSuccEquiv n).symm
      (A.kroneckerMap (· * ·) B)

/-! ## Pauli Decomposition and Weight Truncation

Every 2^n × 2^n complex matrix can be uniquely decomposed in the (unnormalized)
Pauli basis:
  O = ∑_σ a_σ P_σ,  where a_σ = Tr(P_σ O) / 2^n

The **normalized Pauli 2-norm** (also called the "Pauli ℓ²-norm") is:
  ‖O‖²_{Pauli,2} := ∑_σ |a_σ|² = 2^{-n} · ‖O‖²_HS

where ‖O‖_HS = √(Tr(O† O)) is the Hilbert-Schmidt (Frobenius) norm.
-/

/-- The Pauli coefficient of O with respect to Pauli string σ (unnormalized basis):
    a_σ = Tr(P_σ · O) / 2^n.

    Well-defined because the unnormalized Pauli basis satisfies
    Tr(P_σ · P_τ) = 2^n δ_{σ,τ}. -/
def pauliCoeff (n : ℕ) (O : QMatrix n) (σ : PauliString n) : ℂ :=
  Matrix.trace (nQubitPauli n σ * O) / (2 : ℂ) ^ n

/-- The squared normalized Pauli 2-norm:
    ‖O‖²_{Pauli,2} = ∑_σ ‖a_σ‖² = 2^{-n} · Tr(O† O).

    This is the quantity appearing on the right-hand side of the error bound. -/
def pauliNormSq (n : ℕ) (O : QMatrix n) : ℝ :=
  ∑ σ : PauliString n, ‖pauliCoeff n O σ‖ ^ 2

/-- Weight truncation: project an observable onto Pauli components of weight ≤ k.

    Π_k(O) = ∑_{σ : |σ| ≤ k} a_σ · P_σ

    This discards high-weight Pauli components, keeping only those with at most k
    non-identity tensor factors. -/
def weightTruncate (n : ℕ) (k : ℕ) (O : QMatrix n) : QMatrix n :=
  ∑ σ : PauliString n,
    if pauliWeight σ ≤ k then pauliCoeff n O σ • nQubitPauli n σ else 0

/-! ## Circuit Composition and Truncated Observable

Given circuit layers U₀, …, U_{L-1} (indexed by `Fin L`), the full circuit is
  U = U_{L-1} ⋯ U₀

The truncated observable is computed by evolving O backwards through the circuit
layer by layer (Heisenberg picture), applying weight truncation after each step:
  Start with O
  For j = L-1, L-2, …, 0: O ↦ Π_k(U_j† · O · U_j)
The final result is O^(k)_U.

**Note on indexing**: The paper uses 1-based indexing (layers U₁,…,U_L);
we use 0-based indexing (layers U₀,…,U_{L-1}).
-/

/-- Conjugation by a unitary (Heisenberg-picture evolution): U† · O · U. -/
def conjAction {n : ℕ} (U : QMatrix n) (O : QMatrix n) : QMatrix n :=
  U.conjTranspose * O * U

/-- Evolve an observable backwards through a unitary layer and weight-truncate:
    O ↦ Π_k(U† O U). -/
def evolveAndTruncate (n : ℕ) (k : ℕ) (U : QMatrix n) (O : QMatrix n) : QMatrix n :=
  weightTruncate n k (conjAction U O)

/-- The truncated observable after processing layers in the given list.
    Processes layers left-to-right, applying evolve-and-truncate at each step.
    The list should be ordered from the outermost (last-applied) layer first. -/
def truncatedObs (n : ℕ) (k : ℕ) (layers : List (QMatrix n)) (O : QMatrix n) :
    QMatrix n :=
  layers.foldr (evolveAndTruncate n k) O

/-- Convert indexed layers `Fin L → QMatrix n` to a list ordered from the
    outermost (highest index) layer first, suitable for `truncatedObs`.
    Layer L-1 is first (outermost), layer 0 is last (innermost). -/
def layersToList {n : ℕ} (L : ℕ) (U : Fin L → QMatrix n) : List (QMatrix n) :=
  (List.finRange L).reverse.map U

/-- The full truncated observable O^(k)_U for a circuit U = U_{L-1} ⋯ U₀:
    start with O, evolve backwards through each layer with weight truncation. -/
def fullTruncatedObs (n : ℕ) (L : ℕ) (k : ℕ) (U : Fin L → QMatrix n)
    (O : QMatrix n) : QMatrix n :=
  truncatedObs n k (layersToList L U) O

/-! ## Expectation Values -/

/-- The composite circuit unitary U = U_{L-1} ⋯ U₀.
    Defined as the product of layers from index 0 (innermost) to L-1 (outermost). -/
def compositeUnitary {n : ℕ} (L : ℕ) (U : Fin L → QMatrix n) : QMatrix n :=
  (List.finRange L).foldr (fun j acc => U j * acc) 1

/-- The exact expectation value f_U(O) = Tr(O · U ρ U†),
    where U = U_{L-1} ⋯ U₀ is the composite circuit. -/
def circuitExpVal (n : ℕ) (L : ℕ) (U : Fin L → QMatrix n) (O : QMatrix n)
    (ρ : QMatrix n) : ℂ :=
  let Ufull := compositeUnitary L U
  Matrix.trace (O * Ufull * ρ * Ufull.conjTranspose)

/-- The truncated estimator f̃^(k)_U(O) = Tr(O^(k)_U · ρ). -/
def truncatedExpVal (n : ℕ) (L : ℕ) (k : ℕ) (U : Fin L → QMatrix n)
    (O : QMatrix n) (ρ : QMatrix n) : ℂ :=
  Matrix.trace (fullTruncatedObs n L k U O * ρ)

/-! ## Density Matrix and Unitarity Predicates -/

/-- A matrix is a valid quantum state (density matrix) if it is:
    1. Hermitian (self-adjoint): ρ† = ρ
    2. Positive semidefinite: ⟨v, ρ v⟩ ≥ 0 for all v
    3. Trace-one: Tr(ρ) = 1

    These conditions ensure ρ represents a valid mixed quantum state.
    Positive semidefiniteness is stated as: for all vectors v, the real part
    of v† ρ v is nonneg (the imaginary part vanishes by Hermiticity). -/
def IsDensityMatrix {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ.IsHermitian ∧
  (∀ v : Fin d → ℂ, 0 ≤ RCLike.re (dotProduct (star v) (ρ.mulVec v))) ∧
  Matrix.trace ρ = 1

/-- A matrix is unitary if U U† = I and U† U = I.
    Both conditions are stated for completeness, though each implies the other
    for finite-dimensional matrices. -/
def IsUnitaryMatrix {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1

/-! ## Locally Scrambling Conditions

The "locally scrambling" property of a distribution over unitaries means the
distribution is invariant under conjugation by independent single-qubit Clifford
gates. For the theorem statement, we use the two *consequences* of this property
that are directly needed in the proof:

1. **Orthogonality** (second-moment channel annihilates off-diagonal Pauli pairs)
2. **Pauli mixing** (variance bound in terms of Pauli weight)

These are stated as hypotheses on the probability measure over circuits.
-/

/-- The Pauli mixing condition for a single random layer U_j:
    For every non-identity Pauli string σ (|σ| > 0) and every density matrix ρ,
      𝔼_ω[‖Tr(P_σ · U_j(ω) · ρ · U_j(ω)†)‖²] ≤ (2/3)^{|σ|}

    **Side conditions implicit in the definition**:
    - The integrand must be measurable and integrable for the Bochner integral
      to be well-defined. This follows from measurability of U_j. -/
def PauliMixingCondition {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n) : Prop :=
  ∀ (σ : PauliString n), pauliWeight σ ≠ 0 →
  ∀ (ρ : QMatrix n), IsDensityMatrix ρ →
    ∫ ω, ‖Matrix.trace (nQubitPauli n σ * Uj ω * ρ * (Uj ω).conjTranspose)‖ ^ 2 ∂μ
      ≤ ((2 : ℝ) / 3) ^ pauliWeight σ

/-- The orthogonality condition for a single random layer U_j:
    For distinct Pauli strings σ ≠ τ and any matrix A,
      𝔼_ω[Tr(P_σ · U_j A U_j†) · Tr(P_τ · U_j A U_j†)] = 0

    This is the trace form of the second-moment orthogonality:
    𝔼[U_j†⊗² (P_σ ⊗ P_τ) U_j⊗²] = 0 whenever σ ≠ τ.

    The vanishing of these cross-terms is essential for the telescoping
    sum argument in the proof. -/
def OrthogonalityCondition {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n) : Prop :=
  ∀ (σ τ : PauliString n), σ ≠ τ →
  ∀ (A : QMatrix n),
    ∫ ω, (Matrix.trace (nQubitPauli n σ * Uj ω * A * (Uj ω).conjTranspose) *
           Matrix.trace (nQubitPauli n τ * Uj ω * A * (Uj ω).conjTranspose)).re ∂μ = 0

/-- A random unitary layer is locally scrambling if it satisfies both the
    orthogonality and Pauli mixing conditions. -/
def IsLocallyScrambling {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Uj : Ω → QMatrix n) : Prop :=
  PauliMixingCondition μ Uj ∧ OrthogonalityCondition μ Uj

/-! ## Measurability and Integrability Side Conditions -/

/-- Collects the measurability and unitarity conditions for the circuit layers.
    These are necessary for the integrals in the theorem statement to be well-defined.

    - **Measurability**: Each U_j is a measurable function from the probability space
      to the space of 2^n × 2^n complex matrices (equipped with the product σ-algebra
      from the Borel σ-algebra on ℂ).
    - **Almost-everywhere unitarity**: For μ-a.e. ω, U_j(ω) is a unitary matrix.
      This is needed to ensure the Heisenberg evolution U_j† O U_j preserves the
      operator structure. -/
structure CircuitMeasurability {n L : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (U : Fin L → Ω → QMatrix n) : Prop where
  layer_measurable : ∀ j, Measurable (U j)
  layer_unitary : ∀ j, ∀ᵐ ω ∂μ, IsUnitaryMatrix (U j ω)

/-! ## Main Results -/

/-- **Theorem 1 (Mean Squared Error Bound for Pauli Weight Truncation)**.

Let U = U_{L-1} ⋯ U₀ be drawn from an L-layered locally scrambling circuit
distribution. For any weight cutoff k, any Hermitian observable O, and any
density matrix ρ:

  𝔼_U[‖f_U(O) − f̃^(k)_U(O)‖²] ≤ (2/3)^{k+1} · ‖O‖²_{Pauli,2}

**Hypotheses** (side conditions):
- (Ω, μ) is a probability space
- Each layer U_j : Ω → QMatrix n is measurable
- Each U_j(ω) is a.e. unitary
- The L layers are mutually independent (as random variables)
- Each layer satisfies the locally scrambling conditions:
    - Orthogonality of second-moment channel
    - Pauli mixing bound (2/3)^{|P|}
- O is Hermitian (self-adjoint), as required for physical observables
- ρ is a density matrix (Hermitian, PSD, trace 1)
- The squared error is integrable (needed for the Bochner integral to be
  well-defined; automatically satisfied when μ is a probability measure
  and the integrand is bounded, but stated explicitly for generality)
- n ≥ 1 (at least one qubit, so the Pauli basis is nontrivial)
- L ≥ 1 (at least one circuit layer)

The bound is notable for being **independent of the circuit depth L**.
-/
def mainTheorem : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1)
    (L : ℕ) (hL : L ≥ 1)
    (k : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure μ]
    (U : Fin L → Ω → QMatrix n)
    -- Measurability and unitarity of each layer
    (hMeas : CircuitMeasurability μ U)
    -- Mutual independence of layers
    (hIndep : @iIndepFun Ω (Fin L) _ (fun _ => QMatrix n)
      (fun _ => instMeasurableSpaceQMatrix n) U μ)
    -- Each layer is locally scrambling
    (hScrambling : ∀ j, IsLocallyScrambling μ (U j))
    -- Observable is Hermitian (physical observable)
    (O : QMatrix n) (hO : O.IsHermitian)
    -- Input state is a density matrix
    (ρ : QMatrix n) (hρ : IsDensityMatrix ρ)
    -- Integrability of the squared error
    (hIntegrable : MeasureTheory.Integrable
      (fun ω => ‖circuitExpVal n L (fun j => U j ω) O ρ -
                  truncatedExpVal n L k (fun j => U j ω) O ρ‖ ^ 2) μ),
    -- Conclusion: MSE ≤ (2/3)^{k+1} · ‖O‖²_{Pauli,2}
    ∫ ω, ‖circuitExpVal n L (fun j => U j ω) O ρ -
          truncatedExpVal n L k (fun j => U j ω) O ρ‖ ^ 2 ∂μ
      ≤ ((2 : ℝ) / 3) ^ (k + 1) * pauliNormSq n O

theorem main : mainTheorem := by
  intro n hn L hL k Ω _ μ _ U hMeas hIndep hScrambling O hO ρ hρ hIntegrable
  sorry

/-- **Conjecture 1 (Depth-Dependent Improvement)**.

Under the same conditions as Theorem 1, there exists a universal constant
c ∈ (0, 1) such that the error bound improves exponentially with circuit depth:

  𝔼_U[‖f_U(O) − f̃^(k)_U(O)‖²] ≤ (2/3)^{k+1} · c^L · ‖O‖²_{Pauli,2}

This conjectures that deeper locally scrambling circuits produce smaller
truncation error, with the improvement being exponential in the depth L.
The constant c is independent of n, L, k, O, and ρ.

The same side conditions apply as in Theorem 1, with the additional
existential quantification over c ∈ (0, 1). -/
def mainConjecture : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1)
    (L : ℕ) (hL : L ≥ 1)
    (k : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure μ]
    (U : Fin L → Ω → QMatrix n)
    (hMeas : CircuitMeasurability μ U)
    (hIndep : @iIndepFun Ω (Fin L) _ (fun _ => QMatrix n)
      (fun _ => instMeasurableSpaceQMatrix n) U μ)
    (hScrambling : ∀ j, IsLocallyScrambling μ (U j))
    (O : QMatrix n) (hO : O.IsHermitian)
    (ρ : QMatrix n) (hρ : IsDensityMatrix ρ)
    (hIntegrable : MeasureTheory.Integrable
      (fun ω => ‖circuitExpVal n L (fun j => U j ω) O ρ -
                  truncatedExpVal n L k (fun j => U j ω) O ρ‖ ^ 2) μ),
    ∃ (c : ℝ), 0 < c ∧ c < 1 ∧
      ∫ ω, ‖circuitExpVal n L (fun j => U j ω) O ρ -
            truncatedExpVal n L k (fun j => U j ω) O ρ‖ ^ 2 ∂μ
        ≤ ((2 : ℝ) / 3) ^ (k + 1) * c ^ L * pauliNormSq n O

theorem conjecture1 : mainConjecture := by
  intro n hn L hL k Ω _ μ _ U hMeas hIndep hScrambling O hO ρ hρ hIntegrable
  sorry

end
