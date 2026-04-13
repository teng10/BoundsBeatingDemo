import BoundsBeating.Pauli_truncation

/-! # Pauli Truncation Test
- This file contains tests for the Pauli truncation functions defined in `Pauli_truncation.lean`.

- Define some example Pauli strings and test the `pauliWeight` function. -/
/-! ## Example Pauli Strings -/
def p : PauliString 3
| ⟨0, _⟩ => 1
| ⟨1, _⟩ => 0
| ⟨2, _⟩ => 3

-- p 0 = 1  -- X
-- p 1 = 0  -- I
-- p 2 = 3  -- Z
/-! ## Test `pauliWeight` -/
-- #eval pauliWeight p  -- Expected output: 2, since there are two non-identity Paulis (X and Z)
