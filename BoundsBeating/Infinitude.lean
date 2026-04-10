import Mathlib

def foo: Nat := 42

lemma two_le_fac_add_one (n : Nat) : 2 ≤ n.factorial + 1 := by
  cases' n with n hn
  · simp
  sorry
