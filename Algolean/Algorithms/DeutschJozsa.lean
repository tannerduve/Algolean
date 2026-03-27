/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.QuantumOracle

@[expose] public section

/-!
# Deutsch-Jozsa Algorithm

The Deutsch-Jozsa algorithm determines whether a boolean function
`f : Fin (2^n) → Bool` is constant (all outputs equal) or balanced
(exactly half true, half false), promised that one of these holds.
It uses exactly 1 oracle query, compared to `2^(n-1) + 1` classically.

## Main definitions

- `deutschJozsa`: The algorithm as a `Prog (QuantumQuery n) (QState n)`.
- `isConstant`: The promise that `f` is constant.
- `isBalanced`: The promise that `f` is balanced.
- `deutschJozsa_constant`: Measuring `|0⟩` has probability 1 if `f` is constant.
- `deutschJozsa_balanced`: Measuring `|0⟩` has probability 0 if `f` is balanced.
- `deutschJozsa_cost`: The algorithm uses exactly 1 oracle query.
-/

namespace Algolean

namespace Algorithms

open Prog Cslib Complex

/-! ### Promises -/

/-- `f` is constant: all outputs are equal. -/
def isConstant (f : Fin (2 ^ n) → Bool) : Prop :=
  ∀ i j, f i = f j

/-- `f` is balanced: exactly half the outputs are true. -/
def isBalanced (f : Fin (2 ^ n) → Bool) : Prop :=
  (Finset.univ.filter (fun i => f i = true)).card = 2 ^ n / 2

/-! ### Algorithm -/

/-- The Deutsch-Jozsa algorithm. Applies Hadamard to all qubits,
queries the oracle once, then applies Hadamard again. The resulting
state encodes whether `f` is constant or balanced. -/
def deutschJozsa (n : ℕ) (s : QState n) :
    Prog (QuantumQuery n) (QState n) := do
  let s₁ ← hadamardAll s
  let s₂ ← applyGate .oracle s₁
  hadamardAll s₂

/-! ### Cost -/

/-- `hadamardFrom` has zero oracle cost. -/
theorem hadamardFrom_time (k : ℕ) (s : QState n) (M : Model (QuantumQuery n) ℕ)
    (hcost : ∀ q, M.cost (QuantumQuery.hadamard q) = 0) :
    Prog.time (hadamardFrom k s) M = 0 := by
  unfold hadamardFrom
  split
  · case _ h =>
    change Prog.time ((applyGate (.hadamard ⟨k, h⟩) s).bind
      (fun s' => hadamardFrom (k + 1) s')) M = 0
    rw [Prog.time_bind, applyGate_time, hcost, zero_add]
    exact hadamardFrom_time (k + 1) _ M hcost
  · exact Prog.time_pure _ _
termination_by n - k

/-- `hadamardAll` has zero oracle cost: it only uses Hadamard gates. -/
theorem hadamardAll_time (s : QState n) (M : Model (QuantumQuery n) ℕ)
    (hcost : ∀ q, M.cost (QuantumQuery.hadamard q) = 0) :
    Prog.time (hadamardAll s) M = 0 :=
  hadamardFrom_time 0 s M hcost

/-- The Deutsch-Jozsa algorithm uses exactly 1 oracle query. -/
theorem deutschJozsa_cost (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Prog.time (deutschJozsa n (QState.initial n)) (quantumModel n f) = 1 := by
  unfold deutschJozsa
  change Prog.time ((hadamardAll (QState.initial n)).bind fun s₁ =>
    (applyGate .oracle s₁).bind fun s₂ => hadamardAll s₂) (quantumModel n f) = 1
  rw [Prog.time_bind, hadamardAll_time _ _ (fun q => rfl), zero_add,
    Prog.time_bind, applyGate_time, quantumModel_cost_oracle]
  rw [hadamardAll_time _ _ (fun q => rfl)]

/-! ### Correctness -/

/-- The final state of the Deutsch-Jozsa algorithm. -/
noncomputable def deutschJozsaFinalState (n : ℕ)
    (f : Fin (2 ^ n) → Bool) : QState n :=
  Prog.eval (deutschJozsa n (QState.initial n)) (quantumModel n f)

/-- The sign function for the oracle: `(-1)^{f(x)}`. -/
noncomputable def oracleSign (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) : ℂ :=
  if f x then -1 else 1

/-- The amplitude at `|0⟩` after the Deutsch-Jozsa algorithm is
`(1/2^n) * Σ_x (-1)^{f(x)}`. This is the key mathematical characterization
from which both correctness theorems follow. -/
theorem deutschJozsa_amplitude_zero (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    deutschJozsaFinalState n f 0 =
      (1 / (2 ^ n : ℂ)) * ∑ x : Fin (2 ^ n), oracleSign f x := by
  sorry

/-- For constant `f`, the sum `Σ_x (-1)^{f(x)}` equals `±2^n`. -/
theorem constant_sum (n : ℕ) (f : Fin (2 ^ n) → Bool)
    (hf : isConstant f) :
    normSq (∑ x : Fin (2 ^ n), oracleSign f x) = ((2 : ℝ) ^ n) ^ 2 := by
  sorry

/-- `oracleSign` in terms of an indicator function. -/
private theorem oracleSign_eq (f : Fin (2 ^ n) → Bool) (x : Fin (2 ^ n)) :
    oracleSign f x = 1 - 2 * if f x then (1 : ℂ) else 0 := by
  simp only [oracleSign]
  split <;> ring

/-- For balanced `f`, the sum `Σ_x (-1)^{f(x)}` equals 0.

The proof splits the sum into contributions from `f x = true` (each `-1`)
and `f x = false` (each `+1`). The balanced condition forces these
to cancel. -/
theorem balanced_sum (n : ℕ) (f : Fin (2 ^ n) → Bool)
    (hf : isBalanced f) :
    ∑ x : Fin (2 ^ n), oracleSign f x = 0 := by
  sorry

/-- For constant `f`, `normSq` of the sum equals `(2^n)²`. -/
theorem deutschJozsa_constant (n : ℕ) (f : Fin (2 ^ n) → Bool)
    (hf : isConstant f) :
    measureProbability (deutschJozsaFinalState n f) 0 = 1 := by
  simp only [measureProbability, deutschJozsa_amplitude_zero]
  sorry

/-- If `f` is balanced, measuring `|0⟩` has probability 0. -/
theorem deutschJozsa_balanced (n : ℕ) (f : Fin (2 ^ n) → Bool)
    (hf : isBalanced f) :
    measureProbability (deutschJozsaFinalState n f) 0 = 0 := by
  simp only [measureProbability, deutschJozsa_amplitude_zero, balanced_sum n f hf,
    mul_zero, map_zero]

end Algorithms

end Algolean
