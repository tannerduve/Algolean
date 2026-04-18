/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Algolean.Models.Quantum.Oracle
import Algolean.Models.Quantum.Circuit

/-!
# Deutsch-Jozsa Algorithm

The Deutsch-Jozsa algorithm determines whether a boolean function
`f : (Fin n → Fin 2) → Bool` is constant (all outputs equal) or balanced
(exactly half true, half false), promised that one of these holds.
It uses exactly 1 oracle query, compared to `2^(n-1) + 1` classically.

## Main definitions

- `deutschJozsa`: The algorithm as a `Prog (QuantumQuery n) (MState ...)`.
- `isConstant`: The promise that `f` is constant.
- `isBalanced`: The promise that `f` is balanced.
- `deutschJozsa_cost`: The algorithm uses exactly 1 oracle query.
-/

namespace Algolean

namespace Algorithms

open Prog Cslib Complex
open scoped MState

/-! ### Helpers -/

/-- Apply Hadamard to qubits `k, k+1, ..., n-1` sequentially. -/
noncomputable def hadamardFrom (k : ℕ) (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) :=
  if h : k < n then do
    let ρ' ← applyGate (.hadamard ⟨k, h⟩) ρ
    hadamardFrom (k + 1) ρ'
  else
    pure ρ
termination_by n - k

/-- Apply Hadamard to all qubits. -/
noncomputable def hadamardAll (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) :=
  hadamardFrom 0 ρ

/-! ### Promises -/

/-- `f` is constant: all outputs are equal. -/
def isConstant (f : (Fin n → Fin 2) → Bool) : Prop :=
  ∀ i j, f i = f j

/-- `f` is balanced: exactly half the outputs are true. -/
def isBalanced (f : (Fin n → Fin 2) → Bool) : Prop :=
  (Finset.univ.filter (fun x => f x = true)).card = Fintype.card (Fin n → Fin 2) / 2

/-! ### Algorithm -/

/-- The Deutsch-Jozsa algorithm. Applies Hadamard to all qubits,
queries the oracle once, then applies Hadamard again. -/
noncomputable def deutschJozsa (n : ℕ) (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) := do
  let ρ₁ ← hadamardAll ρ
  let ρ₂ ← applyGate .oracle ρ₁
  hadamardAll ρ₂

/-! ### Cost -/

/-- `hadamardFrom` has zero oracle cost. -/
theorem hadamardFrom_time (k : ℕ) (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) ℕ)
    (hcost : ∀ q, M.cost (QuantumQuery.hadamard q) = 0) :
    Prog.time (hadamardFrom k ρ) M = 0 := by
  unfold hadamardFrom
  split
  · case _ h =>
    change Prog.time ((applyGate (.hadamard ⟨k, h⟩) ρ).bind
      (fun ρ' => hadamardFrom (k + 1) ρ')) M = 0
    rw [Prog.time_bind, applyGate_time, hcost, zero_add]
    exact hadamardFrom_time (k + 1) _ M hcost
  · exact Prog.time_pure _ _
termination_by n - k

/-- `hadamardAll` has zero oracle cost. -/
theorem hadamardAll_time (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) ℕ)
    (hcost : ∀ q, M.cost (QuantumQuery.hadamard q) = 0) :
    Prog.time (hadamardAll ρ) M = 0 :=
  hadamardFrom_time 0 ρ M hcost

/-- The Deutsch-Jozsa algorithm uses exactly 1 oracle query. -/
theorem deutschJozsa_cost (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    Prog.time (deutschJozsa n (initialMState n)) (quantumModel n f) = 1 := by
  unfold deutschJozsa
  change Prog.time ((hadamardAll (initialMState n)).bind fun ρ₁ =>
    (applyGate .oracle ρ₁).bind fun ρ₂ => hadamardAll ρ₂) (quantumModel n f) = 1
  rw [Prog.time_bind, hadamardAll_time _ _ (fun q => rfl), zero_add,
    Prog.time_bind, applyGate_time, quantumModel_cost_oracle]
  rw [hadamardAll_time _ _ (fun q => rfl)]

/-! ### Correctness

Correctness statements phrased against the first-qubit computational-basis
measurement of the final state. Proofs are deferred.
-/

/-- The final state of the Deutsch-Jozsa algorithm. -/
noncomputable def deutschJozsaFinalState (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) : MState (Fin n → Fin 2) :=
  Prog.eval (deutschJozsa n (initialMState n)) (quantumModel n f)

/-- For constant `f`, measuring qubit 0 of the output yields outcome `0`
with probability 1. -/
theorem deutschJozsa_constant (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    (hf : isConstant f) (hn : 0 < n) :
    (((measureQubitPOVM (n := n) ⟨0, hn⟩).measure (deutschJozsaFinalState n f))
      0 : ℝ) = 1 := by
  sorry

/-- For balanced `f`, measuring qubit 0 of the output yields outcome `0`
with probability 0. -/
theorem deutschJozsa_balanced (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    (hf : isBalanced f) (hn : 0 < n) :
    (((measureQubitPOVM (n := n) ⟨0, hn⟩).measure (deutschJozsaFinalState n f))
      0 : ℝ) = 0 := by
  sorry

end Algorithms

end Algolean
