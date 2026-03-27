/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.QuantumCircuit

@[expose] public section

/-!
# GHZ State Preparation

GHZ (Greenberger–Horne–Zeilinger) state preparation as a quantum circuit.
The circuit applies Hadamard on qubit 0, then CNOT from qubit 0 to all
others in parallel, producing `(|0...0⟩ + |1...1⟩) / √2`.

## Main definitions

- `cnotLayer`: parallel CNOT from qubit 0 to all others
- `ghz`: GHZ circuit as a `Prog (QuantumCircuit n)`

## Main results

- `cnotLayer_depth`: the CNOT layer has depth 1
- `ghz_measure_zero`: measuring `|0...0⟩` gives probability 1/2
- `ghz_measure_allOnes`: measuring `|1...1⟩` gives probability 1/2
-/

namespace Algolean

namespace Algorithms

open Complex Prog Cslib

/-! ### Circuit construction -/

/-- Build a parallel tree of CNOT gates from qubit 0 to qubits
`k, ..., n-1`. -/
def cnotCascadeFrom (k : ℕ) (h0 : 0 < n)
    (acc : QuantumCircuit n (QState n → QState n)) :
    QuantumCircuit n (QState n → QState n) :=
  if h : k < n then
    cnotCascadeFrom (k + 1) h0
      (.par acc (.gate (.cnot ⟨0, h0⟩ ⟨k, h⟩)))
  else
    acc
termination_by n - k

/-- Parallel CNOT from qubit 0 to all other qubits. Depth 1. -/
def cnotLayer (hn : 1 < n) :
    QuantumCircuit n (QState n → QState n) :=
  cnotCascadeFrom 2 (by omega)
    (.gate (.cnot ⟨0, by omega⟩ ⟨1, by omega⟩))

/-! ### GHZ algorithm -/

/-- GHZ state preparation:
1. Hadamard on qubit 0 (depth 1)
2. CNOT from qubit 0 to all others in parallel (depth 1)

Produces `(|0...0⟩ + |1...1⟩) / √2`. -/
noncomputable def ghz (n : ℕ) (hn : 1 < n) :
    Prog (QuantumCircuit n) (QState n) := do
  let s₀ := QState.initial n
  let s₁ ← applyCircuit (.gate (.hadamard ⟨0, by omega⟩)) s₀
  applyCircuit (cnotLayer hn) s₁

/-! ### Depth -/

private theorem cnotCascadeFrom_depth (k : ℕ) (h0 : 0 < n)
    (acc : QuantumCircuit n (QState n → QState n))
    (hacc : acc.depthOf = 1) :
    (cnotCascadeFrom k h0 acc).depthOf = 1 := by
  unfold cnotCascadeFrom
  split
  · exact cnotCascadeFrom_depth _ h0 _ (by simp [hacc])
  · exact hacc
termination_by n - k

theorem cnotLayer_depth (hn : 1 < n) :
    (cnotLayer hn).depthOf = 1 :=
  cnotCascadeFrom_depth 2 _ _ rfl

/-! ### Correctness -/

/-- Measuring the GHZ output at `|0...0⟩` gives probability `1/2`. -/
theorem ghz_measure_zero (hn : 1 < n) (f : Fin (2 ^ n) → Bool) :
    measureProbability ((ghz n hn).eval (quantumCircuitModel n f))
      ⟨0, by positivity⟩ = 1 / 2 := by
  sorry

/-- Measuring the GHZ output at `|1...1⟩` gives probability `1/2`. -/
theorem ghz_measure_allOnes (hn : 1 < n) (f : Fin (2 ^ n) → Bool) :
    measureProbability ((ghz n hn).eval (quantumCircuitModel n f))
      ⟨2 ^ n - 1, by have := Nat.one_lt_two_pow (n := n) (by omega); omega⟩
      = 1 / 2 := by
  sorry

end Algorithms

end Algolean
