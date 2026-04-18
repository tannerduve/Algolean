/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Algolean.Models.Quantum.Circuit

/-!
# GHZ State Preparation

GHZ (Greenberger–Horne–Zeilinger) state preparation as a quantum circuit.
The circuit applies Hadamard on qubit 0, then CNOT from qubit 0 to all
others sequentially, producing `(|0...0⟩ + |1...1⟩) / √2`.

## Main definitions

- `cnotCascadeFrom`: sequential CNOT from qubit 0 to qubits `k, ..., n-1`
- `ghz`: GHZ circuit as a `Prog (QuantumCircuit n)` producing its CPTP channel

## Main results

- `ghz_measure_zero`: measuring `|0...0⟩` of the output has probability 1/2
- `ghz_measure_allOnes`: measuring `|1...1⟩` of the output has probability 1/2
-/

namespace Algolean

namespace Algorithms

open Complex Prog Cslib
open scoped MState

/-! ### Circuit-level apply helper

`QuantumCircuit`'s `.gate` constructor wraps a `QuantumQuery` and denotes
as a `CPTPMap`. This helper lifts a single gate into a `Prog` whose
evaluation threads an `MState` through the channel. -/

/-- Apply a single gate (wrapped as a circuit leaf) to a density matrix. -/
noncomputable def applyCircuitGate
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumCircuit n) (MState (Fin n → Fin 2)) :=
  FreeM.liftBind (.gate q) fun c => pure (c ρ)

/-! ### CNOT cascade -/

/-- Apply CNOT from qubit 0 to qubits `k, ..., n-1` sequentially. -/
noncomputable def cnotCascadeFrom (k : ℕ) (h0 : 0 < n)
    (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumCircuit n) (MState (Fin n → Fin 2)) :=
  if h : k < n then
    if hne : (⟨0, h0⟩ : Fin n) ≠ ⟨k, h⟩ then do
      let ρ' ← applyCircuitGate (.cnot ⟨0, h0⟩ ⟨k, h⟩ hne) ρ
      cnotCascadeFrom (k + 1) h0 ρ'
    else
      cnotCascadeFrom (k + 1) h0 ρ
  else
    pure ρ
termination_by n - k

/-! ### GHZ algorithm -/

/-- GHZ state preparation:
1. Hadamard on qubit 0
2. CNOT from qubit 0 to all others

Produces `(|0...0⟩ + |1...1⟩) / √2`. -/
noncomputable def ghz (n : ℕ) (hn : 1 < n) :
    Prog (QuantumCircuit n) (MState (Fin n → Fin 2)) := do
  let ρ₀ := initialMState n
  let ρ₁ ← applyCircuitGate (.hadamard ⟨0, by omega⟩) ρ₀
  cnotCascadeFrom 1 (by omega) ρ₁

/-! ### Correctness

All measurement-probability theorems are against the first-qubit POVM on
the output density matrix. Proofs are deferred.
-/

noncomputable abbrev ghzModel (n : ℕ) (f : (Fin n → Fin 2) → Bool) :=
  quantumCircuitModel n (extendOracle (gateOracle f))

/-- Measuring the first qubit of the GHZ output gives outcome 0 with
probability `1/2`. -/
theorem ghz_measure_zero (hn : 1 < n) (f : (Fin n → Fin 2) → Bool) :
    (((measureQubitPOVM (n := n) ⟨0, by omega⟩).measure
      ((ghz n hn).eval (ghzModel n f))) 0 : ℝ) = 1 / 2 := by
  sorry

/-- Measuring the first qubit of the GHZ output gives outcome 1 with
probability `1/2`. -/
theorem ghz_measure_one (hn : 1 < n) (f : (Fin n → Fin 2) → Bool) :
    (((measureQubitPOVM (n := n) ⟨0, by omega⟩).measure
      ((ghz n hn).eval (ghzModel n f))) 1 : ℝ) = 1 / 2 := by
  sorry

end Algorithms

end Algolean
