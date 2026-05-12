module

public import Algolean.QueryModel

@[expose] public section

namespace Algolean.Algorithms

open Cslib

abbrev compositeQuery (Q₁ Q₂ : Type u → Type v) : Type u → Type v :=
  fun β => Sum (Q₁ β) (Q₂ β)

def Model.compose [AddZero c₁] [AddZero c₂]
    (m₁ : Model Q₁ c₁) (m₂ : Model Q₂ c₂) :
    Model (compositeQuery Q₁ Q₂) (c₁ × c₂) where
  evalQuery
    | .inl q => m₁.evalQuery q
    | .inr q => m₂.evalQuery q
  cost
    | .inl q => (m₁.cost q, 0)
    | .inr q => (0, m₂.cost q)

def Reduction.compose {Q₁ Q₂ Q₃ : Type u → Type u} (r₁ : Reduction Q₁ Q₃) (r₂ : Reduction Q₂ Q₃) :
    Reduction (compositeQuery Q₁ Q₂) Q₃ where
  reduce := fun q =>
    match q with
    | .inl q => r₁.reduce q
    | .inr q => r₂.reduce q

def Prog.extend {Q₁ α} (Q₂ : Type u → Type u) (P : Prog Q₁ α) : Prog (compositeQuery Q₁ Q₂) α :=
  match P with
  | .liftBind op cont => .liftBind (Sum.inl op) (fun x => extend Q₂ (cont x))
  | .pure a => pure a

@[simp]
theorem Prog.extend_eval {Q₁ α Q₂ c₁ c₂} [AddZero c₁] [AddZero c₂] {P : Prog Q₁ α}
    {M₁ : Model Q₁ c₁} {M₂ : Model Q₂ c₂} :
    (P.extend Q₂).eval (M₁.compose M₂) = P.eval M₁ := by
  induction P with
  | pure a => simp [extend]
  | liftBind op cond ih =>
    simp [extend, ih]
    congr

theorem compose_eval [AddZero c₁] [AddZero c₂] {P : Prog Q₁ α}
    {r₁ : Reduction Q₁ Q₃} {r₂ : Reduction Q₂ Q₃}
    {M₁ : Model Q₁ c₁} {M₂ : Model Q₂ c₂} {M₃ : Model Q₃ c₃}
    (h₁ : ∀ {ι} (q : Q₁ ι), (r₁.reduce q).eval M₃ = M₁.evalQuery q)
    (h₂ : ∀ {ι} (q : Q₂ ι), (r₂.reduce q).eval M₃ = M₂.evalQuery q) :
    ((P.extend Q₂).reduceProg (r₁.compose r₂)).eval M₃ = P.eval M₁ := by
  rw [Prog.reduceProg_eval (P.extend Q₂) (r₁.compose r₂) (M₁.compose M₂) M₃]
  · simp
  · simp [Reduction.compose, Model.compose, h₁, h₂]


end Algolean.Algorithms
