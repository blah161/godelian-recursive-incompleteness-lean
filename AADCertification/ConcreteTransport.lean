import Init

/-!
# Concrete Hilbert proof transport (no unproved interface fields)

This is a genuinely specified proof calculus, NOT the arithmetic proof
system of PA.  The theorems below are intended to be checked by Lean's
kernel, and have no `sorry` or `axiom` declarations.

The exercise establishes an executable/formal model of the proof-
translation obligation which remains to be transported to a Gödel-
coded presentation of PA.
-/

namespace AADCertification.Concrete

inductive Formula where
  | atom : Nat → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

open Formula

/-- Hilbert system with arbitrary nonlogical axioms, K, S and modus ponens. -/
inductive Derives (A : Formula → Prop) : Formula → Prop where
  | hypothesis {p : Formula} : A p → Derives A p
  | k (p q : Formula) : Derives A (imp p (imp q p))
  | s (p q r : Formula) :
      Derives A (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  | mp {p q : Formula} : Derives A (imp p q) → Derives A p → Derives A q

/-- Transport each axiom to a proof in the destination theory. -/
theorem proof_transport {A B : Formula → Prop}
    (translateAxiom : ∀ p, A p → Derives B p)
    {p : Formula} (d : Derives A p) : Derives B p := by
  induction d with
  | hypothesis h => exact translateAxiom _ h
  | k p q => exact Derives.k p q
  | s p q r => exact Derives.s p q r
  | mp d₁ d₂ ih₁ ih₂ => exact Derives.mp ih₁ ih₂

/-- Append exactly one additional nonlogical axiom. -/
def Adjoin (A : Formula → Prop) (s : Formula) : Formula → Prop :=
  fun p => A p ∨ p = s

theorem lift {A : Formula → Prop} {s p : Formula}
    (d : Derives A p) : Derives (Adjoin A s) p := by
  apply proof_transport (A := A) (B := Adjoin A s) (fun x hx => ?_) d
  exact Derives.hypothesis (Or.inl hx)

theorem selected_axiom {A : Formula → Prop} {s : Formula} :
    Derives (Adjoin A s) s :=
  Derives.hypothesis (Or.inr rfl)

/-- The new axiom changes no theorems if it already has a proof. -/
theorem redundant_axiom {A : Formula → Prop} {s : Formula}
    (hs : Derives A s) :
    ∀ p, Derives (Adjoin A s) p ↔ Derives A p := by
  intro p
  constructor
  · intro d
    refine proof_transport (A := Adjoin A s) (B := A) (fun x hx => ?_) d
    cases hx with
    | inl ha => exact Derives.hypothesis ha
    | inr heq =>
        subst x
        exact hs
  · intro d
    exact lift d

/-- If both bases prove the same formulas and each added axiom can
    be derived from the other, the resulting extensions remain equivalent. -/
theorem adjoin_congruence {A B : Formula → Prop} {s t : Formula}
    (baseEq : ∀ p, Derives A p ↔ Derives B p)
    (sToT : Derives A (imp s t))
    (tToS : Derives A (imp t s)) :
    ∀ p, Derives (Adjoin A s) p ↔ Derives (Adjoin B t) p := by
  intro p
  constructor
  · intro d
    refine proof_transport (A := Adjoin A s) (B := Adjoin B t)
      (fun x hx => ?_) d
    cases hx with
    | inl ha => exact lift ((baseEq x).mp (Derives.hypothesis ha))
    | inr heq =>
        subst x
        have hReverse : Derives B (imp t s) := (baseEq (imp t s)).mp tToS
        exact Derives.mp (lift hReverse) selected_axiom
  · intro d
    refine proof_transport (A := Adjoin B t) (B := Adjoin A s)
      (fun x hx => ?_) d
    cases hx with
    | inl hb => exact lift ((baseEq x).mpr (Derives.hypothesis hb))
    | inr heq =>
        subst x
        exact Derives.mp (lift sToT) selected_axiom

/-- A small concrete regression theorem using an actual K proof. -/
def p : Formula := atom 0
def q : Formula := atom 1
def tautology : Formula := imp p (imp q p)

theorem tautology_has_proof : Derives (fun _ => False) tautology :=
  Derives.k p q

theorem appending_tautology_changes_nothing :
    ∀ φ, Derives (Adjoin (fun _ => False) tautology) φ ↔
      Derives (fun _ => False) φ :=
  redundant_axiom tautology_has_proof

#print axioms proof_transport
#print axioms redundant_axiom
#print axioms adjoin_congruence
#print axioms appending_tautology_changes_nothing

end AADCertification.Concrete
