import Init

/-!
# Abstract contextual certification, conditional upon arithmetic obligations

This formalizes the *shape* of the induction in Section 15. It does NOT
formalize PA, an internal universally quantified PA proof, the diagonal
lemma, or the formalized deduction theorem. The three critical facts
are fields of `Framework` and must not be mistaken for verified PA
results. This is a conditional theorem about any framework satisfying
the fields.
-/

universe u v
namespace AADCertification.Abstract

structure Framework (Presentation : Type u) (Sentence : Type v) where
  provable : Presentation → Sentence → Prop
  consistentWithNeg : Presentation → Sentence → Prop
  godel : Presentation → Sentence
  adjoin : Presentation → Sentence → Presentation
  baseEquivalent : Sentence → Sentence → Prop
  -- ARITHMETIC OBLIGATION 1: internally formalized deduction theorem.
  deduction : ∀ (p : Presentation) (s : Sentence),
    (¬ consistentWithNeg p s ↔ provable p s)
  -- ARITHMETIC OBLIGATION 2: choice of fixed point respects a
  -- uniform, internally certified provability equivalence.
  godelRespects : ∀ (p q : Presentation),
    (∀ s, provable p s ↔ provable q s) →
    baseEquivalent (godel p) (godel q)
  -- ARITHMETIC OBLIGATION 3: certified proof translation through
  -- adding equivalent axioms.
  adjoinRespects : ∀ (p q : Presentation) (s t : Sentence),
    (∀ x, provable p x ↔ provable q x) →
    baseEquivalent s t →
    (∀ x, provable (adjoin p s) x ↔ provable (adjoin q t) x)

namespace Framework
variable {Presentation : Type u} {Sentence : Type v}

def ProvEq (fw : Framework Presentation Sentence)
    (p q : Presentation) : Prop :=
  ∀ s, fw.provable p s ↔ fw.provable q s

def CtxEq (fw : Framework Presentation Sentence)
    (p q : Presentation) : Prop :=
  ∀ s, fw.consistentWithNeg p s ↔ fw.consistentWithNeg q s

theorem ctxEq_iff_provEq (fw : Framework Presentation Sentence)
    (p q : Presentation) : fw.CtxEq p q ↔ fw.ProvEq p q := by
  classical
  constructor
  · intro h s
    have hn : (¬ fw.consistentWithNeg p s) ↔
        (¬ fw.consistentWithNeg q s) := not_congr (h s)
    exact (fw.deduction p s).symm.trans (hn.trans (fw.deduction q s))
  · intro h s
    have hn : (¬ fw.consistentWithNeg p s) ↔
        (¬ fw.consistentWithNeg q s) :=
      (fw.deduction p s).trans ((h s).trans (fw.deduction q s).symm)
    constructor
    · intro hp
      exact Classical.byContradiction (fun hnq => (hn.mpr hnq) hp)
    · intro hq
      exact Classical.byContradiction (fun hnp => (hn.mp hnp) hq)

def successor (fw : Framework Presentation Sentence)
    (p : Presentation) : Presentation :=
  fw.adjoin p (fw.godel p)

def iterate (fw : Framework Presentation Sentence)
    (p : Presentation) : Nat → Presentation
  | 0 => p
  | n + 1 => fw.successor (fw.iterate p n)

theorem successor_preserves_provEq
    (fw : Framework Presentation Sentence) (p q : Presentation)
    (h : fw.ProvEq p q) :
    fw.ProvEq (fw.successor p) (fw.successor q) := by
  exact fw.adjoinRespects p q (fw.godel p) (fw.godel q) h
    (fw.godelRespects p q h)

theorem successor_preserves_ctxEq
    (fw : Framework Presentation Sentence) (p q : Presentation)
    (h : fw.CtxEq p q) :
    fw.CtxEq (fw.successor p) (fw.successor q) := by
  apply (fw.ctxEq_iff_provEq (fw.successor p) (fw.successor q)).mpr
  exact fw.successor_preserves_provEq p q
    ((fw.ctxEq_iff_provEq p q).mp h)

theorem indefinite_contextual_invariance
    (fw : Framework Presentation Sentence) (p q : Presentation)
    (h : fw.CtxEq p q) :
    ∀ n : Nat, fw.CtxEq (fw.iterate p n) (fw.iterate q n) := by
  intro n
  induction n with
  | zero => simpa [iterate] using h
  | succ n ih =>
      simpa [iterate] using
        (fw.successor_preserves_ctxEq (fw.iterate p n) (fw.iterate q n) ih)

#print axioms ctxEq_iff_provEq
#print axioms indefinite_contextual_invariance

end Framework
end AADCertification.Abstract
