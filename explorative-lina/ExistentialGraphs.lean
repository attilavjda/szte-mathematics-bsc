import Mathlib

/-!
# Peirce's existential graphs (alpha part) and their categorical reading

Peirce's *alpha* graphs are the propositional fragment of his diagrammatic
logic:

* the blank sheet of assertion is truth;
* writing two graphs side by side ("juxtaposition") is conjunction;
* enclosing a graph in an oval ("cut") is negation;
* the *scroll*, a cut inside a cut, is implication.

This is the same style of reasoning as graphical linear algebra: a *syntax of
pictures*, together with rewrite rules that are sound for a semantics.  Here
the semantics is `Prop` instead of linear relations.

We formalise

* the syntax `Peirce.EG` and semantics `Peirce.eval`;
* contexts `Peirce.Ctx` with their parity (`even`), i.e. the number of cuts one
  is nested inside;
* the **monotonicity theorem** `Peirce.eval_mono`, which is the semantic
  content of Peirce's rules: in an evenly enclosed area a graph may be
  *weakened*, in an oddly enclosed area it may be *strengthened*;
* the four alpha rules as corollaries: erasure, insertion, double cut,
  iteration/deiteration;
* the categorical reading: the scroll is exactly the *exponential* of the
  poset-category of propositions, characterised by the currying adjunction
  `Peirce.scroll_adjunction`.
-/

namespace Peirce

universe u

variable {α : Type u}

/-- Syntax of alpha existential graphs. -/
inductive EG (α : Type u) : Type u
  | /-- The blank sheet of assertion. -/
    blank : EG α
  | /-- A proposition letter written on the sheet. -/
    atom : α → EG α
  | /-- Juxtaposition: two graphs scribed on the same area. -/
    juxt : EG α → EG α → EG α
  | /-- A cut: the graph enclosed in an oval. -/
    cut : EG α → EG α
  deriving Repr

namespace EG

/-- Semantics: blank = `True`, juxtaposition = `∧`, cut = `¬`. -/
def eval (v : α → Prop) : EG α → Prop
  | blank => True
  | atom a => v a
  | juxt p q => eval v p ∧ eval v q
  | cut p => ¬ eval v p

@[simp] theorem eval_blank (v : α → Prop) : eval v (blank : EG α) = True := rfl
@[simp] theorem eval_atom (v : α → Prop) (a : α) : eval v (atom a) = v a := rfl
@[simp] theorem eval_juxt (v : α → Prop) (p q : EG α) :
    eval v (juxt p q) = (eval v p ∧ eval v q) := rfl
@[simp] theorem eval_cut (v : α → Prop) (p : EG α) : eval v (cut p) = ¬ eval v p := rfl

/-- The scroll: `cut (juxt p (cut q))`, Peirce's drawing of "p implies q". -/
def scroll (p q : EG α) : EG α := cut (juxt p (cut q))

/-- The scroll really is implication. -/
@[simp] theorem eval_scroll (v : α → Prop) (p q : EG α) :
    eval v (scroll p q) ↔ (eval v p → eval v q) := by
  simp only [scroll, eval_cut, eval_juxt]
  tauto

end EG

open EG

/-- A one-hole context: a place on the sheet, possibly inside some cuts. -/
inductive Ctx (α : Type u) : Type u
  | hole : Ctx α
  | juxtL : Ctx α → EG α → Ctx α
  | juxtR : EG α → Ctx α → Ctx α
  | cut : Ctx α → Ctx α

namespace Ctx

/-- Scribe a graph into the hole. -/
def fill : Ctx α → EG α → EG α
  | hole, p => p
  | juxtL c q, p => EG.juxt (fill c p) q
  | juxtR q c, p => EG.juxt q (fill c p)
  | cut c, p => EG.cut (fill c p)

/-- `true` if the hole is enclosed by an even number of cuts. -/
def even : Ctx α → Bool
  | hole => true
  | juxtL c _ => even c
  | juxtR _ c => even c
  | cut c => ! even c

@[simp] theorem fill_hole (p : EG α) : fill hole p = p := rfl
@[simp] theorem even_hole : (hole : Ctx α).even = true := rfl

end Ctx

/-- **Monotonicity of areas.**  If `p` entails `q`, then in an evenly enclosed
area replacing `p` by `q` preserves truth, and in an oddly enclosed area
replacing `q` by `p` preserves truth.  All four alpha rules are instances. -/
theorem eval_mono (v : α → Prop) {p q : EG α} (h : eval v p → eval v q) :
    ∀ c : Ctx α,
      (c.even = true → eval v (c.fill p) → eval v (c.fill q)) ∧
      (c.even = false → eval v (c.fill q) → eval v (c.fill p)) := by
  intro c
  induction c with
  | hole => exact ⟨fun _ hp => h hp, fun hfalse => by simp at hfalse⟩
  | juxtL c r ih =>
      refine ⟨fun he hpq => ⟨ih.1 he hpq.1, hpq.2⟩, fun ho hpq => ⟨ih.2 ho hpq.1, hpq.2⟩⟩
  | juxtR r c ih =>
      refine ⟨fun he hpq => ⟨hpq.1, ih.1 he hpq.2⟩, fun ho hpq => ⟨hpq.1, ih.2 ho hpq.2⟩⟩
  | cut c ih =>
      constructor
      · intro he hcut hq
        have hodd : c.even = false := by
          simpa [Ctx.even] using he
        exact hcut (ih.2 hodd hq)
      · intro ho hcut hp
        have heven : c.even = true := by
          simpa [Ctx.even] using ho
        exact hcut (ih.1 heven hp)

/-- **Rule of erasure.**  Anything scribed in an evenly enclosed area may be
erased. -/
theorem rule_erasure (v : α → Prop) (c : Ctx α) (hc : c.even = true) (p q : EG α) :
    eval v (c.fill (juxt p q)) → eval v (c.fill p) :=
  (eval_mono v (p := juxt p q) (q := p) (fun h => h.1) c).1 hc

/-- **Rule of insertion.**  Anything may be scribed into an oddly enclosed
area. -/
theorem rule_insertion (v : α → Prop) (c : Ctx α) (hc : c.even = false) (p q : EG α) :
    eval v (c.fill p) → eval v (c.fill (juxt p q)) :=
  (eval_mono v (p := juxt p q) (q := p) (fun h => h.1) c).2 hc

/-- **Rule of the double cut** (in the empty context). -/
theorem rule_doubleCut (v : α → Prop) (p : EG α) :
    eval v (cut (cut p)) ↔ eval v p := by
  simp only [eval_cut]
  tauto

/-- **Rule of the double cut**, in an arbitrary context. -/
theorem rule_doubleCut_ctx (v : α → Prop) (c : Ctx α) (p : EG α) :
    eval v (c.fill (cut (cut p))) ↔ eval v (c.fill p) := by
  constructor
  · rcases hc : c.even with _ | _
    · exact (eval_mono v (p := p) (q := cut (cut p)) (fun h hn => hn h) c).2 hc
    · exact (eval_mono v (p := cut (cut p)) (q := p)
        (fun h => by classical exact not_not.mp h) c).1 hc
  · rcases hc : c.even with _ | _
    · exact (eval_mono v (p := cut (cut p)) (q := p)
        (fun h => by classical exact not_not.mp h) c).2 hc
    · exact (eval_mono v (p := p) (q := cut (cut p)) (fun h hn => hn h) c).1 hc

/-- **Iteration and deiteration.**  A graph already scribed on an area may be
copied into any area nested inside it, and a copy may be removed again.  Here
in the basic case of one enclosing cut. -/
theorem rule_iteration (v : α → Prop) (p q : EG α) :
    eval v (juxt p (cut q)) ↔ eval v (juxt p (cut (juxt p q))) := by
  simp only [eval_juxt, eval_cut]
  tauto

/-- **Modus ponens** as a graph transformation: a scroll together with its
antecedent yields the consequent. -/
theorem rule_modusPonens (v : α → Prop) (p q : EG α) :
    eval v (juxt p (scroll p q)) → eval v q := by
  intro h
  exact (eval_scroll v p q).1 h.2 h.1

/-! ## The categorical reading

Propositions ordered by entailment form a (thin) category; conjunction is the
categorical product and the scroll is the exponential.  The rules above are the
familiar structural maps of that category, and the scroll is characterised by
an adjunction — the same universal-property style of argument as in the
commutative-diagram proofs of `CategoryDiagrams.lean`. -/

/-- Juxtaposition is the **product**: a graph entails a juxtaposition exactly
when it entails both components (the universal property of `∧`). -/
theorem juxt_universal (v : α → Prop) (r p q : EG α) :
    (eval v r → eval v (juxt p q)) ↔
      ((eval v r → eval v p) ∧ (eval v r → eval v q)) := by
  simp only [eval_juxt]
  tauto

/-- The blank sheet is the **terminal object**: everything entails it. -/
theorem blank_terminal (v : α → Prop) (p : EG α) : eval v p → eval v (blank : EG α) :=
  fun _ => trivial

/-- **The scroll is an exponential.**  This currying adjunction
`(- ∧ q) ⊣ (q ⇒ -)` is the categorical content of Peirce's scroll. -/
theorem scroll_adjunction (v : α → Prop) (p q r : EG α) :
    (eval v (juxt p q) → eval v r) ↔ (eval v p → eval v (scroll q r)) := by
  simp only [eval_juxt, eval_scroll]
  tauto

end Peirce
