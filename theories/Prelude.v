Require Export Unicode.Utf8 ssreflect ssrfun Program.Equality Logic.FunctionalExtensionality.

Set Primitive Projections.
Set Universe Polymorphism.

Notation funext := functional_extensionality.

Lemma unfunext {A B : Type} (f g : A → B) : f = g → ∀ x, f x = g x.
Proof. by move=> ->. Qed.

Record iso (A B : Type) :=
  {intro : A → B;
   elim : B → A;
   eta : ∀ x, intro (elim x) = x;
   beta : ∀ x, elim (intro x) = x}.

Arguments intro [_] [_] _.
Arguments elim [_] [_] _.
Arguments beta [_] [_] _.
Arguments eta [_] [_] _.

Infix "≅" := iso (at level 100).
Notation "◻" := Type.

Lemma push_iso {A B C} (α : A ≅ B) : (∀ x : A, C (intro α x)) → ∀ x : B, C x.
Proof.
  move=> H x.
  rewrite -[x](eta α).
  by move: {x} (elim α x).
Defined.


Infix "×" := prod (at level 10).
