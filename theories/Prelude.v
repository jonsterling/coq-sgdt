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
  by rewrite -[x](eta α).
Defined.

Infix "×" := prod (at level 10).


Definition iso_fun {A A' B B'} (α : A ≅ A') (β : B ≅ B') : (A → B) ≅ (A' → B').
Proof.
  unshelve esplit.
  - by move=> f x; apply/(intro β)/f/(elim α)/x.
  - by move=> f x; apply/(elim β)/f/(intro α)/x.
  - abstract (by move=> f; apply: funext => ?; rewrite ? eta).
  - abstract (by move=> f; apply: funext=> ?; rewrite ? beta).
Defined.


Definition iso_trans {A B C} (α : A ≅ B) (β : B ≅ C) : A ≅ C.
Proof.
  unshelve esplit.
  - move=> x; apply/(intro β)/(intro α)/x.
  - move=> x; apply/(elim α)/(elim β)/x.
  - abstract (by move=> f /=; rewrite ? eta).
  - abstract (by move=> f /=; rewrite ? beta).
Defined.
