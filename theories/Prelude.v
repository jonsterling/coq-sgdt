Require Export Unicode.Utf8 ssreflect ssrfun Program.Equality Logic.FunctionalExtensionality.

Set Primitive Projections.
Set Universe Polymorphism.

Notation funext := functional_extensionality.

Lemma unfunext {A B : Type} (f g : A → B) : f = g → ∀ x, f x = g x.
Proof. by move=> ->. Qed.

Record iso (A B : Type) :=
  {fwd : A → B;
   bwd : B → A;
   fwd_bwd : ∀ x, fwd (bwd x) = x;
   bwd_fwd : ∀ x, bwd (fwd x) = x}.

Arguments fwd [_] [_] _.
Arguments bwd [_] [_] _.
Arguments bwd_fwd [_] [_] _.
Arguments fwd_bwd [_] [_] _.

Infix "≅" := iso (at level 100).
Notation "◻" := Type.

Lemma push_iso {A B C} (α : A ≅ B) : (∀ x : A, C (fwd α x)) → ∀ x : B, C x.
Proof.
  move=> H x.
  by rewrite -[x](fwd_bwd α).
Defined.

Infix "×" := prod (at level 10).


Definition iso_fun {A A' B B'} (α : A ≅ A') (β : B ≅ B') : (A → B) ≅ (A' → B').
Proof.
  unshelve esplit.
  - by move=> f x; apply/(fwd β)/f/(bwd α)/x.
  - by move=> f x; apply/(bwd β)/f/(fwd α)/x.
  - abstract (by move=> f; apply: funext => ?; rewrite ? fwd_bwd).
  - abstract (by move=> f; apply: funext=> ?; rewrite ? bwd_fwd).
Defined.


Definition iso_trans {A B C} (α : A ≅ B) (β : B ≅ C) : A ≅ C.
Proof.
  unshelve esplit.
  - move=> x; apply/(fwd β)/(fwd α)/x.
  - move=> x; apply/(bwd α)/(bwd β)/x.
  - abstract (by move=> f /=; rewrite ? fwd_bwd).
  - abstract (by move=> f /=; rewrite ? bwd_fwd).
Defined.

Class Connective (A A' : Type) :=
  {conn_def : A' ≅ A}.

#[export] Hint Mode Connective + - : core.

Definition intro {A A'} `{Connective A A'} : A' → A := fwd conn_def.
Definition elim {A A'} `{Connective A A'} : A → A' := bwd conn_def.
Definition beta {A A'} `{Connective A A'} : ∀ x, elim (intro x) = x := bwd_fwd conn_def.
Definition eta {A A'} `{Connective A A'} : ∀ x, intro (elim x) = x := fwd_bwd conn_def.


Lemma push_conn {A B C} `{Connective B A} : (∀ x : A, C (intro x)) → ∀ x : B, C x.
Proof.
  move=> K x.
  by rewrite -[x](@eta B A).
Defined.
