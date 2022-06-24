Require Export ssreflect ssrfun.
Require Import Logic.ProofIrrelevance Logic.FunctionalExtensionality Logic.PropExtensionality.

Export EqNotations.

Set Bullet Behavior "Strict Subproofs".
Set Primitive Projections.
Set Universe Polymorphism.

Notation prfE := proof_irrelevance.
Notation funE := (functional_extensionality _ _).
Notation dfunE := functional_extensionality_dep.
Notation propE := propositional_extensionality.

Lemma unfunE {A B : Type} (f g : A -> B) : f = g -> forall x, f x = g x.
Proof. by move=> ->. Qed.

Global Hint Resolve prfE : core.

Ltac build := unshelve esplit=>//=.

Scheme eq_ind := Induction for eq Sort Type.
Arguments eq_ind [A] x P f y e.

Record sig (A : Type) (B : A -> Type) : Type :=
  Sig {pi1 : A; pi2 : B pi1}.

Arguments Sig [A] [B] pi1 pi2.
Arguments pi1 {A B} _ /.
Arguments pi2 {A B} _ /.

Definition sub (A : Type) (P : A -> Prop) : Type :=
  sig A P.

Set Warnings "-notation-overridden".
Notation "{ x : A & B }" := (sig A (fun x:A => B)) : type_scope.
Notation "{ x : A | B }" := (sub A (fun x:A => (B : Prop))) : type_scope.
Notation "( x , y , .. , z )" := (Sig .. (Sig x y) .. z) : core_scope.
Set Warnings "default".

Definition prod (A B : Type) := {_:A & B}.
Infix "×" := prod (at level 60).


Definition pair {A B} (a : A) (b : B) : A × B :=
  Sig a b.

Lemma sigE {A} {B : A -> Type} : forall (p q : {x : A & B x}) (u : pi1 p = pi1 q) (v : rew u in pi2 p = pi2 q), p = q.
Proof.
  move=> [a +] [x +] //= h; move: x h.
  by apply: eq_ind=> b1 b2//= ->.
Qed.

Lemma subE {A} {P : A -> Prop} : forall (p q : {x : A | P x}), pi1 p = pi1 q -> p = q.
Proof. by move=>???; apply: sigE. Qed.

Lemma prodE {A B} : forall (p q : A × B), pi1 p = pi1 q -> pi2 p = pi2 q -> p = q.
Proof.
  move=> [a1 +] [a2 +] //= h; move: a2 h.
  by apply: eq_ind=> b1 b2 ->.
Qed.



Record iso (A B : Type) :=
  {fwd : A -> B;
   bwd : B -> A;
   fwd_bwd : forall x, fwd (bwd x) = x;
   bwd_fwd : forall x, bwd (fwd x) = x}.

Arguments fwd [_] [_] _.
Arguments bwd [_] [_] _.
Arguments bwd_fwd [_] [_] _.
Arguments fwd_bwd [_] [_] _.

Infix "≅" := iso (at level 100).

Lemma push_iso {A B C} (α : A ≅ B) : (forall x : A, C (fwd α x)) -> forall x : B, C x.
Proof.
  move=> H x.
  by rewrite -[x](fwd_bwd α).
Defined.

Definition iso_fun {A A' B B'} (α : A ≅ A') (β : B ≅ B') : (A -> B) ≅ (A' -> B').
Proof.
  unshelve esplit.
  - by move=> f x; apply/(fwd β)/f/(bwd α)/x.
  - by move=> f x; apply/(bwd β)/f/(fwd α)/x.
  - abstract (by move=> f; apply: funE => ?; rewrite ? fwd_bwd).
  - abstract (by move=> f; apply: funE => ?; rewrite ? bwd_fwd).
Defined.


Definition iso_trans {A B C} (α : A ≅ B) (β : B ≅ C) : A ≅ C.
Proof.
  build.
  - move=> x; apply/(fwd β)/(fwd α)/x.
  - move=> x; apply/(bwd α)/(bwd β)/x.
  - abstract (by move=> f /=; rewrite ? fwd_bwd).
  - abstract (by move=> f /=; rewrite ? bwd_fwd).
Defined.

Definition iso_id {A} : A ≅ A.
Proof. build; by []. Defined.

Class Connective (A A' : Type) :=
  {conn_def : A' ≅ A}.

#[export] Hint Mode Connective + - : core.

Section Rules.
  Context {A A'} `{Connective A A'}.
  Definition intro : A' -> A := fwd conn_def.
  Definition elim : A -> A' := bwd conn_def.
  Definition beta : forall x, elim (intro x) = x := bwd_fwd conn_def.
  Definition eta : forall x, intro (elim x) = x := fwd_bwd conn_def.
End Rules.


Lemma push_conn {A B C} `{Connective B A} : (forall x : A, C (intro x)) -> forall x : B, C x.
Proof.
  move=> K x.
  by rewrite -[x](@eta B A).
Defined.
