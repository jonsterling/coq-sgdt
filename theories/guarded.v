From sgdt Require Import preamble.

Set Universe Polymorphism.

Section Later.
  Universe u.
  Axiom later : Type@{u} -> Type@{u}.
End Later.

Notation "▷ A" := (later A) (at level 60).

Axiom next : forall {A}, A -> ▷ A.
Notation "next: x" := (next x) (at level 100).

Module Later.
  Axiom from_eq : forall {A} (a b : A), ▷ (a = b) -> next a = next b.
  Axiom to_eq : forall {A} (a b : A), next a = next b -> ▷ (a = b).
  Axiom ap : forall {A B}, later (A -> B) -> later A -> later B.

  Module ApNotation.
    Infix "⊛" := ap (at level 50).
  End ApNotation.

  Import ApNotation.

  Axiom ap_compute : forall {A B} (f : A -> B) (x : A), next f ⊛ next x = next (f x).
  Axiom ap_id : forall {A} (x : ▷ A), next id ⊛ x = x.

  Definition map {A B} (f : A -> B) (x : later A) : later B :=
    next f ⊛ x.

  Axiom loeb : forall {A} (f : ▷ A -> A), A.
  Axiom map_assoc : forall {A B C} (f : A -> B) (g : B -> C) x, map g (map f x) = map (g \o f) x.
  Axiom map_id : forall {A} (x : ▷ A), map id x = x.

  Axiom loeb_unfold : forall {A} (f : ▷ A -> A), loeb f = f (next (loeb f)).

  Lemma loeb_iso {F : ▷ Type -> Type} : iso (F (next (Later.loeb F))) (Later.loeb F).
  Proof.
    unshelve esplit.
    - move=> ?; by rewrite Later.loeb_unfold.
    - move=> ?; by rewrite -Later.loeb_unfold.
    - abstract (move=> ? //=; by rewrite rew_opp_l).
    - abstract (move=> ? //=; by rewrite rew_opp_r).
  Qed.
End Later.

Section DLater.
  Universe v.
  Axiom dlater : ▷ (Type@{v}) -> Type@{v}.
End DLater.

Axiom dlater_next_eq : forall A, ▷ A = dlater (next A).
Arguments dlater_next_eq {_}.

Lemma dlater_next_iso {A} : iso (▷ A) (dlater (next A)).
Proof. by rewrite dlater_next_eq; apply: iso_id. Defined.

Global Instance dlater_next_conn {A : Type} : Connective (dlater (next A)) (▷ A).
Proof. by split; apply: dlater_next_iso. Defined.

Export Later.ApNotation.
Infix "<$>" := Later.map (at level 50).

Theorem map_id {A} (x : ▷ A) : id <$> x = x.
Proof. by rewrite /Later.map Later.ap_id. Qed.
