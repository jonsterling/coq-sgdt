From SGDT Require Import Prelude.

Axiom later : Type → Type.
Notation "▷ A" := (later A) (at level 60).

Axiom next : ∀ {A}, A → ▷ A.
Notation "next: x" := (next x) (at level 100).

Module Later.
  Axiom from_eq : ∀ {A} (a b : A), ▷ (a = b) → next a = next b.
  Axiom to_eq : ∀ {A} (a b : A), next a = next b → ▷ (a = b).
  Axiom ap : ∀ {A B}, later (A → B) → later A → later B.

  Module ApNotation.
    Infix "⊛" := ap (at level 50).
  End ApNotation.

  Import ApNotation.

  Axiom ap_compute : ∀ {A B} (f : A → B) (x : A), next f ⊛ next x = next (f x).
  Axiom ap_id : ∀ {A} (x : ▷ A), next id ⊛ x = x.

  Definition map {A B} : (A → B) → later A → later B :=
    fun f x => next f ⊛ x.

  Axiom loeb : ∀ {A} (f : ▷ A → A), A.
  Axiom map_assoc : ∀ {A B C} (f : A → B) (g : B → C) x, map g (map f x) = map (g \o f) x.

  Axiom loeb_unfold : ∀ {A} (f : ▷ A → A), loeb f = f (next (loeb f)).
End Later.

Axiom dlater : ▷ Type → Type.
Axiom dlater_next : ∀ A, iso (▷ A) (dlater (next A)).
Arguments dlater_next {_}.


Lemma loeb_iso {F : ▷ Type → Type} : iso (F (next (Later.loeb F))) (Later.loeb F).
Proof.
  unshelve esplit.
  - move=> ?; by rewrite Later.loeb_unfold.
  - move=> ?; by rewrite -Later.loeb_unfold.
  - abstract (move=> ? //=; by rewrite rew_opp_l).
  - abstract (move=> ? //=; by rewrite rew_opp_r).
Qed.


Export Later.ApNotation.
Infix "<$>" := Later.map (at level 50).
