From SGDT Require Import Prelude GuardedLF.

Set Universe Polymorphism.

Record Thy :=
  {op :> Type;
   bdry : op → Type}.

Arguments bdry [_] _.

Section ITree.
  Context (E : Thy) (R : Type).

  Inductive ITree_F (T : Type) : Type :=
  | Ret (r : R)
  | Do (e : E) (k : bdry e → T).

  Definition ITree_F_map {S T : Type} : (S → T) → (ITree_F S → ITree_F T).
  Proof.
    move=> α; case.
    - apply: Ret.
    - move=> e f.
      apply: Do.
      by move/f/α.
  Defined.

  Definition ITree_F_iso {S T : Type} : (S ≅ T) → (ITree_F S ≅ ITree_F T).
  Proof.
    move=> α.
    unshelve esplit.
    - apply/ITree_F_map/(fwd α).
    - apply/ITree_F_map/(bwd α).
    - case=>//=.
      by move=> ??; congr Do; apply: funext=>?; rewrite fwd_bwd.
    - case=>//=.
      by move=> ??; congr Do; apply: funext=>?; rewrite bwd_fwd.
  Defined.

  Definition ITree : Type := Later.loeb (λ T, ITree_F (dlater T)).

  #[global]
  Instance ITree_conn : Connective ITree (ITree_F (▷ ITree)).
  Proof. by split; apply/iso_trans/loeb_iso/ITree_F_iso/dlater_next. Defined.
End ITree.

Arguments Ret [E] [R] [T].
Arguments Do [E] [R] [T].


Section Alg.

  Context (E : Thy).

  Record Action (A : Type) :=
    {eff : E; kont : bdry eff → ▷ A}.

  Arguments eff [_].
  Arguments kont [_].

  Definition Action_map {A B : Type} (f : A → B) : Action A → Action B.
    move=> α.
    unshelve esplit.
    - exact: eff α.
    - move=> /(kont α).
      apply/Later.map/f.
  Defined.

  Class Alg (A : Type) :=
    {do : Action A → A}.

  Instance ITree_Alg {R} : Alg (ITree E R).
  Proof. by split; move=> α; apply/intro/Do/kont/α. Defined.

  Class alg_hom {A B} `{Alg A} `{Alg B} (f : A → B) : Prop :=
    {pres_do : ∀ α, f (do α) = do (Action_map f α)}.
End Alg.
