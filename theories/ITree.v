From SGDT Require Import Prelude GuardedLF.

(** Guarded Interaction Trees. *)

Set Universe Polymorphism.
Set Primitive Projections.

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

  Definition η : R → ITree.
  Proof. move=> x; apply/intro/Ret/x. Defined.
End ITree.

Arguments Ret [E] [R] [T].
Arguments Do [E] [R] [T].
Arguments η [E] [R].


Record Action (E : Thy) (A : Type) :=
  {eff : E; kont : bdry eff → ▷ A}.

Arguments eff [_] [_].
Arguments kont [_] [_].

Definition Action_map {E} {A B : Type} (f : A → B) : Action E A → Action E B.
Proof.
  move=> α.
  unshelve esplit.
  - exact: eff α.
  - move=> /(kont α).
    apply/Later.map/f.
Defined.

Class Alg E (A : Type) :=
  {do : Action E A → A}.

Instance ITree_Alg {E} {R} : Alg E (ITree E R).
Proof. by split; move=> α; apply/intro/Do/kont/α. Defined.

Class alg_hom {E} {A B} `{Alg E A} `{Alg E B} (f : A → B) : Prop :=
  {pres_do : ∀ α, f (do α) = do (Action_map f α)}.

Instance FunAlg {E} {A B} `{Alg E B} : Alg E (A → B).
Proof.
  split=> f x.
  apply: do.
  move: f; apply: Action_map.
  apply; exact: x.
Defined.


Hint Mode Alg + +.

Module UniversalProperty.
  Section UniversalProperty.
    Context {A B : Type} {E : Thy} `{Alg E B}.

    Definition extends (f : A → B) (h : ITree E A → B) : Prop :=
      ∀ x, h (η x) = f x.

    Lemma extends_unique (f : A → B) (h h' : ITree E A → B) {hhom : alg_hom h} {h'hom : alg_hom h'} : extends f h → extends f h' → h = h'.
    Proof.
      move=> hext h'ext.
      apply: funext.
      apply: (push_iso conn_def).
      apply: Later.loeb=>ih.
      case.
      - by move=>?; rewrite hext h'ext.
      - move=> e k.
        case: hhom => hhom.
        case: h'hom => h'hom.
        rewrite (hhom {| eff := e; kont := k |}).
        rewrite (h'hom {| eff := e; kont := k |}).
        congr do.
        rewrite /Action_map.
        congr Build_Action.
        apply: funext => /= i.
        congr Later.ap.
        apply: Later.from_eq.
        move: ih.
        apply: Later.map => H'.
        apply: funext.
        by apply: (push_iso conn_def).
    Qed.

    Definition ext (f : A → B) : ITree E A → B.
    Proof.
      apply: Later.loeb=>f'.
      case/elim.
      - exact: f.
      - move=> e k.
        apply: do; exists e; move/k.
        move: f'.
        apply: Later.ap.
    Defined.

    Notation "f ♯" := (ext f) (at level 0).

    Lemma ext_extends : ∀ f, extends f f♯.
    Proof. by move=>??; rewrite /ext Later.loeb_unfold /η beta. Qed.

    #[global]
    Instance ext_hom {f} : alg_hom f♯.
    Proof. by split; case=>??; rewrite {1}/ext Later.loeb_unfold /ITree_Alg beta. Qed.
  End UniversalProperty.
End UniversalProperty.
