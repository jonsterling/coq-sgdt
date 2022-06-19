From SGDT Require Import Prelude Guarded.
From HB Require Import structures.

(** Guarded Interaction Trees. *)

Set Primitive Projections.

Record Thy :=
  {op :> Type;
   bdry : op -> Type}.

Arguments bdry [_] _.

Section ITree.
  Universe u.
  Context (E : Thy) (R : Type).

  Inductive ITree_F (T : Type@{u}) : Type@{u} :=
  | Ret (r : R)
  | Do (e : E) (k : bdry e -> T).

  Definition ITree_F_map {S T : Type} : (S -> T) -> (ITree_F S -> ITree_F T).
  Proof.
    move=> α; case.
    - apply: Ret.
    - move=> e f.
      apply: Do.
      by move/f/α.
  Defined.

  Definition ITree_F_iso {S T : Type} : (S ≅ T) -> (ITree_F S ≅ ITree_F T).
  Proof.
    move=> α.
    unshelve esplit.
    - apply/ITree_F_map/(fwd α).
    - apply/ITree_F_map/(bwd α).
    - case=>//=.
      by move=> ??; congr Do; apply: funE=>?; rewrite fwd_bwd.
    - case=>//=.
      by move=> ??; congr Do; apply: funE=>?; rewrite bwd_fwd.
  Defined.

  Definition ITree : Type := Later.loeb (fun T => ITree_F (dlater T)).

  #[global]
  Instance ITree_conn : Connective ITree (ITree_F (▷ ITree)).
  Proof. by split; apply/iso_trans/loeb_iso/ITree_F_iso/dlater_next. Defined.

  Definition η : R -> ITree.
  Proof. move=> x; apply/intro/Ret/x. Defined.
End ITree.

Arguments Ret [E] [R] [T].
Arguments Do [E] [R] [T].
Arguments η [E] [R].


Record Action (E : Thy) (A : Type) :=
  {eff : E; kont : bdry eff -> ▷ A}.

Arguments eff [_] [_].
Arguments kont [_] [_].

Definition Action_map {E} {A B : Type} (f : A -> B) : Action E A -> Action E B.
Proof.
  move=> α.
  unshelve esplit.
  - exact: eff α.
  - move=> /(kont α).
    apply/Later.map/f.
Defined.

Lemma Action_map_cmp {E : Thy} {A B C : Type} {f : A -> B} {g : B -> C} (x : Action E A) : Action_map (g \o f) x = Action_map g (Action_map f x).
Proof.
  rewrite /Action_map.
  f_equal.
  apply: funE => ?.
  by rewrite Later.map_assoc.
Qed.

Lemma Action_map_id {E : Thy} {A : Type} {x : Action E A} : Action_map id x = x.
Proof.
  case: x => ? ?.
  rewrite /Action_map; f_equal.
  apply: funE => ?.
  by rewrite Later.map_id.
Qed.

HB.mixin Record IsAlg (E : Thy) (A : Type) := {do_action : Action E A -> A}.
HB.structure Definition Alg E := {A of IsAlg E A}.

Definition do {E : Thy} {A : Alg.type E} (e : E) (k : bdry e -> ▷ A) : A.
Proof. apply: do_action; esplit; apply: k. Defined.

Definition ITree_do_action {E} {R} : Action E (ITree E R) -> ITree E R.
Proof. by move=> α; apply/intro/Do/kont/α. Defined.

HB.instance Definition ITree_IsAlg E R := IsAlg.Build E (ITree E R) ITree_do_action.

Class is_alg_hom {E} {A B : Alg.type E} (f : A -> B) : Prop :=
  {pres_do_action : forall α, f (do_action α) = do_action (Action_map f α)}.

Lemma pres_do {E} {A B : Alg.type E} {f : A -> B} {_ : is_alg_hom f} :
  forall e (k : bdry e -> ▷ A), f (do e k) = do e (Later.map f \o k).
Proof.
  move=> e k.
  rewrite /do.
  apply: pres_do_action.
Qed.

Definition Fun {E} (A : Type) (B : Alg.type E) := A -> B.

Definition fun_do_action {E} {A} {B : Alg.type E} : Action E (A -> B) -> A -> B.
Proof.
  move=> f x.
  apply: do_action.
  move: f; apply: Action_map.
  apply; exact: x.
Defined.

HB.instance Definition fun_IsAlg E A (B : Alg.type E) := IsAlg.Build E (Fun A B) (@fun_do_action E A B).

Section Ext.
  Context {E : Thy} {A : Type} {B : Alg.type E}.

  Definition extends (f : A -> B) (h : ITree E A -> B) : Prop :=
    forall x, h (η x) = f x.

  Lemma extends_unique (f : A -> B) (h h' : ITree E A -> B) {_ : is_alg_hom h} {_ : is_alg_hom h'} : extends f h -> extends f h' -> h = h'.
  Proof.
    move=> hext h'ext.
    apply: funE; apply: push_conn.
    apply: Later.loeb=>ih.
    case.
    - by move=>?; rewrite hext h'ext.
    - move=> e k.
      have -> : (intro (Do e k) = do e k) by [].
      rewrite ? pres_do; congr do.
      apply: funE=>/=i.
      congr Later.ap.
      apply: Later.from_eq.
      move: ih.
      apply: Later.map => H'.
      apply: funE.
      by apply: push_conn.
  Qed.

  Definition ext (f : A -> B) : ITree E A -> B.
  Proof.
    apply: Later.loeb=>f'.
    case/elim.
    - exact: f.
    - move=> e k.
      apply: (do e); move/k.
      move: f'.
      apply: Later.ap.
  Defined.
End Ext.


Notation "f ♯" := (ext f) (at level 0).

Section ExtLaws.
  Context {E : Thy} {A : Type} {B : Alg.type E}.
  Lemma ext_extends : forall f : A -> B, extends f f♯.
  Proof. by move=>??; rewrite /ext Later.loeb_unfold /η beta. Qed.

  #[global]
  Instance ext_hom {f : A -> B} : is_alg_hom f♯.
  Proof. by split; case=>??; rewrite {1}/ext Later.loeb_unfold beta. Qed.
End ExtLaws.

Section Bind.
  Context {E : Thy}.

  Definition bind {A B} (u : ITree E A) (f : A -> ITree E B) : ITree E B := f♯ u.

  Lemma bind_idL {A B} (x : A) (f : A -> ITree E B) : bind (η x) f = f x.
  Proof. by apply: ext_extends. Qed.

  Lemma bind_idR {A} (u : ITree E A) : bind u (@η _ _) = u.
    move: u.
    rewrite /bind.
    apply: unfunE.
    unshelve apply: extends_unique.
    - by apply: η.
    - by build=> ?; rewrite Action_map_id.
    - by move=> ?; apply: ext_extends.
    - by [].
  Qed.

  Lemma bind_idA {A B C} (u : ITree E A) (g : A -> ITree E B) (h : B -> ITree E C) :
    bind (bind u g) h = bind u (fun x => bind (g x) h).
  Proof.
    move: u; rewrite /bind.
    apply: unfunE.
    unshelve apply: extends_unique.
    - move=> x.
      exact: (h♯ (g x)).
    - build=> α.
      rewrite ? pres_do_action.
      congr do_action.
      rewrite /Action_map //=.
      congr Build_Action.
      apply: funE=> ?.
      by rewrite Later.map_assoc.
    - by move=>?; rewrite ext_extends.
    - by move=> ?; rewrite ext_extends.
  Qed.
End Bind.

(** The forgetful functor from algebras to types is conservative. *)
Lemma U_conservative {E} (A B : Alg.type E) (f : A -> B) :
  is_alg_hom f
  -> forall g : B -> A,
      (forall x, f (g x) = x)
      -> (forall x, g (f x) = x)
      -> is_alg_hom g.
Proof.
  move=> fhom g fg gf.
  split=> α.
  have: injective f.
  - move=> x y h.
    rewrite -[x]gf -[y]gf /=.
    by congr g.
  - move=> finj.
    rewrite /=; rewrite Action_map_cmp Action_map_cmp.
    apply: finj.
    rewrite ? pres_do_action.
    rewrite fg.
    congr do_action.
    rewrite -?Action_map_cmp.
    rewrite (_ : ((f \o g) \o id) \o id = id).
    + by apply: funE => ? //=.
    + by rewrite Action_map_id.
Qed.
