From sgdt Require Import preamble guarded category.
From HB Require Import structures.

(** Guarded Interaction Trees. *)

Set Primitive Projections.

Record Thy :=
  {op :> Set;
   bdry : op -> Set}.

Arguments bdry [_] _.

Section ITree.
  Context (E : Thy) (R : Set).

  Inductive ITree_F (T : Set) : Set :=
  | Ret (r : R)
  | Do (e : E) (k : bdry e -> T).

  Definition ITree_F_map {S T : Set} : (S -> T) -> (ITree_F S -> ITree_F T).
  Proof.
    move=> α; case.
    - apply: Ret.
    - move=> e f.
      apply: Do.
      by move/f/α.
  Defined.

  Definition ITree_F_iso {S T : Set} : (S ≅ T) -> (ITree_F S ≅ ITree_F T).
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

  Definition ITree : Set := Later.loeb (fun T => ITree_F (dlater T)).

  Global Instance ITree_conn : Connective ITree (ITree_F (▷ ITree)).
  Proof. by split; apply/iso_trans/Later.loeb_iso/ITree_F_iso/dlater_next_iso. Defined.

  Definition η : R -> ITree.
  Proof. by move=> x; apply/intro/Ret/x. Defined.
End ITree.

Arguments Ret [E] [R] [T].
Arguments Do [E] [R] [T].
Arguments η [E] [R].


Record Action (E : Thy) (A : Set) :=
  {eff : E; kont : bdry eff -> ▷ A}.

Arguments eff [_] [_].
Arguments kont [_] [_].

Definition Action_map {E} {A B : Set} (f : A -> B) : Action E A -> Action E B.
Proof.
  move=> α.
  unshelve esplit.
  - exact: eff α.
  - move=> /(kont α).
    apply/Later.map/f.
Defined.

Lemma Action_map_cmp {E : Thy} {A B C : Set} {f : A -> B} {g : B -> C} (x : Action E A) : Action_map (g \o f) x = Action_map g (Action_map f x).
Proof.
  rewrite /Action_map.
  f_equal.
  apply: funE => ?.
  by rewrite Later.map_assoc.
Qed.

Lemma Action_map_id {E : Thy} {A : Set} {x : Action E A} : Action_map id x = x.
Proof.
  case: x => ? ?.
  rewrite /Action_map; f_equal.
  apply: funE => ?.
  by rewrite Later.map_id.
Qed.


Module Alg.
  Record mixin_of (E : Thy) (A : Set) :=
    {do_action : Action E A -> A}.

  Structure type E : Type := Pack {sort; class : mixin_of E sort}.

  Module Exports.
    Coercion sort : type >-> Sortclass.
  End Exports.
End Alg.

Export Alg.Exports.

Definition do_action {E : Thy} {X : Alg.type E} := Alg.do_action _ _ (Alg.class E X).

Module AlgHom.
  Record mixin_of {E : Thy} (A B : Alg.type E) (f : A -> B) : Prop :=
    {pres_do_action : forall α, f (do_action α) = do_action (Action_map f α) }.

  Structure type {E} (A B : Alg.type E) := Pack {map; class : mixin_of A B map}.

  Module Exports.
    Coercion map : type >-> Funclass.
  End Exports.

  Lemma ext {E} {A B : Alg.type E} : forall f g : type A B, map _ _ f = map _ _ g -> f = g.
  Proof.
    case=> f hf; case=> g hg //= fg.
    move: g fg hg.
    apply: eq_ind=> ?.
    by congr Pack.
  Qed.
End AlgHom.

Export AlgHom.Exports.


Definition pres_do_action {E : Thy} {X Y : Alg.type E} (f : AlgHom.type X Y) :
  forall α, f (do_action α) = do_action (Action_map f α).
Proof.
  apply: AlgHom.pres_do_action.
  apply: AlgHom.class.
Defined.

Definition do {E : Thy} {A : Alg.type E} (e : E) (k : bdry e -> ▷ A) : A.
Proof. apply: do_action; esplit; apply: k. Defined.

Definition ITree_do_action {E : Thy} {R : Set} : Action E (ITree E R) -> ITree E R.
Proof. by move=> α; apply/intro/Do/kont/α. Defined.

Definition ITree_alg_mixin {E : Thy} {R : Set} : Alg.mixin_of E (ITree E R).
Proof. by build; apply: ITree_do_action. Defined.

Canonical ITree_alg (E : Thy) (R : Set) : Alg.type E.
Proof. by esplit; apply: ITree_alg_mixin. Defined.

Lemma pres_do {E} {A B : Alg.type E} {f : AlgHom.type A  B} :
  forall e (k : bdry e -> ▷ A), f (do e k) = do e (Later.map f \o k).
Proof.
  move=> e k.
  rewrite /do.
  apply: pres_do_action.
Qed.

Definition fun_do_action {E} {A : Set} {B : Alg.type E} : Action E (A -> B) -> A -> B.
Proof.
  move=> f x.
  apply: do_action.
  move: f; apply: Action_map.
  apply; exact: x.
Defined.

Section Ext.
  Context {E : Thy} {A : Set} {B : Alg.type E}.

  Definition extends (f : A -> B) (h : ITree E A -> B) : Prop :=
    forall x, h (η x) = f x.

  Lemma extends_unique (f : A -> B) (h h' : AlgHom.type (ITree_alg E A) B) : extends f h -> extends f h' -> h = h'.
  Proof.
    move=> hext h'ext.
    apply: AlgHom.ext.
    apply: funE.
    apply: push_conn.
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
  Context {E : Thy} {A : Set} {B : Alg.type E}.
  Lemma ext_extends : forall f : A -> B, extends f f♯.
  Proof. by move=>??; rewrite /ext Later.loeb_unfold /η beta. Qed.

  Definition ext_hom_mixin (f : A -> B) : AlgHom.mixin_of _ _ f♯.
  Proof. by build; case=> ??; rewrite {1}/ext Later.loeb_unfold beta. Qed.

  Canonical ext_hom (f : A -> B) : AlgHom.type (ITree_alg E A) B.
  Proof. by esplit; apply: ext_hom_mixin. Defined.
End ExtLaws.

Section IdHom.
  Context {E : Thy} {A : Alg.type E}.
  Definition id_hom_mixin : AlgHom.mixin_of A A id.
  Proof. by build=> ?; rewrite Action_map_id. Qed.

  Canonical id_hom : AlgHom.type A A.
  Proof. by esplit; apply: id_hom_mixin. Defined.
End IdHom.

Section CmpHom.
  Context {E : Thy} {A B C : Alg.type E} (f : AlgHom.type A B) (g : AlgHom.type B C).

  Definition cmp_hom_mixin : AlgHom.mixin_of A C (fun x => g (f x)).
  Proof. by build=> ?; rewrite Action_map_cmp -?pres_do_action. Qed.

  Canonical cmp_hom : AlgHom.type A C.
  Proof. by esplit; apply: cmp_hom_mixin. Defined.
End CmpHom.

Section Bind.
  Context {E : Thy}.

  Definition bind {A B : Set} (u : ITree E A) (f : A -> ITree E B) : ITree E B := ext_hom f u.

  Lemma bind_idL {A B : Set} (x : A) (f : A -> ITree E B) : bind (η x) f = f x.
  Proof. by apply: ext_extends. Qed.

  Lemma bind_idR {A : Set} (u : ITree E A) : bind u (@η _ _) = u.
    move: u.
    rewrite /bind.
    apply: unfunE.
    congr AlgHom.map.
    unshelve apply: extends_unique.
    - by apply: η.
    - by move=> ?; apply: ext_extends.
    - by build=> ?; rewrite Action_map_id.
  Qed.

  Lemma bind_idA {A B C} (u : ITree E A) (g : A -> ITree E B) (h : B -> ITree E C) :
    bind (bind u g) h = bind u (fun x => bind (g x) h).
  Proof.
    move: u; rewrite /bind.
    apply: unfunE.
    rewrite (_ :  (fun x : ITree E A => (h) ♯ ((g) ♯ x)) = (cmp_hom (ext_hom g) (ext_hom h))); first by [].
    congr AlgHom.map.
    unshelve apply: extends_unique.
    - move=> x.
      exact: (h♯ (g x)).
    - move=> x //=.
      by rewrite ext_extends.
    - move=> x //=.
      by rewrite ext_extends.
  Qed.
End Bind.


Section Map.
  Context {E : Thy}.

  Definition map {A B : Set} (f : A -> B) : AlgHom.type (ITree_alg E A) (ITree_alg E B).
    apply: ext_hom.
    move=> x.
    apply: η (f x).
  Defined.

  Lemma map_id {A : Set} : map (id : A -> A) = id_hom.
  Proof.
    apply: AlgHom.ext; apply: funE=> u; rewrite /map.
    congr AlgHom.map.
    unshelve apply: extends_unique.
    - by exact: η.
    - by move=> ?; apply: ext_extends.
    - by [].
  Qed.

  Lemma map_cmp {A B C : Set} (f : A -> B) (g : B -> C) : map (fun x => g (f x)) = cmp_hom (map f) (map g).
  Proof.
    apply: AlgHom.ext.
    apply: funE=> u.
    congr AlgHom.map.
    unshelve apply: extends_unique.
    - move=> a.
      apply: (ext_hom (@η _ _ \o g)).
      apply: (ext_hom (@η _ _ \o f)).
      apply: η.
      apply: a.
    - move=> x.
      by rewrite //= ?ext_extends.
    - move=> x.
      by rewrite //= ?ext_extends.
  Qed.
End Map.

Module ALG.
  Section ALG.
    Context (E : Thy).

    Definition hom_mixin : Hom.mixin_of (Alg.type E).
    Proof. build; apply AlgHom.type. Defined.

    Canonical hom : Hom.type.
    Proof. esplit; apply: hom_mixin. Defined.

    Definition precat_mixin : Precategory.mixin_of hom.
    Proof.
      build.
      - move=> X Y Z f g.
        build.
        + by exact: (g \o f).
        + abstract by build=> α; case: f=> f hf; case: g=> g hg; rewrite Action_map_cmp -?pres_do_action.
      - move=> X.
        build.
        + by exact: id.
        + abstract by build=> α; rewrite Action_map_id.
    Defined.

    Canonical precat : Precategory.type.
    Proof. esplit; apply: precat_mixin. Defined.

    Definition cat_mixin : Category.mixin_of precat.
    Proof. by build; move=>*; apply: AlgHom.ext. Qed.

    Canonical cat : Category.type.
    Proof. esplit; apply: cat_mixin. Defined.
  End ALG.
End ALG.


(** The forgetful functor from algebras to types is conservative. *)
Lemma U_conservative {E} (A B : Alg.type E) (f : AlgHom.type A B) :
  forall g : B -> A,
      (forall x, f (g x) = x)
      -> (forall x, g (f x) = x)
      -> AlgHom.mixin_of _ _ g.
Proof.
  move=> g fg gf.
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
