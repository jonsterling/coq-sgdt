From sgdt Require Import preamble.

(** Easier than activating -impredicative-set. *)
#[bypass_check(universes = yes)]
Definition All {A : Type} (B : A -> Set) : Set :=
  forall x : A, B x.

Notation "'⋀' x .. y , p" := (All (fun x => .. (All (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '⋀' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Module Reflection.
  Section Defs.
    Context (A : Type).

    Definition pre : Set :=
      ⋀ X : Set, (⋀ _ : A, X) -> X.

    Definition ok (α : pre) : Prop :=
      forall (X Y : Set) (f : X -> Y) (h : A -> X),
        α Y ((fun g x => f (g x)) h) = f (α X h).

    Definition T : Set :=
      {α : pre | ok α}.
  End Defs.

  Section Unit.
    Context {A : Type}.

    Definition unit_pre : A -> pre A.
    Proof. by move=> a X; apply. Defined.

    Lemma unit_pre_ok (x : A) : ok _ (unit_pre x).
    Proof. by []. Qed.

    Definition unit : A -> T A.
    Proof. by move=> a; exists (unit_pre a); apply: unit_pre_ok. Defined.
  End Unit.

  Section Map.
    Context {A B : Type} (f : A -> B).

    Definition map_pre : pre A -> pre B.
    Proof. by move=> α X h; apply: α=>/f/h. Defined.

    Definition map_pre_ok : forall α : pre A, ok A α -> ok B (map_pre α).
    Proof. by move=> α hα X Y g h; rewrite -hα. Qed.

    Definition map : T A -> T B.
    Proof.
      move=> x.
      exists (map_pre (pi1 x)).
      apply: map_pre_ok.
      by apply pi2.
    Defined.

    Definition map_beta : forall x, map (unit x) = unit (f x).
    Proof. by move=> ?; apply: subE. Qed.
  End Map.

  Section Alg.
    Context {A : Set}.

    Definition alg : T A -> A.
    Proof. by move=> /pi1 α; apply: (α A). Defined.

    Definition alg_beta : forall x : A, alg (unit x) = x.
    Proof. by []. Qed.

    Definition alg_eta : forall x : T A, x = unit (alg x).
    Proof.
      move=> α.
      apply: subE =>//=.
      apply: dfunE => X.
      apply: funE => ?.
      by rewrite /unit_pre /alg -(pi2 α).
    Qed.
  End Alg.

  Section Ext.
    Context {A : Type} {B : Set} (f : A -> B).

    Definition ext : T A -> B.
    Proof. by move=> x; apply: alg; apply: map f x. Defined.

    Lemma ext_beta : forall x, ext (unit x) = f x.
    Proof. by move=> ?; rewrite /ext map_beta alg_beta. Qed.
  End Ext.

  Section ExtEta.
    Context {A : Type} {B : Set}.

    (* Argument due to Awodey, Frey, Speight *)
    Lemma ext_eta : forall h : T A -> B, ext (h \o unit) = h.
    Proof.
      move=> h.
      apply: funE=> α.
      rewrite /ext /alg /map /map_pre //= (pi2 α).
      congr h.
      apply: subE=>//=.
      apply: dfunE=> X.
      apply: funE=> f.
      rewrite
        (_ : (pi1 (pi1 α (T A) unit) X f) = ext f (pi1 α _ unit)) //=
        /ext -(pi2 α _ _ (map f))
        (_ : (fun x : A => map f (unit x)) = (fun x => unit (f x))).
      - by apply: funE=> ?; apply: map_beta.
      - by rewrite (pi2 α) alg_beta.
    Qed.

    Context (f : A -> B).

    Definition is_univ_map (h : T A -> B) := forall x, h (unit x) = f x.

    Lemma univ_map_uniq h1 h2 : is_univ_map h1 -> is_univ_map h2 -> h1 = h2.
    Proof.
      move=> hh1 hh2.
      rewrite -(ext_eta h1) -(ext_eta h2).
      congr ext.
      apply: funE=>?//=.
      by rewrite hh1 hh2.
    Qed.
  End ExtEta.
End Reflection.

Definition Ex {A : Type} (B : A -> Set) : Set :=
  Reflection.T {x : A & B x}.

Notation "'⋁' x .. y , p" := (Ex (fun x => .. (Ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '⋁' '/ ' x .. y , '/ ' p ']'")
  : type_scope.


Section PackUnpack.
  Context {A : Type} {B : A -> Set}.

  Definition pack (a : A) (b : B a) : ⋁ x : A, B x.
  Proof.
    apply: Reflection.unit.
    exists a; exact: b.
  Defined.

  Definition unpack {C : Set} (f : forall x : A, B x -> C) (u : ⋁ x : A, B x) : C.
    move: u.
    apply Reflection.ext; case.
    apply: f.
  Defined.
End PackUnpack.
