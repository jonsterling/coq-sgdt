From SGDT Require Import Prelude GuardedLF.

Set Universe Polymorphism.

Module Type Printable.
  Parameter O : Type.
  Parameter ϵ : O.
End Printable.


Module Effect (O : Printable).
  Import O.

  Definition 𝔼 A := O × ▷ A.

  Definition 𝔼_map {A B} (f : A -> B) : 𝔼 A -> 𝔼 B.
  Proof.
    move=> x; split.
    - exact: (pi1 x).
    - move: (pi2 x).
      apply/Later.map/f.
  Defined.

  Class 𝔼_alg A := push : 𝔼 A -> A.

  Definition 𝔼_alg_hom {A B} `{𝔼_alg A} `{𝔼_alg B} (f : A -> B) : Prop :=
    forall x, f (push x) = push (𝔼_map f x).

  Lemma 𝔼_alg_hom_cmp {A B C} `{𝔼_alg A} `{𝔼_alg B} `{𝔼_alg C} (f : A -> B) (g : B -> C) : 𝔼_alg_hom f -> 𝔼_alg_hom g -> 𝔼_alg_hom (g \o f).
  Proof.
    move=> fhom ghom x /=.
    by rewrite fhom /𝔼_map ghom /𝔼_map /= Later.map_assoc.
  Qed.


  Inductive F' (A : Type) (R : ▷ Type) :=
  | now : A -> F' A R
  | step : O -> dlater R -> F' A R.

  Definition F (A : Type) : Type := Later.loeb (F' A).

  Instance F_conn {A : Type} : Connective (F A) (F' A (next (F A))).
  Proof. by split; apply: loeb_iso. Defined.

  Opaque F.

  Instance F_is_𝔼_alg {A} : 𝔼_alg (F A).
  Proof.
    move=> x.
    apply/intro/step.
    - exact: (pi1 x).
    - apply: intro.
      exact: (pi2 x).
  Defined.

  Instance FunAlg {A B} `{𝔼_alg B} : 𝔼_alg (A -> B).
  Proof.
    move => f x.
    apply: push.
    move: f.
    apply: 𝔼_map.
    by apply.
  Defined.

  Definition η {A : Type} : A -> F A.
  Proof. move=> x; apply/intro/now/x. Defined.

  Module UniversalProperty.
    Definition extend {A B} `{𝔼_alg B} (f : A -> B) : F A -> B.
    Proof.
      apply: Later.loeb => f'.
      case/elim.
      - exact: f.
      - move=> o /elim x.
        apply: push; split.
        + exact: o.
        + exact: (f' ⊛ x).
    Defined.

    Notation "f ♯" := (extend f) (at level 0).

    Lemma extend_extends {A B} `{𝔼_alg B} (f : A -> B) : forall x, f ♯ (η x) = f x.
    Proof. by move=> x; rewrite /extend /η Later.loeb_unfold beta. Qed.

    Lemma extend_is_hom {A B} {pushB : 𝔼_alg B} (f : A -> B) : 𝔼_alg_hom f♯.
    Proof. by move=>?; rewrite {1}/extend Later.loeb_unfold /push /F_is_𝔼_alg ?beta. Qed.


    Lemma extend_uniq {A B} {pushB : 𝔼_alg B} (f : A -> B) : forall h : F A -> B, 𝔼_alg_hom h -> (forall x, h (η x) = f x) -> h = extend f.
    Proof.
      move=> h h_hom H.
      apply: funE.
      apply: (push_iso conn_def).
      apply: Later.loeb => ih.
      elim.
      - by move=> ?; rewrite H /extend Later.loeb_unfold beta.
      - move=> o.
        apply: (push_iso dlater_next) => l.
        rewrite /𝔼_alg_hom /push /F_is_𝔼_alg in h_hom.
        rewrite (h_hom (Sig o l)) /extend Later.loeb_unfold beta /push /𝔼_map.
        congr pushB; congr Sig; rewrite beta /Later.map; congr (_⊛_).
        apply: Later.from_eq.
        move: ih; apply: Later.map => ih.
        apply: funE.
        by apply: (push_iso conn_def).
    Qed.
  End UniversalProperty.

  Import UniversalProperty.

  Definition bind {A B : Type} : F A -> (A -> F B) -> F B.
  Proof. by move/[swap]; apply: extend. Defined.

  Infix ">>=" := bind (at level 10).



  Module MonadLaws.
    Lemma bindr {A : Type} : forall (m : F A), m >>= η = m.
    Proof.
      apply: unfunE.
      rewrite [id](extend_uniq η) // => [[o m]].
      by rewrite /𝔼_map /= map_id.
    Qed.

    Lemma bindl {A B : Type} : forall (x : A) (k : A -> F B), η x >>= k = k x.
    Proof. by move=>??; rewrite /η /bind /extend Later.loeb_unfold beta. Qed.

    Lemma binda {A B C : Type} : forall (m : F A) (g : A -> F B) (h : B -> F C), (m >>= g) >>= h = m >>= (fun x => g x >>= h).
    Proof.
      move=> + g h.
      apply/unfunE/extend_uniq.
      - by rewrite /bind; apply: 𝔼_alg_hom_cmp; exact: extend_is_hom.
      - by move=> ?; rewrite bindl.
    Qed.
  End MonadLaws.

  Import MonadLaws.

  Definition ltr_alg_from_𝔼_alg {A : Type} {pushA : 𝔼_alg A} : ▷ A -> A.
  Proof.
    move=> m.
    apply: pushA; split.
    - exact: ϵ.
    - exact: m.
  Defined.

  Definition ltr_alg_F {A : Type} : ▷ F A -> F A.
  Proof. apply: ltr_alg_from_𝔼_alg. Defined.

  Definition μ {A : Type} : F (F A) -> F A.
  Proof. exact: (extend id). Defined.

  Definition mapF {A B : Type} : (A -> B) -> F A -> F B.
  Proof.
    move=> f x.
    apply: (bind x).
    by move=> z; apply/η/f/z.
  Defined.

  Lemma seq_assoc {A B C : Type} `{𝔼_alg C} :
    forall (M : F A) (N : A -> F B) {P : B -> C},
      P♯ (N♯ M) = (P♯ \o N)♯ M.
  Proof.
    move=> M N P; move: M.
    apply/unfunE/extend_uniq.
    - by apply: 𝔼_alg_hom_cmp; exact: extend_is_hom.
    - by move=> ?; rewrite extend_extends.
  Qed.

  Lemma seq_ret {A : Type} : forall M : F A, η♯ M = M.
  Proof.
    move=> M.
    by rewrite (_ : η♯ M = M >>= η) // bindr.
  Qed.

  Lemma seq_fun {A B C : Type} `{𝔼_alg C}:
    forall (M : F A) (N : A -> B -> C),
      N ♯ M = fun y => (N^~ y)♯ M.
  Proof.
    move=> M N; apply: funE => O; move: M; apply/unfunE/extend_uniq.
    - by move=> ?; rewrite extend_is_hom {1}/push /FunAlg /𝔼_map Later.map_assoc /=.
    - by move=> ?; rewrite extend_extends.
  Qed.
End Effect.
