From SGDT Require Import Prelude GuardedLF.

Set Universe Polymorphism.

Module Type Printable.
  Parameter O : Type.
  Parameter ϵ : O.
End Printable.


Module Effect (O : Printable).
  Import O.

  Definition 𝔼 A := O × ▷ A.

  Definition 𝔼_map {A B} (f : A → B) : 𝔼 A → 𝔼 B.
  Proof.
    move=> x; split.
    - exact: x.1.
    - move: x.2.
      apply/Later.map/f.
  Defined.

  Class 𝔼_alg A := push : 𝔼 A → A.

  Definition 𝔼_alg_hom {A B} `{𝔼_alg A} `{𝔼_alg B} (f : A → B) : Prop :=
    ∀ x, f (push x) = push (𝔼_map f x).

  Lemma 𝔼_alg_hom_cmp {A B C} `{𝔼_alg A} `{𝔼_alg B} `{𝔼_alg C} (f : A → B) (g : B → C) : 𝔼_alg_hom f → 𝔼_alg_hom g → 𝔼_alg_hom (g \o f).
  Proof.
    move=> fhom ghom x /=.
    rewrite fhom /𝔼_map ghom; congr push.
    rewrite /𝔼_map /=; congr (_,_).
    move: {x} x.2 => x.
    by rewrite Later.map_assoc.
  Qed.


  Inductive F' (A : Type) (R : ▷ Type) :=
  | now : A → F' A R
  | step : O → dlater R → F' A R.

  Definition F (A : Type) : Type := Later.loeb (F' A).

  Definition F_def {A : Type} : F' A (next (F A)) ≅ F A.
  Proof. apply: loeb_iso. Qed.

  Opaque F.

  Notation F_intro := (intro F_def).
  Notation F_elim := (elim F_def).
  Notation F_beta := (beta F_def).
  Notation F_eta := (eta F_def).

  Instance F_is_𝔼_alg {A} : 𝔼_alg (F A).
  Proof.
    move=> x.
    apply: F_intro.
    apply: step.
    - exact: (fst x).
    - apply: (intro dlater_next).
      exact: (snd x).
  Defined.

  Instance FunAlg {A B} `{𝔼_alg B} : 𝔼_alg (A → B).
  Proof.
    move => f x.
    apply: push.
    move: f.
    apply: 𝔼_map.
    by apply.
  Defined.

  Definition η {A : Type} : A → F A.
  Proof. move=> x; apply/F_intro/now/x. Defined.

  Module UniversalProperty.
    Definition extend {A B} `{𝔼_alg B} (f : A → B) : F A → B.
    Proof.
      apply: Later.loeb => f'.
      case/F_elim.
      - exact: f.
      - move=> o /(elim dlater_next) x.
        apply: push; split.
        + exact: o.
        + exact: (f' ⊛ x).
    Defined.

    Notation "f ♯" := (extend f) (at level 0).

    Lemma extend_extends {A B} `{𝔼_alg B} (f : A → B) : ∀ x, f ♯ (η x) = f x.
    Proof. by move=> x; rewrite /extend /η Later.loeb_unfold beta. Qed.

    Lemma extend_is_hom {A B} {pushB : 𝔼_alg B} (f : A → B) : 𝔼_alg_hom f♯.
    Proof. by move=>?; rewrite {1}/extend Later.loeb_unfold /push /F_is_𝔼_alg ?beta. Qed.


    Lemma extend_uniq {A B} {pushB : 𝔼_alg B} (f : A → B) : ∀ h : F A → B, 𝔼_alg_hom h → (∀ x, h (η x) = f x) → h = extend f.
    Proof.
      move=> h h_hom H.
      apply: funext.
      apply: (push_iso F_def).
      apply: Later.loeb => ih.
      elim.
      - by move=> ?; rewrite H /extend Later.loeb_unfold beta.
      - move=> o.
        apply: (push_iso dlater_next) => l.
        rewrite /𝔼_alg_hom /push /F_is_𝔼_alg in h_hom.
        rewrite (h_hom (o, l)) /extend Later.loeb_unfold beta /push /𝔼_map.
        congr pushB; congr (_,_); rewrite beta /Later.map; congr (_⊛_).
        apply: Later.from_eq.
        move: ih; apply: Later.map => ih.
        apply: funext.
          by apply: (push_iso F_def).
    Qed.
  End UniversalProperty.

  Import UniversalProperty.

  Definition bind {A B : Type} : F A → (A → F B) → F B.
  Proof. by move/[swap]; apply: extend. Defined.

  Infix ">>=" := bind (at level 10).



  Module MonadLaws.
    Lemma bindr {A : Type} : ∀ (m : F A), m >>= η = m.
    Proof.
      apply: unfunext; symmetry.
      apply: extend_uniq; last by [].
      move=> [o m].
      rewrite /𝔼_map /=.
      congr (push (_,_)).
      move: m; apply: Later.loeb => ih m.
        by rewrite /Later.map Later.ap_id.
    Qed.

    Lemma bindl {A B : Type} : ∀ (x : A) (k : A → F B), η x >>= k = k x.
    Proof. by move=>??; rewrite /η /bind /extend Later.loeb_unfold beta. Qed.


    Lemma binda {A B C : Type} : ∀ (m : F A) (g : A → F B) (h : B → F C), (m >>= g) >>= h = m >>= (λ x, g x >>= h).
    Proof.
      move=> m g h; move: m.
      apply: unfunext; apply: extend_uniq.
      - by rewrite /bind; apply: 𝔼_alg_hom_cmp; apply: extend_is_hom.
      - by move=> ?; rewrite bindl.
    Qed.
  End MonadLaws.

  Import MonadLaws.

  Definition ltr_alg_from_𝔼_alg {A : Type} {pushA : 𝔼_alg A} : ▷ A → A.
  Proof.
    move=> m.
    apply: pushA; split.
    - exact: ϵ.
    - exact: m.
  Defined.

  Definition ltr_alg_F {A : Type} : ▷ F A → F A.
  Proof. apply: ltr_alg_from_𝔼_alg. Defined.

  Definition μ {A : Type} : F (F A) → F A.
  Proof. exact: (extend id). Defined.

  Definition mapF {A B : Type} : (A → B) → F A → F B.
  Proof.
    move=> f x.
    apply: (bind x).
      by move=> z; apply/η/f/z.
  Defined.

  Lemma seq_assoc {A B C : Type} `{𝔼_alg C} :
    ∀ (M : F A) (N : A → F B) {P : B → C},
      P♯ (N♯ M) = (P♯ \o N)♯ M.
  Proof.
    move=> M N P; move: M.
    apply: unfunext; apply: extend_uniq.
    - by apply: 𝔼_alg_hom_cmp; apply: extend_is_hom.
    - by move=> x; rewrite extend_extends.
  Qed.

  Lemma seq_ret {A : Type} : ∀ M : F A, η♯ M = M.
  Proof.
    move=> M.
    rewrite (_ : η♯ M = M >>= η); first by [].
      by rewrite bindr.
  Qed.

  Lemma seq_fun {A B C : Type} `{𝔼_alg C}:
    ∀ (M : F A) (N : A → B → C),
      N ♯ M = λ y, (N^~ y)♯ M.
  Proof.
    move=> M N.
    apply: funext => z; move: M.
    apply: unfunext; apply: extend_uniq.
    - by move=> ?; rewrite extend_is_hom {1}/push /FunAlg /𝔼_map Later.map_assoc /=.
    - by move=> ?; rewrite extend_extends.
  Qed.

End Effect.
