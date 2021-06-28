From SGDT Require Import Prelude GuardedLF.

Set Universe Polymorphism.

Axiom O : Type.
Axiom ϵ : O.

Definition W A := prod O (▷ A).
Definition W_map {A B} (f : A → B) : W A → W B.
  move=> x.
  split.
  - exact: (fst x).
  - move: (snd x).
    apply: Later.map.
    exact: f.
Defined.

Class W_alg A := push : W A → A.

Definition W_alg_hom {A B} `{W_alg A} `{W_alg B} (f : A → B) : Prop :=
  ∀ x, f (push x) = push (W_map f x).

Inductive F' (A : Type) (R : ▷ Type) :=
| now : A → F' A R
| step : O → dlater R → F' A R.

Definition F (A : Type) : Type.
Proof.
  apply: Later.loeb => R.
  refine (F' A R).
Defined.

Definition F_def {A : Type} : F' A (next (F A)) ≅ F A.
Proof. apply: loeb_iso. Defined.

Notation F_intro := (intro F_def).
Notation F_elim := (elim F_def).
Notation F_beta := (beta F_def).
Notation F_eta := (eta F_def).

Instance F_is_W_alg {A} : W_alg (F A).
Proof.
  move=> x.
  apply: F_intro.
  apply: step.
  - exact: (fst x).
  - apply: (intro dlater_next).
    exact: (snd x).
Defined.

Instance FunAlg {A B} `{W_alg B} : W_alg (A → B).
Proof.
  move => f x.
  apply: push.
  move: f.
  apply: W_map.
  by apply.
Defined.

Definition η {A : Type} : A → F A.
Proof. move=> x; apply/F_intro/now/x. Defined.

Definition extend {A B} `{W_alg B} (f : A → B) : F A → B.
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

Lemma extend_extends {A B} `{W_alg B} (f : A → B) : ∀ x, f ♯ (η x) = f x.
Proof. by move=> x; rewrite /extend /η Later.loeb_unfold beta. Qed.

Lemma W_alg_hom_cmp {A B C} `{W_alg A} `{W_alg B} `{W_alg C} (f : A → B) (g : B → C) : W_alg_hom f → W_alg_hom g → W_alg_hom (g \o f).
Proof.
  move=> fhom ghom x /=.
  rewrite fhom /W_map ghom; congr push.
  rewrite /W_map /=; congr (_,_).
  move: {x} x.2 => x.
  by rewrite Later.map_assoc.
Qed.

Lemma extend_is_hom {A B} {pushB : W_alg B} (f : A → B) : W_alg_hom f♯.
Proof. by move=>?; rewrite {1}/extend Later.loeb_unfold /push /F_is_W_alg ?beta. Qed.


Lemma extend_uniq {A B} {pushB : W_alg B} (f : A → B) : ∀ h : F A → B, W_alg_hom h → (∀ x, h (η x) = f x) → h = extend f.
Proof.
  move=> h h_hom H.
  apply: funext.
  apply: (push_iso F_def).
  apply: Later.loeb => ih.
  elim.
  - by move=> ?; rewrite H /extend Later.loeb_unfold beta.
  - move=> o.
    apply: (push_iso dlater_next) => l.
    rewrite /W_alg_hom /push /F_is_W_alg in h_hom.
    rewrite (h_hom (o, l)) /extend Later.loeb_unfold beta /push /W_map.
    congr pushB; congr (_,_); rewrite beta /Later.map; congr (_⊛_).
    apply: Later.from_eq.
    move: ih; apply: Later.map => ih.
    apply: funext.
    by apply: (push_iso F_def).
Qed.

Definition bind {A B : Type} : F A → (A → F B) → F B.
Proof. by move/[swap]; apply: extend. Defined.

Infix ">>=" := bind (at level 10).


Lemma bindr {A : Type} : ∀ (m : F A), m >>= η = m.
Proof.
  apply: unfunext; symmetry.
  apply: extend_uniq; last by [].
  move=> [o m].
  rewrite /W_map /=.
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
  - by rewrite /bind; apply: W_alg_hom_cmp; apply: extend_is_hom.
  - by move=> ?; rewrite bindl.
Qed.


Definition ltr_alg_from_W_alg {A : Type} {pushA : W_alg A} : ▷ A → A.
Proof.
  move=> m.
  apply: pushA; split.
  - exact: ϵ.
  - exact: m.
Defined.

Definition ltr_alg_F {A : Type} : ▷ F A → F A.
Proof. apply: ltr_alg_from_W_alg. Defined.

Definition μ {A : Type} : F (F A) → F A.
Proof. exact: (extend id). Defined.

Definition mapF {A B : Type} : (A → B) → F A → F B.
Proof.
  move=> f x.
  apply: (bind x).
  by move=> z; apply/η/f/z.
Defined.

Lemma seq_assoc {A B C : Type} `{W_alg C} :
  ∀ (M : F A) (N : A → F B) {P : B → C},
    extend P (extend N M) =
    extend (λ x, extend P (N x)) M.
Proof.
  move=> M N P; move: M.
  apply: unfunext; apply: extend_uniq.
  - by apply: W_alg_hom_cmp; apply: extend_is_hom.
  - by move=> x; rewrite extend_extends.
Qed.

Lemma seq_ret {A : Type} : ∀ M : F A, extend η M = M.
Proof.
  move=> M.
  rewrite (_ : extend η M = bind M η); first by [].
  by rewrite bindr.
Qed.

Lemma seq_fun {A B C : Type} `{W_alg C}:
  ∀ (M : F A) (N : A → B → C),
    extend (λ x, λ y, N x y) M = λ y, extend (λ x, N x y) M.
Proof.
  move=> M N.
  apply: funext => z; move: M.
  apply: unfunext; apply: extend_uniq.
  - by move=> ?; rewrite extend_is_hom {1}/push /FunAlg /W_map Later.map_assoc /=.
  - by move=> ?; rewrite extend_extends.
Qed.
