(* Thanks, Poleiro!
   https://poleiro.info/posts/2019-12-25-quotients-in-coq.html *)

Require Import Unicode.Utf8_core.
Require Import FunctionalExtensionality.
Require Import Logic.ClassicalDescription.
Require Import Logic.PropExtensionality.
Require Import QArith.QArith.
Require Import Psatz.
Require Import Classes.Equivalence.

Local Open Scope Q.

Set Default Proof Using "Type".

Definition I_:= { q : Q | 0 < q <= 1}.

Definition I_toQ (q: I_): Q := proj1_sig q.
Definition I_toH (q: I_): (0 < I_toQ q <= 1) := proj2_sig q.

Definition I_eq (p q: I_): Prop := I_toQ p == I_toQ q.

#[ export ] Instance equiv_I: Equivalence I_eq.
Proof.
  split.
  - unfold Reflexive, I_eq.
    intros.
    apply Qeq_refl.
  - unfold Symmetric, I_eq.
    intros.
    apply (Qeq_sym _ _ H).
  - unfold Transitive, I_eq.
    intros.
    apply (Qeq_trans _ _ _ H H0).
Qed.

Definition I := { C: I_ → Prop | ∃ q, C = I_eq q }.

Lemma I_eq_split: forall C1 C2 H1 H2 (p: C1 = C2),
    eq_rect C1 (λ C, (∃ q, C = I_eq q)) H1 C2 p = H2 
  → (exist _ C1 H1 : I) = (exist _ C2 H2 : I).
Proof.
  intros.
  destruct p.
  simpl in H.
  rewrite <- H.
  reflexivity.
Qed.

Definition liftI (q: I_): I := exist _ (I_eq q) (ex_intro _ q eq_refl).

Lemma liftI_inj: ∀ {p q}, liftI p = liftI q → I_eq p q.
Proof.
  intros.
  injection H as H.
  rewrite H.
  apply equiv_I.
Qed.

Lemma eq_liftI: ∀ {p q}, I_eq p q → liftI p = liftI q.
Proof.
  intros.
  unfold liftI.
  assert (I_eq p = I_eq q).
  - apply functional_extensionality; intros.
    apply propositional_extensionality.
    split; intros.
    + rewrite <- H0.
      symmetry.
      apply H.
    + rewrite <- H0.
      apply H.
  - apply (I_eq_split _ _ _ _ H0).
    apply proof_irrelevance.
Qed.

Lemma I_inv: ∀ q, ∃ x, q = liftI x.
Proof.
  intros.
  destruct q.
  destruct e.
  rewrite e.
  exists x0.
  auto.
Qed.

Section Elim.

  Variable (S: I → Type) (f: ∀ x, S (liftI x)).
  Hypothesis (fP: ∀ x y (e: I_eq x y), eq_rect _ S (f x) _ (eq_liftI e) = f y).

  Lemma I_rect_subproof: ∀ (q: I),
    ∃ (a: S q), unique (λ a, ∃ x (eq: liftI x = q), a = eq_rect _ S (f x) _ eq) a.
  Proof using fP.
    intros.
    pose proof I_inv q.
    destruct H.
    rewrite H.
    exists (f x).
    unfold unique.
    split.
    - exists x.
      assert (liftI x = liftI x).
      + reflexivity.
      + exists ((eq_liftI (liftI_inj H0))).
        symmetry.
        eapply fP.
    - intros y ?.
      destruct H0 as [?[??]].
      specialize (fP x0 x).
      rewrite H0.
      symmetry.
      pose proof liftI_inj x1.
      assert (x1 = (eq_liftI H1)).
      + apply proof_irrelevance.
      + rewrite H2.
        apply (fP H1).
  Qed.

  Definition I_rect q: S q :=
    proj1_sig (constructive_definite_description _ (I_rect_subproof q)).

  Lemma I_rectE: ∀ x, I_rect (liftI x) = f x.
  Proof using.
    intros.
    unfold I_rect.
    destruct (constructive_definite_description _) as [?[?[??]]].
    simpl.
    rewrite e.
    pose (eq_liftI (liftI_inj x2)).
    specialize (fP x1 x (liftI_inj x2)).
    rewrite <- fP.
    f_equal.
    apply proof_irrelevance.
  Qed.

End Elim.

Lemma eq_rect_const: ∀ {A B} {x y: A} {b: B} {p: x = y},
    eq_rect x (λ _, B) b y p = b.
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Qed.

Definition I_rec {A: Type} (f: I_ → A) (H: ∀ p q, I_eq p q → f p = f q): I → A :=
  I_rect (λ _, A) f (λ p q e, eq_trans eq_rect_const (H p q e)).

Lemma I_recE: ∀ {A} {f: I_ → A} {H p}, I_rec f H (liftI p) = f p.
Proof.
  intros.
  unfold I_rec.
  pose proof I_rectE.
  specialize (H0 (λ _, A) f).
  apply H0.
Qed.

Section Iadd_aux1.

  Variable (p q: Q).

  Let f := λ (r: I_), p + q == I_toQ r.

  Let H: ∀ r r', I_eq r r' → f r = f r'.
  Proof.
    intros.
    apply propositional_extensionality.
    unfold f.
    split; intros.
    - rewrite H0.
      apply H.
    - rewrite H0.
      symmetry.
      apply H.
  Qed.

  Definition Iadd_aux1: I → Prop := I_rec f H.

  Lemma Iadd_aux1E: ∀ r, Iadd_aux1 (liftI r) ↔ p + q == I_toQ r.
  Proof.
    intros.
    split; intros.
    - unfold Iadd_aux1 in H0.
      rewrite I_recE in H0.
      apply H0.
    - unfold Iadd_aux1.
      rewrite I_recE.
      apply H0.
  Qed.

End Iadd_aux1.

Section Iadd_aux2.

  Variable (p: Q).

  Let f := λ (q: I_), Iadd_aux1 p (I_toQ q).

  Let H: ∀ r r', I_eq r r' → f r = f r'.
  Proof.
    intros.
    apply functional_extensionality; intros.
    unfold f.
    apply propositional_extensionality.
    split; intros.
    - pose proof I_inv x as [??].
      subst x.
      apply Iadd_aux1E.
      apply Iadd_aux1E in H0.
      rewrite <- H0.
      unfold I_eq in H.
      rewrite H.
      reflexivity.
    - pose proof I_inv x as [??].
      subst x.
      apply Iadd_aux1E.
      apply Iadd_aux1E in H0.
      rewrite <- H0.
      unfold I_eq in H.
      rewrite H.
      reflexivity.
  Qed.

  Definition Iadd_aux2: I → I → Prop := I_rec f H.

  Lemma Iadd_aux2E: ∀ q r, Iadd_aux2 (liftI q) (liftI r) ↔ p + I_toQ q == I_toQ r.
  Proof.
    intros.
    split; intros.
    - unfold Iadd_aux2 in H0.
      rewrite I_recE in H0.
      unfold f in H0.
      apply Iadd_aux1E.
      exact H0.
    - unfold Iadd_aux2.
      rewrite I_recE.
      unfold f.
      apply Iadd_aux1E.
      exact H0.
  Qed.

End Iadd_aux2.

Section Iadd.

  Let f := λ (p: I_), Iadd_aux2 (I_toQ p).

  Let H: ∀ p q, I_eq p q → f p = f q.
  Proof.
    intros.
    apply functional_extensionality; intros.
    apply functional_extensionality; intros.
    unfold f.
    apply propositional_extensionality.
    split; intros.
    - pose proof I_inv x as [??].
      subst x.
      pose proof I_inv x0 as [??].
      subst x0.
      apply Iadd_aux2E.
      apply Iadd_aux2E in H0.
      rewrite <- H0.
      unfold I_eq in H.
      rewrite H.
      reflexivity.
    - pose proof I_inv x as [??].
      subst x.
      pose proof I_inv x0 as [??].
      subst x0.
      apply Iadd_aux2E.
      apply Iadd_aux2E in H0.
      rewrite <- H0.
      unfold I_eq in H.
      rewrite H.
      reflexivity.
  Qed.

  Definition Iadd: I → I → I → Prop := I_rec f H.

  Lemma IaddE: ∀ p q r, Iadd (liftI p) (liftI q) (liftI r) ↔ I_toQ p + I_toQ q == I_toQ r.
  Proof.
    intros.
    split; intros.
    - unfold Iadd in H0.
      rewrite I_recE in H0.
      unfold f in H0.
      apply Iadd_aux2E.
      exact H0.
    - unfold Iadd.
      rewrite I_recE.
      unfold f.
      apply Iadd_aux2E.
      exact H0.
  Qed.

End Iadd.

Lemma one_in_I: 0 < 1%Q <= 1.
Proof. psatz Q. Qed.

Definition I1 := liftI (exist _ 1 one_in_I).

Ltac invI x := pose proof (I_inv x) as [??]; subst x.

Lemma I_add_pos: ∀ {p0 q: I_}, I_toQ p0 + I_toQ q > 0.
Proof.
  intros.
  pose proof I_toH p0.
  pose proof I_toH q.
  psatz Q.
Qed.

Section Iadd_opt_aux.

  Variable (p: I_).

  Let f: ∀ (q: I_), option I := λ (q: I_),
    match Qlt_le_dec 1 (I_toQ p + I_toQ q) with
    | left H => None
    | right H => Some (liftI (exist _ (I_toQ p + I_toQ q) (conj I_add_pos H)))
    end.

  Let H: ∀ q q', I_eq q q' → f q = f q'.
  Proof.
    intros.
    unfold f.
    unfold I_eq in H.
    destruct (Qlt_le_dec 1 (I_toQ p + I_toQ q));
    destruct (Qlt_le_dec 1 (I_toQ p + I_toQ q')).
    - reflexivity.
    - exfalso. psatz Q.
    - exfalso. psatz Q.
    - f_equal.
      apply eq_liftI.
      unfold I_eq.
      simpl.
      psatz Q.
  Qed.

  Definition Iadd_opt_aux: I → option I := I_rec f H.

  Lemma Iadd_opt_auxE: ∀ q, Iadd_opt_aux (liftI q) =
    match Qlt_le_dec 1 (I_toQ p + I_toQ q) with
    | left H => None
    | right H => Some (liftI (exist _ (I_toQ p + I_toQ q) (conj I_add_pos H)))
    end.
  Proof.
    intros.
    unfold Iadd_opt_aux.
    rewrite I_recE.
    unfold f.
    reflexivity.
  Qed.

End Iadd_opt_aux.

Section Iadd_opt.

  Let f: I_ → I → option I := Iadd_opt_aux.

  Let H: ∀ p p', I_eq p p' → f p = f p'.
  Proof.
    intros.
    apply functional_extensionality; intros.
    unfold f.
    invI x.
    rewrite! Iadd_opt_auxE.
    unfold I_eq in H.
    destruct (Qlt_le_dec 1 (I_toQ p + I_toQ x0));
    destruct (Qlt_le_dec 1 (I_toQ p' + I_toQ x0)).
    - reflexivity.
    - exfalso. psatz Q.
    - exfalso. psatz Q.
    - f_equal.
      apply eq_liftI.
      unfold I_eq.
      simpl.
      psatz Q.
  Qed.

  Definition Iadd_opt: I → I → option I := I_rec f H.

  Lemma Iadd_optE: ∀ p q, Iadd_opt (liftI p) (liftI q) =
    match Qlt_le_dec 1 (I_toQ p + I_toQ q) with
    | left H => None
    | right H => Some (liftI (exist _ (I_toQ p + I_toQ q) (conj I_add_pos H)))
    end.
  Proof.
    intros.
    unfold Iadd_opt.
    rewrite I_recE.
    unfold f.
    unfold Iadd_opt_aux.
    rewrite I_recE.
    reflexivity.
  Qed.

End Iadd_opt.
