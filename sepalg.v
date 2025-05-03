Require Import Unicode.Utf8_core.
Require Import Strings.String.
Require Import ZArith.ZArith.
Require Import QArith.QArith.
Require Import Psatz.
Require Import FunctionalExtensionality.

Require Import thesis.interval.

Local Open Scope Q.

Ltac invert H := inversion H; subst; clear H.

Class MultiUnitSepAlg (Σ: Type): Type :=
  {
    join: Σ → Σ → Σ → Prop;
    MSA_fun: ∀ {x y z1 z2}, join x y z1 → join x y z2 → z1 = z2;
    MSA_cancel: ∀ {x1 x2 y z}, join x1 y z → join x2 y z → x1 = x2;
    MSA_comm: ∀ {x y z}, join x y z → join y x z;
    MSA_assoc: ∀ {x y z a b}, join x y a → join a z b → { c | join y z c ∧ join x c b };
    MSA_unit: ∀ x, { u | join u x x };
    MSA_positive: ∀ {a b c}, join a b c → join c c c → join a a a;
  }.

#[export] Instance discrete_MSA {A}: MultiUnitSepAlg A.
Proof.
  refine {| join := λ x y z, x = z ∧ y = z; MSA_fun := _; MSA_cancel := _; MSA_comm := _; MSA_assoc := _; MSA_unit := _ |}.
  - intuition.
    subst.
    reflexivity.
  - intuition.
    subst.
    reflexivity.
  - intuition.
  - intuition.
    subst.
    exists b.
    tauto.
  - intuition.
    exists x.
    tauto.
  - intuition.
Defined.

#[export] Instance prod_MSA {A} {B} `(MultiUnitSepAlg A, MultiUnitSepAlg B): MultiUnitSepAlg (A * B).
Proof.
  refine {| join := λ x y z, join (fst x) (fst y) (fst z) ∧ join (snd x) (snd y) (snd z); MSA_fun := _; MSA_cancel := _; MSA_comm := _; MSA_assoc := _; MSA_unit := _ |}.
  - intros.
    destruct x, y, z1, z2, H1, H2.
    pose proof MSA_fun H1 H2.
    pose proof MSA_fun H3 H4.
    simpl in *; subst.
    reflexivity.
  - intros.
    destruct x1, x2, y, z, H1, H2.
    pose proof MSA_cancel H1 H2.
    pose proof MSA_cancel H3 H4.
    simpl in *; subst.
    reflexivity.
  - intros.
    destruct x, y, z, H1.
    pose proof MSA_comm H1.
    pose proof MSA_comm H2.
    tauto.
  - intros.
    destruct x, y, z, a, b, H1, H2.
    pose proof MSA_assoc H1 H2 as [? [? ?]].
    pose proof MSA_assoc H3 H4 as [? [? ?]].
    exists (x, x0).
    tauto.
  - intros.
    destruct x.
    pose proof MSA_unit a as [? ?].
    pose proof MSA_unit b as [? ?].
    exists (x, x0).
    tauto.
  - intros.
    destruct a, b, c, H1, H2.
    pose proof MSA_positive H1 H2.
    pose proof MSA_positive H3 H4.
    tauto.
Defined.

#[export] Instance index_prod_MSA {A} {B} `(MultiUnitSepAlg B): MultiUnitSepAlg (A → B).
Proof.
  refine {| join := λ f g h, ∀ a, join (f a) (g a) (h a); MSA_fun := _; MSA_cancel := _; MSA_comm := _; MSA_assoc := _; MSA_unit := _ |}.
  - intros.
    apply functional_extensionality.
    intros a.
    specialize (H0 a).
    specialize (H1 a).
    apply (MSA_fun H0 H1).
  - intros.
    apply functional_extensionality.
    intros a.
    specialize (H0 a).
    specialize (H1 a).
    apply (MSA_cancel H0 H1).
  - intros.
    specialize (H0 a).
    apply (MSA_comm H0).
  - intros.
    exists (fun a => proj1_sig (MSA_assoc (H0 a) (H1 a))).
    split.
    + intros c.
      apply (proj2_sig (MSA_assoc (H0 c) (H1 c))).
    + intros c.
      apply (proj2_sig (MSA_assoc (H0 c) (H1 c))).
  - intros.
    exists (fun a => proj1_sig (MSA_unit (x a))).
    intros a.
    apply (proj2_sig (MSA_unit (x a))).
  - intros.
    specialize (H0 a0).
    specialize (H1 a0).
    apply (MSA_positive H0 H1).
Defined.

Definition MSA_empty {A} `{MultiUnitSepAlg A} (a: A): Prop :=
  join a a a.

Theorem MSA_unit_empty: ∀ {A} `{MultiUnitSepAlg A} {u a: A},
    join u a a → MSA_empty u.
Proof.
  intros.
  pose proof MSA_unit u as [u' ?].
  pose proof MSA_assoc j H0 as [b [? ?]].
  pose proof MSA_fun H0 H1.
  subst b.
  pose proof MSA_cancel H2 H1.
  subst u'.
  assumption.
Qed.

Theorem MSA_join_empty: ∀ {A} `{MultiUnitSepAlg A} {a b c: A},
    join a b c → MSA_empty a → b = c.
Proof.
  intros.
  unfold MSA_empty in H1.
  pose proof MSA_assoc H1 H0 as [d [? ?]].
  pose proof MSA_comm H0.
  pose proof MSA_comm H3.
  pose proof MSA_cancel H4 H5.
  subst d.
  pose proof MSA_fun H0 H2.
  auto.
Qed.

Theorem MSA_positive': ∀ {A} `{MultiUnitSepAlg A} {a b c: A},
    join a b c → MSA_empty c → a = c ∧ b = c.
Proof.
  intros.
  pose proof MSA_positive H0 H1.
  pose proof MSA_positive (MSA_comm H0) H1.
  pose proof MSA_join_empty H0 H2.
  pose proof MSA_join_empty (MSA_comm H0) H3.
  tauto.
Qed.

Inductive join_opt A: option A → option A → option A → Prop :=
| JOptNone: join_opt A None None None
| JOpt1 a: join_opt A (Some a) None (Some a)
| JOpt2 a: join_opt A None (Some a) (Some a).

#[local] Hint Constructors join_opt.

#[export] Instance option_MSA {A}: MultiUnitSepAlg (option A).
Proof.
  refine {| join := join_opt A; MSA_fun := _; MSA_cancel := _; MSA_comm := _; MSA_assoc := _; MSA_unit := _ |}.
  - intros. invert H; invert H0; reflexivity.
  - intros. invert H; invert H0; reflexivity.
  - intros. invert H; constructor.
  - intros.
    exists (match y with None => z | _ => y end).
    invert H; invert H0; auto.
  - intros. destruct x; eauto.
  - intros. invert H; invert H0; auto.
Defined.

Lemma none_empty_opt: ∀ {A} {v: option A}, v = None ↔ MSA_empty v.
Proof.
  intros.
  split; intros.
  - subst.
    simpl.
    auto.
  - destruct v.
    + simpl in H.
      invert H.
    + reflexivity.
Qed.

Lemma join_opt_some: ∀ {A v1 v2 v3 x},
    join_opt A v1 v2 v3 →
    v1 = Some x →
    v2 = None ∧ v3 = Some x.
Proof.
  intros ? ? ? ? ? C W.
  invert C; auto.
  discriminate.
Qed.

Inductive cell_frag: Type :=
| CFEmp: cell_frag
| CFZ: I → Z → cell_frag (* fractional permission *)
| CFUndef: cell_frag
| CFFun: string → cell_frag.

Inductive join_frag: cell_frag → cell_frag → cell_frag → Prop :=
| JFragEmp: join_frag CFEmp CFEmp CFEmp
| JFragZ1 (q: I) (v: Z): join_frag (CFZ q v) CFEmp (CFZ q v)
| JFragZ2 (q: I) (v: Z): join_frag CFEmp (CFZ q v) (CFZ q v)
| JFragFrct (p q r: I) (v: Z): Iadd p q r → join_frag (CFZ p v) (CFZ q v) (CFZ r v)
| JFragUndef1: join_frag CFUndef CFEmp CFUndef
| JFragUndef2: join_frag CFEmp CFUndef CFUndef
| JFragFun (f: string): join_frag (CFFun f) (CFFun f) (CFFun f).

#[local] Hint Constructors join_frag.

#[export] Instance cell_frag_MSA: MultiUnitSepAlg cell_frag.
Proof.
  refine {| join := join_frag; MSA_fun := _; MSA_cancel := _; MSA_comm := _; MSA_assoc := _; MSA_unit := _ |}.
  - intros. invert H; invert H0; try reflexivity.
    rewrite (Iadd_fun H1 H5).
    reflexivity.
  - intros. invert H; invert H0; try reflexivity.
    + invI p; invI q.
      apply IaddE in H2.
      assert (I_toQ x == 0) by psatz Q.
      pose proof I_toH x.
      exfalso.
      psatz Q.
    + invI p; invI r.
      apply IaddE in H1.
      assert (I_toQ x == 0) by psatz Q.
      pose proof I_toH x.
      exfalso.
      psatz Q.
    + rewrite (Iadd_cancel H1 H3).
      reflexivity.
  - intros. invert H; auto.
    apply (JFragFrct _ _ _ _ (Iadd_comm H0)).
  - intros.
    destruct y.
    + exists z.
      invert H; invert H0; auto.
    + destruct z.
      * exists (CFZ i z0).
        invert H; invert H0; auto.
      * destruct x; destruct a; destruct b; try (exfalso; invert H; invert H0; tauto).
        exists (CFZ i2 z2).
        invert H.
        auto.
        pose (Iadd_opt i i0).
        destruct o eqn: eq.
        exists (CFZ i4 z).
        invert H; invert H0; auto.
        invI i1; invI i; invI i0; invI i2; invI i3; invI i4.
        apply IaddE in H1; apply IaddE in H2.
        pose proof (Iadd_optE x0 x1).
        destruct (Qlt_le_dec 1 (I_toQ x0 + I_toQ x1)).
        unfold o in eq.
        rewrite H in eq.
        discriminate eq.
        unfold o in eq.
        rewrite H in eq.
        remember (liftI x4).
        injection eq as eq.
        subst i.
        apply liftI_inj in eq.
        unfold I_eq in eq; simpl in eq.
        split; apply JFragFrct; apply IaddE; psatz Q.
        exfalso.
        invI i1; invI i; invI i0; invI i2; invI i3.
        pose proof (Iadd_optE x0 x1).
        destruct (Qlt_le_dec 1 (I_toQ x0 + I_toQ x1)).
        invert H; invert H0; auto.
        apply IaddE in H2; apply IaddE in H3.
        pose proof I_toH x; pose proof I_toH x0;
        pose proof I_toH x2; pose proof I_toH x1;
        pose proof I_toH x3.
        psatz Q.
        unfold o in eq.
        rewrite H1 in eq.
        discriminate eq.
      * exfalso.
        invert H; invert H0; auto.
      * exfalso.
        invert H; invert H0; auto.
    + exists CFUndef.
      invert H; invert H0; auto.
    + exists (CFFun s).
      invert H; invert H0; auto.
  - intros. destruct x; eauto.
  - intros. invert H; invert H0; auto.
    invI r.
    apply IaddE in H2.
    exfalso.
    pose proof I_toH x.
    psatz Q.
Defined.

Lemma emp_empty: ∀ {v}, v = CFEmp → MSA_empty v.
Proof. intros. simpl. subst v. auto. Qed.

Lemma fun_empty: ∀ {v f}, v = CFFun f → MSA_empty v.
Proof. intros. simpl. subst v. auto. Qed.

Definition frag_writable (v: cell_frag): Prop :=
  match v with CFUndef => True | CFZ q _ => q = I1 | _ => False end.

Lemma join_writable: ∀ {v1 v2 v3},
    join_frag v1 v2 v3 →
    frag_writable v1 →
    v2 = CFEmp ∧ v1 = v3.
Proof.
  intros ? ? ? C W.
  invert C; simpl in W; try tauto.
  invI p; invI q; invI r.
  apply IaddE in H; simpl in H.
  pose proof I_toH x0; pose proof I_toH x1.
  exfalso; psatz Q.
Qed.

Lemma join_int: ∀ {v1 v2 v3 q n},
    join_frag v1 v2 v3 →
    v1 = CFZ q n →
    ∃ q', v3 = CFZ q' n.
Proof.
  intros ? ? ? ? ? W ?.
  subst v1.
  invert W; eauto.
Qed.

Lemma join_fun: ∀ {x y z f},
    join_frag x y z →
    x = CFFun f →
    y = CFFun f ∧ z = CFFun f.
Proof.
  intros.
  subst x.
  invert H; simpl; auto.
Qed.

Definition assn Σ := Σ → Prop.

Definition derivable {Σ} (P Q: assn Σ) :=
  ∀ σ, P σ → Q σ.

Definition equivalent {Σ} (P Q: assn Σ) :=
  derivable P Q ∧ derivable Q P.

Notation "P ⊢ Q" := (derivable P Q) (at level 50, no associativity).
Notation "P ⟛ Q" := (equivalent P Q) (at level 50, no associativity).

Definition atrue {Σ}: assn Σ := λ _, True.

Definition afalse {Σ}: assn Σ := λ _, False.

Definition aconj {Σ} (P Q: assn Σ): assn Σ :=
  λ σ, P σ ∧ Q σ.

Definition adisj {Σ} (P Q: assn Σ): assn Σ :=
  λ σ, P σ ∨ Q σ.

Definition aimply {Σ} (P Q: assn Σ): assn Σ :=
  λ σ, P σ → Q σ.

Definition asepcon {Σ} `{MultiUnitSepAlg Σ} (P Q: assn Σ): assn Σ :=
  λ σ, ∃ σ₁ σ₂, join σ₁ σ₂ σ ∧ P σ₁ ∧ Q σ₂.

Definition awand {Σ} `{MultiUnitSepAlg Σ} (P Q: assn Σ): assn Σ :=
  λ σ, ∀ σ₁ σ₂, P σ₁ → join σ₁ σ σ₂ → Q σ₂.

Definition aex {Σ} {A: Type} (P: A → assn Σ): assn Σ :=
  λ σ, ∃ a, P a σ.

Definition aall {Σ} {A: Type} (P: A → assn Σ): assn Σ :=
  λ σ, ∀ a, P a σ.

Definition aemp {Σ} `{MultiUnitSepAlg Σ}: assn Σ :=
  λ σ, MSA_empty σ.

Definition aprop {Σ} `{MultiUnitSepAlg Σ} (P: Prop): assn Σ :=
  λ σ, P ∧ MSA_empty σ.

Declare Custom Entry assn.

Notation "⦃ P ⦄" := P (P custom assn at level 100).
Notation "⦅ x ⦆" := x (in custom assn, x constr).
Notation "x" := x (in custom assn at level 0, x constr at level 0).
Notation "f a" := (f a) (in custom assn at level 1, left associativity, only parsing). (* ok? *)
Notation "∃ x .. y , P" := (aex (λ x, .. (aex (λ y, P)) .. )) (in custom assn at level 95, x binder, y binder).
Notation "∀ x .. y , P" := (aall (λ x, .. (aall (λ y, P)) .. )) (in custom assn at level 95, x binder, y binder).
Notation "P ⇒ Q" := (aimply P Q) (in custom assn at level 90, right associativity).
Notation "P ∨ Q" := (adisj P Q) (in custom assn at level 85, right associativity).
Notation "P ∧ Q" := (aconj P Q) (in custom assn at level 80, right associativity).
Notation "P -* Q" := (awand P Q) (in custom assn at level 75, right associativity).
Notation "P * Q" := (asepcon P Q) (in custom assn at level 70, right associativity).
Notation "P * Q" := (asepcon P Q) (in custom assn at level 70, right associativity).
Notation "'emp'" := (aemp) (in custom assn at level 0).
Notation "'True'" := (atrue) (in custom assn at level 0).
Notation "'False'" := (afalse) (in custom assn at level 0).
Notation "⟨ P ⟩" := (aprop P) (in custom assn, P constr).
Notation "( P )" := P (in custom assn, P at level 100).

Theorem derivable_trans: ∀ {Σ} {P Q R: assn Σ},
    P ⊢ Q → Q ⊢ R → P ⊢ R.
Proof.
  unfold derivable.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

Theorem derivable_refl: ∀ {Σ} {P: assn Σ},
    P ⊢ P.
Proof.
  unfold derivable.
  intros.
  assumption.
Qed.

Theorem equivalent_sym: ∀ {Σ} {P Q: assn Σ},
    P ⟛ Q → Q ⟛ P.
Proof.
  intros ???.
  intros [? ?]; unfold equivalent; tauto.
Qed.

Theorem equivalent_refl: ∀ {Σ} {P: assn Σ},
    P ⟛ P.
Proof.
  intros.
  unfold equivalent, derivable; auto.
Qed.

Theorem equivalent_trans: ∀ {Σ} {P Q R: assn Σ},
    P ⟛ Q → Q ⟛ R → P ⟛ R.
Proof.
  intros.
  unfold equivalent in *.
  split; eapply derivable_trans.
  apply H.
  apply H0.
  apply H0.
  apply H.
Qed.

Theorem derivable_wand_l: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q: assn Σ},
    ⦃ P * (P -* Q) ⦄ ⊢ Q.
Proof.
  unfold derivable.
  intros.
  destruct H0 as (?&?&?&?&?).
  eapply H2.
  apply H1.
  apply H0.
Qed.

Theorem equivalent_float_exists_sepcon: ∀ {Σ} `{MultiUnitSepAlg Σ}
                                     {A} {P: assn Σ} {Q: A → assn Σ},
    ⦃ (∃ a, Q a) * P ⦄ ⟛ ⦃ ∃ a, Q a * P ⦄.
Proof.
  unfold equivalent, derivable.
  split; intros.
  - destruct H0 as (?&?&?&(?&?)&?).
    exists x1, x, x0.
    tauto.
  - destruct H0 as (?&?&?&?&?).
    exists x0, x1.
    unfold aex.
    intuition.
    eauto.
Qed.

Theorem sepcon_assoc: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R: assn Σ},
    ⦃ (P * Q) * R ⦄ ⟛ ⦃ P * (Q * R) ⦄.
Proof.
  unfold equivalent, derivable.
  intros ? MSA ? ? ?.
  split; intros.
  - destruct H as [? [? [? [[? [? [? [? ?]]]] ?]]]].
    pose proof MSA_assoc H0 H as [? ?].
    repeat eexists.
    2: { apply H1. }
    3: { apply H2. }
    3: { apply H3. }
    apply (proj2 a).
    tauto.
  - destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]].
    pose proof MSA_comm H.
    pose proof MSA_comm H1.
    pose proof MSA_assoc H5 H4 as [? ?].
    repeat eexists.
    3: { apply H0. }
    3: { apply H2. }
    3: { apply H3. }
    apply MSA_comm.
    apply (proj2 a).
    apply MSA_comm.
    tauto.
Qed.

Theorem sepcon_comm: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q: assn Σ},
    ⦃ P * Q ⦄ ⟛ ⦃ Q * P ⦄.
Proof.
  unfold equivalent, derivable.
  split; intros.
  - destruct H0 as [? [? ?]].
    exists x0, x.
    pose proof (MSA_comm (proj1 H0)).
    tauto.
  - destruct H0 as [? [? ?]].
    exists x0, x.
    pose proof (MSA_comm (proj1 H0)).
    tauto.
Qed.

Theorem emp_sepcon_unit: ∀ {Σ} `{MultiUnitSepAlg Σ} {P: assn Σ},
    P ⟛ ⦃ P * aemp ⦄.
Proof.
  intros ???.
  unfold equivalent, derivable.
  split; intros.
  - unfold asepcon.
    pose proof MSA_unit σ as [??].
    pose proof MSA_unit_empty j.
    exists σ, x.
    apply MSA_comm in j.
    tauto.
  - unfold asepcon in H.
    destruct H0 as (?&?&?&?&?).
    apply MSA_comm in H0.
    pose proof MSA_join_empty H0 H2.
    subst x.
    exact H1.
Qed.

Theorem derivable_exist_l: ∀ {Σ} {A} {P: A → assn Σ} {Q},
    ⦃ ∃ x, P x ⦄ ⊢ Q
  ↔ ∀ x, P x ⊢ Q.
Proof.
  intros ????.
  split; intros H.
  - intros x.
    unfold derivable in H |- *.
    intros ? HP.
    apply H.
    unfold aex.
    exists x.
    apply HP.
  - unfold derivable in H |- *.
    intros ? Hex.
    unfold aex in Hex.
    destruct Hex.
    eapply H.
    eauto.
Qed.

Theorem derivable_exist_r: ∀ {Σ} {A} {P: A → assn Σ} {x},
    ⦃ P x ⦄ ⊢ ⦃ ∃ x, P x ⦄.
Proof.
  intros ????.
  intros ? H.
  unfold aex.
  eauto.
Qed.

Theorem derivable_prop_l: ∀ {Σ} `{MultiUnitSepAlg Σ} {P: assn Σ} {Q p},
    ⦃ P * ⟨p⟩ ⦄ ⊢ Q
  ↔ (p → P ⊢ Q).
Proof.
  intros ? H0 ???.
  split; intros H.
  - intros x.
    unfold derivable in H |- *.
    intros ? HP.
    apply H.
    unfold asepcon.
    pose proof MSA_unit σ as [u X].
    exists σ, u.
    pose proof MSA_unit_empty X.
    apply MSA_comm in X.
    unfold aprop.
    auto.
  - unfold derivable in H |- *.
    intros ? Hp.
    unfold asepcon in Hp.
    destruct Hp as (σ'&u&HJ&HP&Hp).
    unfold aprop in Hp.
    apply MSA_comm in HJ.
    pose proof MSA_join_empty HJ (proj2 Hp).
    subst σ'.
    apply H; tauto.
Qed.

Theorem derivable_disj_l: ∀ {Σ} {P Q R: assn Σ},
    ⦃ P ∨ R ⦄ ⊢ Q
  ↔ P ⊢ Q ∧ R ⊢ Q.
Proof.
  intros ????.
  split; intros.
  - unfold derivable in H |- *.
    unfold adisj in H.
    split; intros; apply H; tauto.
  - unfold derivable in H |- *.
    unfold adisj.
    intros ? [HP|HR].
    + apply (proj1 H).
      exact HP.
    + apply (proj2 H).
      exact HR.
Qed.

Theorem sepcon_mono: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R: assn Σ},
    P ⊢ Q
  → ⦃ P * R ⦄ ⊢ ⦃ Q * R ⦄.
Proof.
  intros.
  intros ? HPR.
  unfold asepcon in HPR |- *.
  destruct HPR as (?&?&?&?&?).
  eexists; eexists; eauto.
Qed.

Theorem sepcon_congr: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R: assn Σ},
    P ⟛ Q
  → ⦃ P * R ⦄ ⟛ ⦃ Q * R ⦄.
Proof.
  intros.
  split;
    apply sepcon_mono;
    apply H0.
Qed.

Theorem disj_mono: ∀ {Σ} {P Q R: assn Σ},
    P ⊢ Q
  → ⦃ P ∨ R ⦄ ⊢ ⦃ Q ∨ R ⦄.
Proof.
  intros.
  intros ? HPR.
  unfold adisj in HPR |- *.
  intuition.
Qed.

Theorem disj_congr: ∀ {Σ} {P Q R: assn Σ},
    P ⟛ Q
  → ⦃ P ∨ R ⦄ ⟛ ⦃ Q ∨ R ⦄.
Proof.
  intros.
  split;
    apply disj_mono;
    apply H.
Qed.

Theorem disj_comm: ∀ {Σ} {P Q: assn Σ},
    ⦃ P ∨ Q ⦄ ⟛ ⦃ Q ∨ P ⦄.
Proof.
  unfold adisj.
  intros.
  split; intros ? H; intuition.
Qed.

Theorem disj_assoc: ∀ {Σ} {P Q R: assn Σ},
    ⦃ P ∨ Q ∨ R ⦄ ⟛ ⦃ (P ∨ Q) ∨ R ⦄.
Proof.
  unfold adisj.
  intros.
  split; intros ? H; intuition.
Qed.

Theorem false_disj_unit: ∀ {Σ} {P: assn Σ},
    ⦃ False ∨ P ⦄ ⟛ ⦃ P ⦄.
Proof.
  unfold adisj, afalse.
  intros.
  split; intros ? H; intuition.
Qed.

Theorem sepcon_disj_distr: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R: assn Σ},
    ⦃ (P ∨ Q) * R ⦄ ⟛ ⦃ P * R ∨ Q * R ⦄.
Proof.
  intros ? H0 ?.
  split; intros ? H.
  - destruct H as (σ₁&σ₂&HJ&HPQ&HR).
    destruct HPQ as [H1|H1];
      [left|right];
      exists σ₁, σ₂;
      tauto.
  - destruct H as [(σ₁&σ₂&HJ&H1&HR)|(σ₁&σ₂&HJ&H1&HR)];
      exists σ₁, σ₂;
      unfold adisj;
      tauto.
Qed.

Theorem false_sepcon_annihilate: ∀ {Σ} `{MultiUnitSepAlg Σ} {P: assn Σ},
    ⦃ False * P ⦄ ⟛ ⦃ False ⦄.
Proof.
  intros ? H0 ?.
  split; intros ? H.
  - destruct H as (?&?&_&F&_).
    destruct F.
  - destruct H.
Qed.

(* Derived Rules. *)

Theorem sepcon_mono_r: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R: assn Σ},
    P ⊢ Q
  → ⦃ R * P ⦄ ⊢ ⦃ R * Q ⦄.
Proof.
  intros.
  eapply derivable_trans.
  apply sepcon_comm.
  eapply derivable_trans.
  eapply sepcon_mono.
  apply H0.
  apply sepcon_comm.
Qed.

Theorem sepcon_mono_2: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R S: assn Σ},
    P ⊢ Q → R ⊢ S
  → ⦃ P * R ⦄ ⊢ ⦃ Q * S ⦄.
Proof.
  intros.
  eapply derivable_trans.
  eapply sepcon_mono.
  apply H0.
  eapply sepcon_mono_r.
  apply H1.
Qed.

Theorem sepcon_congr_r: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R: assn Σ},
    P ⟛ Q
  → ⦃ R * P ⦄ ⟛ ⦃ R * Q ⦄.
Proof.
  intros.
  eapply equivalent_trans.
  apply sepcon_comm.
  eapply equivalent_trans.
  eapply sepcon_congr.
  apply H0.
  apply sepcon_comm.
Qed.

Theorem sepcon_congr_2: ∀ {Σ} `{MultiUnitSepAlg Σ} {P Q R S: assn Σ},
    P ⟛ Q → R ⟛ S
  → ⦃ P * R ⦄ ⟛ ⦃ Q * S ⦄.
Proof.
  intros.
  eapply equivalent_trans.
  eapply sepcon_congr.
  apply H0.
  eapply sepcon_congr_r.
  apply H1.
Qed.

(* Derived Rules End. *)

Require Import Ring Ring_theory.
Require Import Setoid.

Add Parametric Relation Σ (MSA: MultiUnitSepAlg Σ): (assn Σ) (@equivalent Σ)
  reflexivity proved by (@equivalent_refl Σ)
  symmetry proved by (@equivalent_sym Σ)
  transitivity proved by (@equivalent_trans Σ) as Setoid_assn.

Add Parametric Morphism Σ (MSA: MultiUnitSepAlg Σ): (@asepcon Σ MSA) with
  signature equivalent ==> equivalent ==> equivalent as sepcon_mor.
Proof.
  intros.
  eapply equivalent_trans.
  - eapply sepcon_congr.
    apply H.
  - eapply equivalent_trans.
    apply sepcon_comm.
    eapply equivalent_trans.
    2: { apply sepcon_comm. }
    apply sepcon_congr.
    apply H0.
Qed.

Add Parametric Morphism Σ (MSA: MultiUnitSepAlg Σ): (@adisj Σ) with
  signature equivalent ==> equivalent ==> equivalent as adisj_mor.
Proof.
  intros.
  eapply equivalent_trans.
  - eapply disj_congr.
    apply H.
  - eapply equivalent_trans.
    apply disj_comm.
    eapply equivalent_trans.
    2: { apply disj_comm. }
    apply disj_congr.
    apply H0.
Qed.

Definition assn_ring_theory: ∀ Σ `{MSA: MultiUnitSepAlg Σ},
    semi_ring_theory afalse aemp adisj asepcon equivalent.
Proof.
  intros ? H0.
  split; intros.
  - exact false_disj_unit.
  - exact disj_comm.
  - exact disj_assoc.
  - apply equivalent_sym.
    eapply equivalent_trans.
    apply emp_sepcon_unit.
    apply sepcon_comm.
  - exact false_sepcon_annihilate.
  - exact sepcon_comm.
  - apply equivalent_sym.
    exact sepcon_assoc.
  - exact sepcon_disj_distr.
Qed.

Ltac deriv_step X := (eapply derivable_trans; [eapply X|]).
Ltac equiv_step X := (eapply equivalent_trans; [eapply X|]).
Ltac deriv_step_ring X := (refine (@derivable_trans _ _ X _ _ _);
                           [ring|]).
Ltac equiv_step_ring X := (refine (@equivalent_trans _ _ X _ _ _);
                           [ring|]).
