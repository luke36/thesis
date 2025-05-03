Require Import Unicode.Utf8_core.
Require Import Strings.String.
Require Import Lists.List. Import ListNotations.
Require Import ZArith.ZArith.
Require Import QArith.QArith.
Require Import FunctionalExtensionality.

Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import FP.SetsFixedpoints.

Require Import thesis.interval.
Require Import thesis.lang.
Require Import thesis.semantics.
Require Import thesis.sepalg.

Local Open Scope Z.
Local Open Scope sets.
Local Open Scope list.

(* Heap Fragments (rather than authoritative/physical heap). *)

Definition fic_heap := Z → cell_frag.
#[export] Instance fic_heap_MSA: MultiUnitSepAlg fic_heap := index_prod_MSA cell_frag_MSA.
Check assn_ring_theory.
Add Ring Ring_assn_fic_heap: (assn_ring_theory fic_heap) (abstract).

Definition fic_stack := Z → option Z.
#[export] Instance fic_stack_MSA: MultiUnitSepAlg fic_stack := index_prod_MSA option_MSA.

Definition fic_reg := reg → option Z.
#[export] Instance fic_reg_MSA: MultiUnitSepAlg fic_reg := index_prod_MSA option_MSA.

Definition fic_LΣ: Type := fic_reg * fic_stack * fic_heap.
#[export] Instance fic_LΣ_MSA: MultiUnitSepAlg fic_LΣ := prod_MSA (prod_MSA fic_reg_MSA fic_stack_MSA) fic_heap_MSA.
Add Ring Ring_assn_fic_LΣ: (assn_ring_theory fic_LΣ) (abstract).

Definition lift_heap (σ: heap): fic_heap :=
  λ a, match σ a with
       | CEmp => CFEmp
       | CZ n => CFZ I1 n
       | CUndef => CFUndef
       | CFun f => CFFun f
       end.

Definition lift_LΣ (σ: LΣ): fic_LΣ :=
  (λ r, Some (rg σ r), λ l, Some (st σ l), lift_heap (hp σ)).

Lemma lift_heap_eq: ∀ {σ σ' a},
    σ a = σ' a ↔ (lift_heap σ) a = (lift_heap σ') a.
Proof.
  intros.
  unfold lift_heap.
  split; intros;
    destruct (σ a); destruct (σ' a);
    try discriminate; try reflexivity;
    injection H as H;
    rewrite H; reflexivity.
Qed.

Lemma lift_heap_fun: ∀ {σ a f},
    σ a = CFun f ↔ (lift_heap σ) a = CFFun f.
Proof.
  intros.
  unfold lift_heap.
  split; intros;
    destruct (σ a); try discriminate; try reflexivity;
    injection H as H;
    rewrite H; reflexivity.
Qed.

Lemma lift_heap_int: ∀ {σ a q n},
    σ a = CZ n ∧ q = I1 ↔ (lift_heap σ) a = CFZ q n.
Proof.
  intros.
  unfold lift_heap.
  split; [intros [H ?]|intros H];
    destruct (σ a); try discriminate; try reflexivity;
    injection H as H;
    subst; tauto.
Qed.

Lemma lift_heap_undef: ∀ {σ a},
    σ a = CUndef ↔ (lift_heap σ) a = CFUndef.
Proof.
  intros.
  unfold lift_heap.
  split; intros;
    destruct (σ a); try discriminate; try reflexivity;
    injection H as H;
    subst; tauto.
Qed.

Lemma lift_heap_emp: ∀ {σ a},
    σ a = CEmp ↔ (lift_heap σ) a = CFEmp.
Proof.
  intros.
  unfold lift_heap.
  split; intros;
    destruct (σ a); try discriminate; try reflexivity;
    injection H as H;
    subst; tauto.
Qed.

Lemma lift_heap_writable: ∀ {σ a},
    writable (σ a) ↔ frag_writable ((lift_heap σ) a).
Proof.
  intros.
  unfold lift_heap.
  split; intros;
    destruct (σ a); simpl in H; try discriminate; try reflexivity; try tauto.
Qed.

(* Heap Fragments End. *)

Inductive Assn: Type → Type :=
| ALift Σ (P: assn Σ): Assn Σ
| AFunSpec Σ (f: string) (H: fun_spec): Assn Σ
| AMachSpec Σ (H: mach_spec): Assn Σ
| AConj Σ (P Q: Assn Σ): Assn Σ
| ADisj Σ (P Q: Assn Σ): Assn Σ
| AImply Σ (P Q: Assn Σ): Assn Σ
| ASepCon Σ (P Q: Assn Σ): Assn Σ
| AWand Σ (P Q: Assn Σ): Assn Σ
| AEx Σ (A: Type) (Px: A → Assn Σ): Assn Σ
| AAll Σ (A: Type) (Px: A → Assn Σ): Assn Σ
with fun_spec :=
  FunSpec (Pa: list Z → Assn fic_heap) (Qa: list Z → Z → Assn fic_heap)
with mach_spec :=
  MachSpec (Pa: Assn fic_LΣ) (Qa: Assn fic_LΣ).

Arguments ALift {Σ}.
Arguments AFunSpec {Σ}.
Arguments AMachSpec {Σ}.
Arguments AConj {Σ}.
Arguments ADisj {Σ}.
Arguments AImply {Σ}.
Arguments ASepCon {Σ}.
Arguments AWand {Σ}.
Arguments AEx {Σ} {A}.
Arguments AAll {Σ} {A}.

Declare Custom Entry Assn.

Notation "∃ x .. y , P" := (AEx (λ x, .. (AEx (λ y, P)) .. )) (in custom Assn at level 95, x binder, y binder).
Notation "∀ x .. y , P" := (AAll (λ x, .. (AAll (λ y, P)) .. )) (in custom Assn at level 95, x binder, y binder).
Notation "P ⇒ Q" := (AImply P Q) (in custom Assn at level 90, right associativity).
Notation "P ∨ Q" := (ADisj P Q) (in custom Assn at level 85, right associativity).
Notation "P ∧ Q" := (AConj P Q) (in custom Assn at level 80, right associativity).
Notation "P -* Q" := (AWand P Q) (in custom Assn at level 75, right associativity).
Notation "P * Q" := (ASepCon P Q) (in custom Assn at level 70, right associativity).
Notation "⌈ P ⌉" := (ALift P) (in custom Assn, P custom assn).
Notation "( P )" := P (in custom Assn, P at level 100).
Notation "x" := x (in custom Assn at level 0, x constr at level 0).
Notation "f a" := (f a) (in custom Assn at level 1). (* ok? *)
(* Notation "⦅ x ⦆" := x (in custom Assn, x constr). *)

Definition prog_spec: Type := (string → fun_spec → Prop) * (mach_spec → Prop).

Definition lift_Σ Σ: Type := prog_spec * Σ.

Definition ΣC: Type := lift_Σ fic_heap.
Definition ΣA: Type := lift_Σ fic_LΣ.

#[export] Instance ΣC_MSA: MultiUnitSepAlg ΣC := prod_MSA discrete_MSA fic_heap_MSA.
#[export] Instance ΣA_MSA: MultiUnitSepAlg ΣA := prod_MSA discrete_MSA fic_LΣ_MSA.
Add Ring Ring_assn_ΣC: (assn_ring_theory ΣC) (abstract).
Add Ring Ring_assn_ΣA: (assn_ring_theory ΣA) (abstract).

Notation "'spec'" := fst (only parsing).
Notation "'low'" := snd (only parsing).

Definition lift_assn {Σ} (P: assn Σ): assn (lift_Σ Σ) :=
  λ σ, P (low σ).

Notation "[ P ]" := (lift_assn P) (in custom assn, P at level 100).

Definition afun_spec {Σ} (f: string) (H: fun_spec): assn (lift_Σ Σ) :=
  λ σ, (f, H) ∈ fst (spec σ).

Definition amach_spec {Σ} (H: mach_spec): assn (lift_Σ Σ) :=
  λ σ, H ∈ snd (spec σ).

Definition eval_assn {Σ} `{MultiUnitSepAlg Σ}
  (P: Assn Σ): assn (lift_Σ Σ).
Proof.
  induction P.
  - exact (lift_assn P).
  - exact (afun_spec f H).
  - exact (amach_spec H).
  - exact (aconj (IHP1 H0) (IHP2 H0)).
  - exact (adisj (IHP1 H0) (IHP2 H0)).
  - exact (aimply (IHP1 H0) (IHP2 H0)).
  - exact (asepcon (IHP1 H0) (IHP2 H0)).
  - exact (awand (IHP1 H0) (IHP2 H0)).
  - exact (aex (λ a, X a H0)).
  - exact (aall (λ a, X a H0)).
Defined.

Notation "⟦ P ⟧" := (eval_assn P).

Definition hoare_prog_fun (Δ: prog_spec) (χ_ok: sem_ok) (χ_er: sem_er) :=
  ∀ f Φ Ψ vs h g σ,
    (f, FunSpec Φ Ψ) ∈ fst Δ
  → (eval_assn (Φ vs) (Δ, h)) → join h g (lift_heap σ)
  → ¬ (inl (f, vs, σ)) ∈ χ_er
  ∧ ∀ n σ',
      (inl (f, vs, σ), inl (n, σ')) ∈ χ_ok
    → ∃ h', (eval_assn (Ψ vs n) (Δ, h')) ∧ join h' g (lift_heap σ').

Definition hoare_prog_mach (Δ: prog_spec) (χ_ok: sem_ok) (χ_er: sem_er) :=
  ∀ Φ Ψ h g σ,
    MachSpec Φ Ψ ∈ snd Δ
  → (eval_assn Φ) (Δ, h) → join h g (lift_LΣ σ)
  → ¬ inr σ ∈ χ_er
  ∧ ∀ σ', (inr σ, inr σ') ∈ χ_ok
        → ∃ h', (eval_assn Ψ) (Δ, h') ∧ join h' g (lift_LΣ σ').

Definition hoare_prog (Δ: prog_spec) (χ_ok: sem_ok) (χ_er: sem_er) :=
  hoare_prog_fun Δ χ_ok χ_er ∧ hoare_prog_mach Δ χ_ok χ_er.

Definition spec_include (Δ Γ: prog_spec) :=
  fst Δ ⊆ fst Γ ∧ snd Δ ⊆ snd Γ.

Record ProofContext (Δ: prog_spec) := mkProofContext {
  ctx_χ_ok: sem_ok;
  ctx_χ_er: sem_er;
  ctx_Δ': prog_spec;
  ctx_Hsub: spec_include Δ ctx_Δ';
  ctx_HΔ: hoare_prog ctx_Δ' ctx_χ_ok ctx_χ_er;
                                        }.
(* Predicates. *)

Definition empty_but (l: Z): assn fic_heap := λ σ, ∀ l', l ≠ l' → MSA_empty (σ l').

Definition astore_int_q l q v: assn fic_heap :=
  λ σ, σ l = CFZ q v ∧ empty_but l σ.
Definition astore_int l v := astore_int_q l I1 v.

Notation "a ↦ [ q ] v" := (astore_int_q a q v) (in custom assn at level 50, q constr).
Notation "a ↦ v" := (astore_int a v) (in custom assn at level 50).

Definition astore_uninit (l: Z): assn fic_heap :=
  λ σ, frag_writable (σ l) ∧ empty_but l σ.

Notation "a ↦ -" := (astore_uninit a) (in custom assn at level 50).

Definition astore_fun (l: Z) (H: fun_spec): assn ΣC :=
  λ σ, ∃ f, low σ l = CFFun f ∧ (f, H) ∈ fst (spec σ) ∧ MSA_empty σ.

Notation "'𝔉' {{{ Φ }}} a {{{ Ψ }}}" := (astore_fun a (FunSpec Φ Ψ)) (in custom assn at level 50, Φ custom Assn, Ψ custom Assn, a constr).

(* we default to lists while you can use more efficient representations. *)
Definition code := list (Z * ins).

Fixpoint astore_array_q a q l: assn fic_heap :=
  match l with
  | [] => aemp
  | n :: l' => ⦃ astore_int_q a q n * astore_array_q ⦅a + 1⦆ q l' ⦄
  end.

Definition astore_array a l := astore_array_q a I1 l.

Definition astore_uninit_array a n: assn fic_heap :=
  λ σ, n >= 0
     ∧ (∀ l, a <= l < a + n → frag_writable (σ l))
     ∧ (∀ l, (l < a ∨ l >= a + n) → MSA_empty (σ l)).

Notation "a ↦.. [ q ] l" := (astore_array_q a q l) (in custom assn at level 50, q constr).
Notation "a ↦.. l" := (astore_array a l) (in custom assn at level 50).
Notation "a ↦.. n ×- " := (astore_uninit_array a n) (in custom assn at level 50, n constr).

Definition astore_ins_q a q i: assn fic_heap :=
  astore_array_q a q (encode i).

Fixpoint astore_code_q q (c: code): assn fic_heap :=
  match c with
  | [] => aemp
  | (a, i) :: c' => ⦃ astore_ins_q a q i * astore_code_q q c' ⦄
  end.

Definition astore_code c := astore_code_q I1 c.

Notation "'↦c' [ q ] c" := (astore_code_q q c) (in custom assn at level 50, q constr).
Notation "'↦c' c" := (astore_code c) (in custom assn at level 50).

Definition lift_assn_heap_LΣ (P: assn fic_heap): assn fic_LΣ :=
  λ σ, MSA_empty (rg σ) ∧ MSA_empty (st σ) ∧ P (hp σ).

Notation "⌈ P ⌉" := (lift_assn_heap_LΣ P) (in custom assn, P at level 100).

Definition lift_assn_ΣC_ΣA (P: assn ΣC): assn ΣA :=
  λ σ, MSA_empty (rg (low σ)) ∧ MSA_empty (st (low σ)) ∧ P (spec σ, hp (low σ)).

Notation "⇑ P" := (lift_assn_ΣC_ΣA P) (in custom assn at level 50).

Definition lower_assn_ΣA_ΣC (P: assn ΣA): assn ΣC :=
  λ σ, (∀ τ, P τ → MSA_empty (rg τ) ∧ MSA_empty (st τ))
     ∧ P (spec σ, (λ _, None, λ _, None, low σ)).

Notation "⇓ P" := (lower_assn_ΣA_ΣC P) (in custom assn at level 50).

Definition areg_int (r: reg) (n: Z): assn fic_LΣ :=
  λ σ, rg σ r = Some n ∧ (∀ r', r ≠ r' → rg σ r' = None)
       ∧ MSA_empty (st σ) ∧ MSA_empty (hp σ).

Definition areg_any r := ⦃ ∃ n, areg_int r n ⦄.

Definition astack_int (a n: Z): assn fic_LΣ :=
  λ σ, st σ a = Some n ∧ (∀ a', a ≠ a' → st σ a' = None)
       ∧ MSA_empty (rg σ) ∧ MSA_empty (hp σ).

Definition astack_any a := ⦃ ∃ n, astack_int a n ⦄.

Fixpoint astack_array a l: assn fic_LΣ :=
  match l with
  | [] => aemp
  | v :: l' => ⦃ astack_int a v * astack_array ⦅a + 1⦆ l' ⦄
  end.

Notation "a r↦ v" := (areg_int a v) (in custom assn at level 50).
Notation "a r↦ -" := (areg_any a) (in custom assn at level 50).
Notation "a s↦ v" := (astack_int a v) (in custom assn at level 50).
Notation "a s↦ -" := (astack_any a) (in custom assn at level 50).
Notation "a s↦.. l" := (astack_array a l) (in custom assn at level 50).

Definition amach_spec_mach {Σ} (H: mach_spec): assn (lift_Σ Σ) :=
  λ σ, H ∈ snd (spec σ) ∧ MSA_empty (low σ).

Notation "'𝔐' {{{ Φ }}} {{{ Ψ }}}" := (amach_spec_mach (MachSpec Φ Ψ)) (in custom assn at level 50, Φ custom Assn, Ψ custom Assn).

Definition caller_any := ⦃ R0 r↦ - * R1 r↦ - * R2 r↦ - ⦄.

Definition caller_r0 n := ⦃ R0 r↦ n * R1 r↦ - * R2 r↦ - ⦄.

Definition stack_up_any a: assn fic_LΣ :=
  λ σ, (∀ l, l < a → MSA_empty (st σ l))
     ∧ (∀ l, l >= a → ∃ n, st σ l = Some n)
     ∧ MSA_empty (rg σ) ∧ MSA_empty (hp σ).

Definition prologue l vs :=
  ⦃ caller_any * SP r↦ l * l s↦.. vs * stack_up_any ⦅l + Z.of_nat (length vs)⦆ ⦄.

Definition epilogue l n :=
  ⦃ caller_r0 n * SP r↦ l * stack_up_any l ⦄.

(* Predicates End.*)

(* Predicates derivations. *)

Lemma store_int_q_split: ∀ {a p q r n},
    Iadd p q r
  → ⦃ a ↦[p] n * a ↦[q] n ⦄ ⟛ ⦃ a ↦[r] n ⦄.
Proof.
  intros ????? Hpqr.
  split; intros ? H.
  - destruct H as (σ₁&σ₂&HJσ&Hp&Hq).
    unfold astore_int_q in *.
    split.
    + specialize (HJσ a).
      rewrite (proj1 Hp), (proj1 Hq) in HJσ.
      invert HJσ.
      rewrite (Iadd_fun Hpqr H0).
      reflexivity.
    + intros l ne.
      pose proof proj2 Hp _ ne.
      pose proof proj2 Hq _ ne.
      specialize (HJσ l).
      rewrite<- (MSA_join_empty HJσ H).
      assumption.
  - pose proof MSA_unit σ as [u X].
    exists (λ l, if a =? l then CFZ p n else u l),
           (λ l, if a =? l then CFZ q n else u l).
    unfold astore_int_q in H.
    split.
    + intros l.
      destruct (Z.eq_dec a l).
      * subst l.
        rewrite! Z.eqb_refl.
        rewrite (proj1 H).
        apply (JFragFrct _ _ _ _ Hpqr).
      * rewrite (proj2 (Z.eqb_neq _ _) n0).
        pose proof (proj2 H _ n0).
        apply MSA_comm in X.
        pose proof MSA_join_empty (X _) H0.
        rewrite H1.
        apply H0.
    + unfold astore_int_q.
      rewrite! Z.eqb_refl.
      pose proof MSA_unit_empty X.
      intuition;
        intros l ne;
        rewrite (proj2 (Z.eqb_neq _ _) ne);
        apply H0.
Qed.

Lemma store_array_q_split: ∀ {a p q r l},
    Iadd p q r
  → ⦃ a ↦..[p] l * a ↦..[q] l ⦄ ⟛ ⦃ a ↦..[r] l ⦄.
Proof.
  intros.
  generalize dependent a.
  induction l.
  - intros a.
    simpl.
    ring.
  - rename a into v.
    intros a.
    simpl.
    equiv_step_ring ⦃ (a ↦ [p] v * a ↦ [q] v) * (⦅a + 1⦆ ↦.. [p] l * ⦅a + 1⦆ ↦.. [q] l) ⦄.
    apply sepcon_congr_2.
    apply (store_int_q_split H).
    apply IHl.
Qed.

Lemma store_code_q_split: ∀ {p q r c},
    Iadd p q r
  → ⦃ ↦c[p] c * ↦c[q] c ⦄ ⟛ ⦃ ↦c[r] c ⦄.
Proof.
  intros.
  induction c.
  - simpl.
    ring.
  - destruct a as [a i].
    simpl.
    equiv_step_ring ⦃ (astore_ins_q a p i * astore_ins_q a q i)
                    * (↦c [p] c * ↦c [q] c) ⦄.
    apply sepcon_congr_2.
    apply (store_array_q_split H).
    apply IHc.
Qed.

Lemma lift_assn_mono: ∀ {Σ} {P Q: assn Σ},
    P ⊢ Q → ⦃ [P] ⦄ ⊢ ⦃ [Q] ⦄.
Proof.
  intros ???.
  intros H.
  intros ? HP.
  unfold lift_assn in HP |- *.
  apply H.
  apply HP.
Qed.

Lemma lift_assn_heap_LΣ_mono: ∀ {P Q},
    P ⊢ Q → ⦃ ⌈P⌉ ⦄ ⊢ ⦃ ⌈Q⌉ ⦄.
Proof.
  intros ??.
  intros H.
  intros ? HP.
  unfold lift_assn_heap_LΣ in HP |- *.
  pose proof (H (snd σ)).
  tauto.
Qed.

Lemma lift_assn_sepcon_congr: ∀ {P Q},
    ⦃ [P] * [Q] ⦄ ⟛ ⦃ [P * Q] ⦄.
Proof.
  intros ??.
  split; intros ? H.
  - unfold asepcon, lift_assn in H |- *.
    destruct H as ((?&h1)&(?&h2)&(?&HJ)&HP&HQ).
    simpl snd in *.
    eauto.
  - unfold asepcon, lift_assn in H |- *.
    destruct H as (h1&h2&HJ&HP&HQ).
    simpl snd in *.
    exists (fst σ, h1), (fst σ, h2).
    simpl snd.
    intuition.
    split; [simpl;tauto|apply HJ].
Qed.

Lemma lift_assn_heap_LΣ_sepcon_congr: ∀ {P Q},
    ⦃ ⌈P⌉ * ⌈Q⌉ ⦄ ⟛ ⦃ ⌈P * Q⌉ ⦄.
Proof.
  intros ??.
  split; intros ? H.
  - unfold asepcon, lift_assn_heap_LΣ in H |- *.
    destruct H as (((?&?)&h1)&((?&?)&h2)&(?&HJ)&HP&HQ).
    pose proof (proj1 H).
    pose proof (proj2 H).
    simpl snd in *.
    simpl fst in *.
    pose proof MSA_join_empty H0 (proj1 HP); subst f1.
    pose proof MSA_join_empty H1 (proj1 (proj2 HP)); subst f2.
    intuition eauto.
  - unfold asepcon, lift_assn_heap_LΣ in H |- *.
    destruct H as (Hem1&Hem2&h1&h2&HJ&HP&HQ).
    pose proof MSA_unit (rg σ) as [u1 X1].
    pose proof MSA_unit (st σ) as [u2 X2].
    pose proof MSA_unit_empty X1.
    pose proof MSA_unit_empty X2.
    exists (u1, u2, h1), (u1, u2, h2).
    simpl fst.
    simpl snd.
    intuition.
    split; [|apply HJ].
    split; simpl fst; simpl snd.
    + pose proof MSA_join_empty (MSA_comm X1) Hem1.
      subst u1; auto.
    + pose proof MSA_join_empty (MSA_comm X2) Hem2.
      subst u2; auto.
Qed.

(* Predicates derivations end. *)

Lemma destruct_sepcon_liftΣ: ∀ {Σ} {MSA: MultiUnitSepAlg Σ}
                               {P Q: assn (lift_Σ Σ)} {Δ σ},
    @asepcon (prog_spec * Σ) (prod_MSA discrete_MSA MSA) P Q (Δ, σ)
  → ∃ σ₁ σ₂, P (Δ, σ₁) ∧ Q (Δ, σ₂) ∧ join σ₁ σ₂ σ.
Proof.
  intros ? H0 ???? H.
  destruct H as ((?&σ₁)&(?&σ₂)&HJ&HP&HQ).
  destruct HJ.
  simpl in H, H1.
  destruct H.
  subst p p0.
  exists σ₁, σ₂.
  tauto.
Qed.

