Require Import Unicode.Utf8_core.
Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import ZArith.ZArith.

Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import FP.SetsFixedpoints.

Require Import thesis.interval.
Require Import thesis.lang.
Require Import thesis.semantics.
Require Import thesis.sepalg.

Local Open Scope Z.
Local Open Scope sets.
Local Open Scope list.

Set Default Proof Using "Type".

(* Heap Fragments (rather than authoritative/physical heap). *)

Definition fic_heap := Z → cell_frag.
#[export] Instance fic_heap_MSA: MultiUnitSepAlg fic_heap := index_prod_MSA cell_frag_MSA.

Definition fic_stack := Z → option Z.
#[export] Instance fic_stack_MSA: MultiUnitSepAlg fic_stack := index_prod_MSA option_MSA.

Definition fic_reg := reg → option Z.
#[export] Instance fic_reg_MSA: MultiUnitSepAlg fic_reg := index_prod_MSA option_MSA.

Definition fic_LΣ: Type := fic_reg * fic_stack * fic_heap.
#[export] Instance fic_LΣ_MSA: MultiUnitSepAlg fic_LΣ := prod_MSA (prod_MSA fic_reg_MSA fic_stack_MSA) fic_heap_MSA.

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

Definition prog_spec: Type := (string → fun_spec → Prop) * (mach_spec → Prop).

Definition lift_Σ Σ: Type := prog_spec * Σ.

Definition ΣC: Type := lift_Σ fic_heap.
Definition ΣA: Type := lift_Σ fic_LΣ.

#[export] Instance ΣC_MSA: MultiUnitSepAlg ΣC := prod_MSA discrete_MSA fic_heap_MSA.
#[export] Instance ΣA_MSA: MultiUnitSepAlg ΣA := prod_MSA discrete_MSA fic_LΣ_MSA.

Notation "'spec'" := fst (only parsing).
Notation "'low'" := snd (only parsing).

Definition lift_assn {Σ} (P: assn Σ): assn (lift_Σ Σ) :=
  λ σ, P (low σ).

Notation "'↑'" := lift_assn.

Definition afun_spec {Σ} (f: string) (H: fun_spec): assn (lift_Σ Σ) :=
  λ σ, (f, H) ∈ fst (spec σ).

Definition amach_spec {Σ} (H: mach_spec): assn (lift_Σ Σ) :=
  λ σ, H ∈ snd (spec σ).

Definition eval_assn {Σ} `{MultiUnitSepAlg Σ}
  (P: Assn Σ): assn (lift_Σ Σ).
Proof.
  induction P.
  - exact (↑P).
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

Section hoare_expr.

  Definition empty_but (l: Z): assn fic_heap := λ σ, ∀ l', l ≠ l' → MSA_empty (σ l').

  Definition astore_int_q l q v: assn fic_heap :=
    λ σ, σ l = CFZ q v ∧ empty_but l σ.

  Definition astore_uninit (l: Z): assn fic_heap :=
    λ σ, frag_writable (σ l) ∧ empty_but l σ.

  Definition astore_fun (l: Z) (H: fun_spec): assn ΣC :=
    λ σ, ∃ f, low σ l = CFFun f ∧ (f, H) ∈ fst (spec σ) ∧ MSA_empty σ.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.
  Variable Δ: prog_spec.

  Definition spec_include (Δ Γ: prog_spec) :=
    fst Δ ⊆ fst Γ ∧ snd Δ ⊆ snd Γ.

  Definition hoare (P: assn ΣC) (e: expr Z expr_sem) (Q: Z → assn ΣC) :=
    ∀ Δ' h g σ,
      spec_include Δ Δ' → hoare_prog Δ' χ_ok χ_er
    → P (Δ', h) → join h g (lift_heap σ)
    → (¬ σ ∈ er (eval_expr' χ_ok χ_er e))
    ∧ ∀ n σ',
        (σ, n, σ') ∈ ok (eval_expr' χ_ok χ_er e)
      → ∃ h', Q n (Δ', h') ∧ join h' g (lift_heap σ').

  Theorem hoare_bind: ∀ {P Q R e₁ e₂},
      hoare P e₁ Q
    → (∀ v, hoare (Q v) (e₂ v) R)
    → hoare P (EBind e₁ e₂) R.
  Proof.
    intros ????? H1 H2.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - simpl; sets_unfold.
      specialize (H1 _ _ _ _ Hsub HΔ HP HJ) as (H1e&H1n).
      intros [H|(n&σ'&Hn1&He2)].
      + apply H1e.
        exact H.
      + specialize (H1n _ _ Hn1) as (?&HQ&HJ').
        unfold hoare in H2.
        specialize (H2 _ _ _ _ _ Hsub HΔ HQ HJ').
        apply H2.
        exact He2.
    - simpl; sets_unfold.
      intros ?? (m&σ'&Hn1&Hn2).
      unfold hoare in H1.
      specialize (H1 _ _ _ _ Hsub HΔ HP HJ) as (_&H1n).
      specialize (H1n _ _ Hn1) as (?&HQ&HJ').
      unfold hoare in H2.
      specialize (H2 _ _ _ _ _ Hsub HΔ HQ HJ') as (?&H2n).
      apply H2n.
      exact Hn2.
  Qed.

  Definition hoare_ok (P: assn ΣC) (e: expr Z expr_sem) (Q: Z → assn ΣC) :=
    ∀ Δ' h g σ,
      spec_include Δ Δ' → hoare_prog Δ' χ_ok χ_er
    → P (Δ', h) → join h g (lift_heap σ)
    → ∀ n σ',
        (σ, n, σ') ∈ ok (eval_expr' χ_ok χ_er e)
      → ∃ h', Q n (Δ', h') ∧ join h' g (lift_heap σ').

  Theorem hoare_fix_ok: ∀ {I Q e},
      (∀ x, hoare I (EFixVar x) Q → hoare I (e x) Q)
    → hoare_ok I (EFix e) Q.
  Proof.
    intros ??? H.
    unfold hoare.
    simpl.
    intros ???? Hsub HΔ HI HJ.
    simpl; unfold Lfix.
    intros ?? [i Hn].
    generalize dependent Hn.
    generalize dependent HJ.
    generalize dependent HI.
    generalize dependent HΔ.
    generalize dependent Hsub.
    generalize dependent σ'.
    generalize dependent n.
    generalize dependent σ.
    generalize dependent g.
    generalize dependent h.
    generalize dependent Δ'.
    induction i.
    + simpl.
      intros.
      tauto.
    + simpl.
      intros ???????? HI HJ Hn.
      unfold hoare in H.
      eapply H; simpl; eauto.
      2: { apply Hn. }
      intros.
      split; [tauto|].
      intros.
      eapply IHi; simpl; eauto.
  Qed.

  Theorem hoare_fix: ∀ {I Q e},
      (∀ x, hoare I (EFixVar x) Q → hoare I (e x) Q)
    → hoare I (EFix e) Q.
  Proof.
    intros ??? H.
    unfold hoare.
    simpl.
    intros ???? Hsub HΔ HI HJ.
    split.
    - simpl; unfold Lfix.
      intros [i Hn].
      generalize dependent Hn.
      generalize dependent HJ.
      generalize dependent HI.
      generalize dependent HΔ.
      generalize dependent Hsub.
      generalize dependent σ.
      generalize dependent g.
      generalize dependent h.
      generalize dependent Δ'.
      induction i.
      + simpl.
        tauto.
      + simpl.
        intros ???? Hsub HΔ HI HJ Hn.
        unfold hoare in H.
        eapply H; simpl; eauto.
        2: { apply Hn. }
        simpl.
        clear Δ' h g σ Hsub HΔ HI HJ Hn.
        intros ???? Hsub HΔ HI HJ.
        pose proof hoare_fix_ok H.
        split.
        * eauto.
        * eapply H0; eauto.
    - eapply hoare_fix_ok; eauto.
  Qed.

  Theorem hoare_var: ∀ {x},
      hoare aemp (EVar x) (λ m, aprop (x = m)).
  Proof.
    intros.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - simpl.
      tauto.
    - intros ?? Hn.
      simpl in Hn; sets_unfold in Hn.
      unfold pure in Hn.
      destruct Hn as (Hn1&Hn2).
      subst σ'.
      exists h.
      split.
      + pose proof MSA_unit (Δ', h) as [u' X'].
        unfold aprop.
        pose proof MSA_unit_empty X'.
        apply MSA_comm in X'.
        tauto.
      + exact HJ.
  Qed.

  Theorem hoare_val: ∀ {n},
      hoare aemp (EVal n) (λ m, aprop (n = m)).
  Proof.
    intros.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - simpl.
      tauto.
    - intros ?? Hn.
      simpl in Hn; sets_unfold in Hn.
      unfold pure in Hn.
      destruct Hn as (Hn1&Hn2).
      subst σ'.
      exists h.
      split.
      + pose proof MSA_unit (Δ', h) as [u' X'].
        unfold aprop.
        pose proof MSA_unit_empty X'.
        apply MSA_comm in X'.
        tauto.
      + exact HJ.
  Qed.

  Theorem hoare_arith: ∀ {op e₁ e₂},
      hoare aemp (EArith op e₁ e₂) (λ n, aprop (n = (eval_arith_op op) e₁ e₂)).
  Proof.
    intros.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - simpl.
      tauto.
    - intros ?? Hn.
      simpl in Hn; sets_unfold in Hn.
      unfold pure in Hn.
      destruct Hn as (Hn1&Hn2).
      subst σ'.
      exists h.
      split.
      + pose proof MSA_unit (Δ', h) as [u' X'].
        unfold aprop.
        pose proof MSA_unit_empty X'.
        apply MSA_comm in X'.
        easy.
      + exact HJ.
  Qed.

  Theorem hoare_comp: ∀ {op e₁ e₂},
      hoare aemp (EComp op e₁ e₂)
        (λ n, aprop ((eval_comp_op op) e₁ e₂ ∧ n = 1 ∨ (¬ (eval_comp_op op) e₁ e₂) ∧ n = 0)).
  Proof.
    intros.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - simpl.
      tauto.
    - intros ?? Hn.
      simpl in Hn; sets_unfold in Hn.
      unfold pure in Hn.
      destruct Hn as (Hn1&Hn2).
      subst σ'.
      exists h.
      split.
      + pose proof MSA_unit (Δ', h) as [u' X'].
        unfold aprop.
        pose proof MSA_unit_empty X'.
        apply MSA_comm in X'.
        easy.
      + exact HJ.
  Qed.

  Theorem hoare_choice: ∀ {P Q e₁ e₂},
      hoare P e₁ Q
    → hoare P e₂ Q
    → hoare P (EChoice e₁ e₂) Q.
  Proof.
    intros ???? H1 H2.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - simpl.
      intros [Hn1|Hn2].
      + apply (H1 _ _ _ _ Hsub HΔ HP HJ).
        exact Hn1.
      + apply (H2 _ _ _ _ Hsub HΔ HP HJ).
        exact Hn2.
    - intros ?? [Hn1|Hn2].
      + apply (H1 _ _ _ _ Hsub HΔ HP HJ).
        exact Hn1.
      + apply (H2 _ _ _ _ Hsub HΔ HP HJ).
        exact Hn2.
  Qed.

  Theorem hoare_assume: ∀ {e},
      hoare aemp (EAssume e) (λ _, (aprop (e ≠ 0))).
  Proof.
    intros ?.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split; [tauto|].
    intros ?? Hn.
    simpl in Hn; sets_unfold in Hn.
    destruct Hn.
    subst σ'.
    exists h.
    split.
    - pose proof MSA_unit (Δ', h) as [u X].
      pose proof MSA_unit_empty X.
      apply MSA_comm in X.
      unfold aprop.
      tauto.
    - exact HJ.
  Qed.

  Theorem hoare_skip:
      hoare aemp ESkip (λ _, aemp).
  Proof.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    + tauto.
    + simpl; sets_unfold.
      intros ?? Hn.
      subst σ'.
      eexists.
      apply (conj HP HJ).
  Qed.

  Theorem hoare_fun_addr: ∀ {f H},
      (f, H) ∈ fst Δ
    → hoare aemp (EFunAddr f) (λ l, astore_fun l H).
  Proof.
    intros ?? HH.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    split.
    - tauto.
    - simpl; sets_unfold.
      intros ?? Hn.
      destruct Hn.
      subst σ'.
      exists h.
      split.
      + unfold lift_assn, astore_fun.
        exists f.
        pose proof MSA_prod_empty HP.
        apply lift_heap_fun in H1.
        pose proof (MSA_positive' (HJ n) (fun_empty H1)).
        simpl.
        rewrite (proj1 H2).
        apply Hsub in HH.
        tauto.
      + apply HJ.
  Qed.

  Theorem hoare_call: ∀ {l Φ Ψ vs},
      hoare (asepcon (astore_fun l (@FunSpec Φ Ψ)) (eval_assn (Φ vs)))
            (ECall l vs)
            (λ n, eval_assn (Ψ vs n)).
  Proof.
    intros ????.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    unfold asepcon in HP.
    destruct HP as (σ₁&σ₂&HJ'&HF&HP).
    unfold astore_fun in HF.
    destruct HF as (f&Hl&HH&Hemp).
    pose proof MSA_join_empty HJ' Hemp as H1.
    subst σ₂.
    destruct σ₁ as [Δ₁ h₁].
    pose proof (proj1 HJ') as H2.
    cbv in H2; destruct H2 as [H2 _].
    subst Δ₁.
    unfold hoare_prog in HΔ.
    unfold hoare_prog_fun in HΔ.
    specialize (proj1 HΔ _ _ _ _ _ _ _ HH HP HJ) as HΔ0.
    pose proof join_fun (proj2 HJ' l) Hl as [H3 _].
    pose proof join_fun (HJ l) H3 as H4.
    split.
    - simpl.
      intros [H|H].
      + destruct H as (f'&Hl'&He).
        apply lift_heap_fun in Hl'.
        rewrite (proj2 H4) in Hl'.
        injection Hl' as Hl'; subst f'.
        apply HΔ0.
        exact He.
      + apply H.
        exists f.
        apply lift_heap_fun.
        easy.
    - intros ?? Hn.
      apply HΔ0.
      simpl in Hn.
      destruct Hn as [(f'&Hl'&Hn')|(_&_&NF&_)].
      + apply lift_heap_fun in Hl'.
        rewrite (proj2 H4) in Hl'.
        injection Hl' as Hl'; subst f'.
        exact Hn'.
      + exfalso.
        apply NF.
        exists f.
        apply lift_heap_fun.
        tauto.
  Qed.

  Theorem hoare_store: ∀ {l v},
      hoare (↑(astore_uninit l))
            (EStore l v)
            (λ _, ↑(astore_int_q l I1 v)).
  Proof.
    intros ??.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    unfold lift_assn, astore_uninit in HP; simpl in HP.
    pose proof join_writable (HJ _) (proj1 HP) as H1.
    split.
    - simpl.
      sets_unfold.
      rewrite (proj2 H1) in HP.
      pose proof ((proj2 lift_heap_writable) (proj1 HP)).
      tauto.
    - intros ?? Hn.
      simpl in Hn.
      destruct Hn as (Hl'&Hl''&Hemp).
      exists (λ l', if l =? l' then CFZ I1 v else h l').
      split.
      + unfold lift_assn, astore_int_q.
        simpl.
        split.
        * rewrite Z.eqb_refl.
          reflexivity.
        * intros l' n0.
          specialize (proj2 HP _ n0).
          apply Z.eqb_neq in n0; rewrite n0.
          tauto.
      + intros l'.
        destruct (Z.eq_dec l l').
        * subst l'.
          rewrite Z.eqb_refl.
          rewrite (proj1 lift_heap_int (conj Hl'' eq_refl)).
          rewrite (proj1 H1).
          constructor.
        * rewrite <- (proj1 lift_heap_eq (Hemp _ n0)).
          apply Z.eqb_neq in n0; rewrite n0.
          apply HJ.
  Qed.

  Theorem hoare_load: ∀ {l q v},
      hoare (↑(astore_int_q l q v))
            (ELoad l)
            (λ n, asepcon (↑(astore_int_q l q v)) (aprop (n = v))).
  Proof.
    intros ???.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    unfold lift_assn, astore_int_q in HP.
    pose proof join_int (HJ _) (proj1 HP) as [??].
    split.
    - simpl.
      intros He.
      apply He.
      exists v.
      eapply lift_heap_int.
      exact H.
    - intros ?? Hn.
      simpl in Hn; sets_unfold in Hn.
      destruct Hn as [Hn ?]; subst σ'.
      exists h.
      split; [|tauto].
      unfold asepcon.
      pose proof MSA_unit (Δ', h) as [u X].
      pose proof MSA_unit_empty X.
      exists (Δ', h), u.
      apply MSA_comm in X.
      unfold lift_assn, astore_int_q.
      simpl snd in HP |- *.
      unfold aprop.
      rewrite (proj1 (proj2 lift_heap_int H)) in Hn; injection Hn as Hn.
      easy.
  Qed.

  Theorem hoare_frame: ∀ {P Q F e},
      hoare P e Q
    → hoare (asepcon P F) e (λ n, asepcon (Q n) F).
  Proof.
    intros ???? H.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    unfold asepcon in HP.
    destruct HP as (σ₁&σ₂&HJ'&HP&HF).
    pose proof MSA_assoc (proj2 HJ') HJ as [f H1].
    destruct σ₁ as [Δ₁ h₁].
    pose proof (proj1 HJ') as H2; simpl in H2.
    destruct H2 as [? HΔ₂].
    subst Δ₁.
    unfold hoare in H.
    specialize (H _ _ _ _ Hsub HΔ HP (proj2 H1)).
    split.
    - apply H.
    - intros ?? Hn.
      pose proof (proj2 H _ _ Hn) as (h'&HQ&HJ'').
      apply MSA_comm in HJ''.
      pose proof MSA_comm (proj1 H1) as H3.
      pose proof MSA_assoc H3 HJ'' as [h'' [H4 ?]].
      exists h''.
      split.
      + unfold asepcon.
        exists (Δ', h'), σ₂.
        apply MSA_comm in H4.
        simpl join.
        tauto.
      + apply MSA_comm.
        tauto.
  Qed.

  Theorem hoare_conseq: ∀ {P P' Q' Q e},
      derivable P P'
    → (∀ n, derivable (Q' n) (Q n))
    → hoare P' e Q'
    → hoare P e Q.
  Proof.
    intros ????? H1 H2 H.
    unfold hoare.
    intros ???? Hsub HΔ HP HJ.
    apply H1 in HP.
    specialize (H _ _ _ _ Hsub HΔ HP HJ).
    split; [tauto|].
    intros ?? Hn.
    unfold derivable in H2.
    apply H in Hn.
    destruct Hn as [h' ?].
    exists h'.
    split.
    - apply H2.
      tauto.
    - tauto.
  Qed.

  Theorem hoare_prop: ∀ {P e Q} {p: Prop},
      (p → hoare P e Q)
    ↔ hoare (asepcon P (aprop p)) e Q.
  Proof.
    intros ????.
    split.
    - intros H.
      unfold hoare.
      intros ???? Hsub HΔ HP HJ.
      unfold asepcon in HP.
      destruct HP as (σ₁&σ₂&?&?&?).
      unfold aprop in H2.
      destruct H2 as [??].
      apply MSA_comm in H0.
      pose proof MSA_join_empty H0 H3.
      subst σ₁.
      eapply (H H2); eauto.
    - intros H Hp.
      unfold hoare, asepcon in H.
      intros ????????.
      eapply H; eauto.
      pose proof MSA_unit (Δ', h) as [u X].
      pose proof MSA_unit_empty X.
      exists (Δ', h), u.
      apply MSA_comm in X.
      easy.
  Qed.

End hoare_expr.

Arguments hoare {χ_ok} {χ_er}.

Definition Hoare Δ P e Q := ∀ χ_ok χ_er, @hoare χ_ok χ_er Δ P e Q.

(* Machine Code Logic. See Magnus O. Myreen,
   'Verified Just-In-Time Compiler on x86'. *)

Definition reg_eqb (r r': reg): bool :=
  match r with
  | SP => match r' with SP => true | _ => false end
  | PC => match r' with PC => true | _ => false end
  | R0 => match r' with R0 => true | _ => false end
  | R1 => match r' with R1 => true | _ => false end
  | R2 => match r' with R2 => true | _ => false end
  | R3 => match r' with R3 => true | _ => false end
  | R4 => match r' with R4 => true | _ => false end
  | R5 => match r' with R5 => true | _ => false end
  end.

Theorem reg_eqb_eq: ∀ r r',
    reg_eqb r r' = true ↔ r = r'.
Proof.
  intros r r'.
  split; destruct r; destruct r'; try auto; try discriminate.
Qed.

Theorem reg_eqb_neq: ∀ r r',
    reg_eqb r r' = false ↔ r ≠ r'.
Proof.
  intros r r'.
  split; destruct r; destruct r'; try auto; try discriminate;
    try (intro C; exfalso; apply C; reflexivity).
Qed.

Theorem reg_eqb_refl: ∀ r, reg_eqb r r = true.
Proof.
  intros r.
  destruct r; tauto.
Qed.

Theorem reg_eq_dec: ∀ (r r': reg), r = r' ∨ r ≠ r'.
Proof.
  intros ? ?.
  destruct (reg_eqb r r') eqn: E.
  - left.
    apply reg_eqb_eq.
    assumption.
  - right.
    apply reg_eqb_neq.
    assumption.
Qed.

Lemma abort_final: ∀ {σ χ_er}, abort χ_er σ → final σ → False.
Proof.
  intros ?? HA HF.
  unfold final in HF.
  unfold abort in HA.
  rewrite HF in HA.
  simpl in HA.
  destruct HA.
Qed.

Lemma step_final: ∀ {σ σ' χ_ok}, step χ_ok σ σ' → final σ → False.
Proof.
  intros ??? Hs HF.
  unfold final in HF.
  unfold step in Hs.
  rewrite HF in Hs.
  simpl in Hs.
  destruct Hs.
Qed.

(* More about proof-relevant multistep. *)

Definition steps_app {χ σ σ₁ σ'}
  (x: steps χ σ σ₁) (y: steps χ σ₁ σ'): steps χ σ σ'.
  induction x.
  - exact y.
  - eapply ss_cons.
    + exact s.
    + apply IHx.
      exact y.
Defined.

Fixpoint steps_len {χ σ σ'} (x: steps χ σ σ'): nat :=
  match x with
  | ss_cons _ _ x' => S (steps_len x')
  | ss_nil _ => 0
  end.

Lemma steps_app_len: ∀ {χ σ σ₁ σ'} (x: steps χ σ σ₁) (y: steps χ σ₁ σ'),
    steps_len (steps_app x y) = (steps_len x + steps_len y)%nat.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.
Qed.

Section induction.

  Require Import Lia.

  Local Open Scope nat.

  Variable χ_ok: sem_ok.
  Variable P: ∀ σ σ', steps χ_ok σ σ' → Prop.
  Hypothesis H: ∀ σ σ' (x: steps χ_ok σ σ'),
      (∀ σ σ' (y: steps χ_ok σ σ'), steps_len y < steps_len x → P σ σ' y)
      → P σ σ' x.

  Theorem steps_ind_by_len:
    ∀ σ σ' (x: steps χ_ok σ σ'), P σ σ' x.
  Proof using H.
    assert (∀ σ σ' (x: steps χ_ok σ σ') σ0 σ0' (y: steps χ_ok σ0 σ0'),
               steps_len y <= steps_len x → P σ0 σ0' y).
    - induction x; intros; apply H; intros.
      + invert H0.
        rewrite H3 in H1.
        invert H1.
      + apply IHx.
        simpl in H0.
        lia.
    - intros.
      eapply H0.
      apply Nat.le_refl.
  Qed.

End induction.

Definition nontrivial_split {χ σ σ'} (x: steps χ σ σ') σ₁ :=
  ∃ σ₂ H y z, x = @ss_cons χ σ σ₂ σ' H (@steps_app _ σ₂ σ₁ σ' y z).

Lemma nontrivial_cons: ∀ {χ σ₁ σ₂ σ₃ σ} {x: steps χ σ₂ σ₃} {H: step χ σ₁ σ₂},
    nontrivial_split x σ → nontrivial_split (ss_cons χ H x) σ.
Proof.
  intros.
  unfold nontrivial_split in H0 |- *.
  destruct H0 as (σ₄&H4&y&z&H0).
  exists _, H.
  rewrite H0.
  exists (ss_cons _ H4 y), z.
  tauto.
Qed.

Lemma nontrivial_app: ∀ {χ σ₁ σ₂ σ₃ σ}
                        {x: steps χ σ₁ σ₂} {y: steps χ σ₂ σ₃},
    nontrivial_split y σ
    → nontrivial_split (steps_app x y) σ.
Proof.
  intros.
  induction x.
  - simpl.
    exact H.
  - simpl.
    apply nontrivial_cons.
    apply IHx.
    exact H.
Qed.

(* More about proof-relevant multistep End. *)

Section hoare_mach.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.
  Variable Δ: prog_spec.

  Definition hoare_final (P Q: assn ΣA) :=
    ∀ Δ' h g σ,
      spec_include Δ Δ' → hoare_prog Δ' χ_ok χ_er
     → P (Δ', h) → join h g (lift_LΣ σ)
     → ¬ σ ∈ eval_mach_er χ_ok χ_er
     ∧ ∀ σ',
         (σ, σ') ∈ eval_mach_ok χ_ok
       → ∃ h', Q (Δ', h') ∧ join h' g (lift_LΣ σ').

  Definition hoare_steps (P Q: assn ΣA) :=
    ∀ Δ' h g σ σ₁ (x: steps χ_ok σ σ₁),
      spec_include Δ Δ' → hoare_prog Δ' χ_ok χ_er
    → P (Δ', h) → join h g (lift_LΣ σ)
    → abort χ_er σ₁ ∨ final σ₁
    → ∃ h' σ',
        nontrivial_split x σ'
      ∧ Q (Δ', h') ∧ join h' g (lift_LΣ σ').

  (* we default to lists while you can use more efficient representations. *)
  Definition code := list (Z * ins).

  Fixpoint astore_array_q a q l: assn fic_heap :=
    match l with
    | [] => aemp
    | n :: l' => asepcon (astore_int_q a q n) (astore_array_q (a + 1) q l')
    end.              

  Definition astore_ins_q a q i: assn fic_heap :=
    astore_array_q a q (encode i).

  Fixpoint astore_code_q q (c: code): assn fic_heap :=
    match c with
    | [] => aemp
    | (a, i) :: c' => asepcon (astore_ins_q a q i) (astore_code_q q c')
    end.

  Definition lift_assn_heap_ΣA_base (P: assn fic_heap): assn fic_LΣ :=
    λ σ, MSA_empty (rg σ) ∧ MSA_empty (st σ) ∧ P (hp σ).

  Notation "'⇑'" := lift_assn_heap_ΣA_base.

  Definition hoare_code_final P c Q :=
    ∀ q, hoare_final (asepcon P (↑(⇑(astore_code_q q c))))
                     (asepcon Q (↑(⇑(astore_code_q q c)))).

  Definition hoare_code_steps P c Q :=
    ∀ q, hoare_steps (asepcon P (↑(⇑(astore_code_q q c))))
                     (asepcon Q (↑(⇑(astore_code_q q c)))).

  Theorem hoare_seq: ∀ {P Q R},
      hoare_steps P Q → hoare_steps Q R
    → hoare_steps P R.
  Proof.
    intros ??? H1 H2.
    unfold hoare_steps.
    intros ?????? Hsub HS HP HJ Hend.
    specialize (H1 _ _ _ _ _ x Hsub HS HP HJ Hend).
    destruct H1 as (h₂&σ₂&Hsplt&HQ&HJ').
    unfold nontrivial_split in Hsplt.
    destruct Hsplt as (σ₃&H3&y&z&Happ).
    specialize (H2 _ _ _ _ _ z Hsub HS HQ HJ' Hend).
    destruct H2 as (h'&σ'&Hsplt'&HR&HJ'').
    exists h', σ'.
    split; [|tauto].
    rewrite Happ.
    apply nontrivial_cons.
    apply nontrivial_app.
    exact Hsplt'.
  Qed.

  Theorem hoare_inv: ∀ {I Q},
      hoare_steps I (adisj I Q) → hoare_steps I Q.
  Proof.
    unfold hoare_steps.
    intros ?? H.
    intros ??????.
    revert h g.
    induction σ, σ₁, x using (steps_ind_by_len _).
    intros ?? Hsub HS HI HJ Hend.
    specialize (H _ _ _ _ _ x Hsub HS HI HJ Hend).
    destruct H as (h₁&σ₁&Hsplt&HIQ&HJ').
    destruct HIQ.
    - unfold nontrivial_split in Hsplt.
      destruct Hsplt as (σ₂&Hstep&y&z&Hx).
      assert (steps_len z < steps_len x)%nat as Hlt.
      { rewrite Hx.
        simpl.
        pose proof steps_app_len y z.
        lia. }
      specialize (H0 _ _ _ Hlt _ _ Hsub HS H HJ' Hend).
      destruct H0 as (h'&σ₃&Hsplt'&HQ&HJ'').
      exists h', σ₃.
      split; [|tauto].
      rewrite Hx.
      apply nontrivial_cons.
      apply nontrivial_app.
      exact Hsplt'.
    - exists h₁, σ₁.
      tauto.
  Qed.

  Definition areg_int (r: reg) (n: Z): assn fic_LΣ :=
    λ σ, rg σ r = Some n ∧ (∀ r', r ≠ r' → rg σ r' = None)
       ∧ MSA_empty (st σ) ∧ MSA_empty (hp σ).

  Definition areg_uninit r := aex (λ n, areg_int r n).

  Definition astack_int (a n: Z): assn fic_LΣ :=
    λ σ, st σ a = Some n ∧ (∀ a', a ≠ a' → st σ a' = None)
       ∧ MSA_empty (rg σ) ∧ MSA_empty (hp σ).

  Definition astack_uninit a := aex (λ n, astack_int a n).

  Theorem hoare_const: ∀ {r n i},
    hoare_code_steps (↑(asepcon (areg_int PC i) (areg_uninit r)))
                     [(i, IConst n r)]
                     (↑(asepcon (areg_int PC (i + 3)) (areg_int r n))).
  Proof.
    (* intros ???. *)
    (* unfold hoare_code_steps; intros q. *)
    (* unfold hoare_steps. *)
    (* intros ?????? Hin HΔ HP HJ Hend. *)
    (* destruct HP as ((?&h₁)&(?&h₂)&HJh&HP&Hc). *)
    (* destruct HP as (h₃&h₄&HJh₁&HPC&Hr). *)
    (* unfold lift_assn, lift_assn_heap_ΣA_base in Hc. *)
    (* pose proof (proj1 HJh) as [??]. *)
    (* simpl in H, H0; subst p p0. *)
    (* destruct HJh as [_ HJh]. *)
    (* simpl snd in HJh, HJh₁, Hc. *)
    (* (* lift PC *) *)
    (* unfold areg_int in HPC. *)
    (* pose proof compatible_opt_some (proj1 (proj1 HJh₁) _) (proj1 HPC) as H1. *)
    (* pose proof compatible_opt_some (proj1 (proj1 HJh) _) (proj2 H1) as H2. *)
    (* pose proof compatible_opt_some (proj1 (proj1 HJ) _) (proj2 H2) as H3. *)
    (* simpl in H3; injection (proj2 H3) as H4. *)
    (* (* lift z *) *)
    (* unfold astore_code_q, single_code in Hc. *)
    (* assert (hp h₂ i = CZ q z) as H5. *)
    (* { specialize (proj2 (proj2 Hc) i). *)
    (*   rewrite Z.eqb_refl. *)
    (*   tauto. } *)
    (* pose proof compatible_int (MSA_comm (proj2 HJh _)) H5 as [? H6]. *)
    (* pose proof compatible_int (proj2 HJ _) H6 as [? H7]. *)
    (* simpl in H7. *)
    (* destruct x. *)
    (* { exfalso. *)
    (*   unfold abort, final, eval_ins_er, cur_ins in Hend. *)
    (*   rewrite H4, H7, HI in Hend. *)
    (*   destruct Hend as [H|H]; [destruct H|discriminate H]. } *)
    (* exists (λ r', if reg_eqb r r' then Some n else rg h r', st h, hp h), σ₁. *)
    (* split. *)
    (* { unfold nontrivial_split. *)
    (*   exists σ₁, s, (ss_nil _), x. *)
    (*   reflexivity. } *)
    (* split. *)
  Admitted.

  Theorem hoare_nop: ∀ {i},
    hoare_code_steps (↑(areg_int PC i))
                     [(i, INop)]
                     (↑(areg_int PC (i + 1))).
  Proof. Admitted.

  Theorem hoare_jmp_jump: ∀ {i r₁ r₂ x n},
      x > 0
    → hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (areg_int r₁ x) (areg_int r₂ n))))
        [(i, IJmp r₁ r₂)]
        (↑(asepcon (areg_int PC (i + n)) (asepcon (areg_int r₁ x) (areg_int r₂ n)))).
  Proof. Admitted.

  Theorem hoare_jmp_next: ∀ {i r₁ r₂ x n},
      x <= 0
    → hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (areg_int r₁ x) (areg_int r₂ n))))
        [(i, IJmp r₁ r₂)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (areg_int r₁ x) (areg_int r₂ n)))).
  Proof. Admitted.

  Theorem hoare_arith_two: ∀ {i op r₁ r₂ n m},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (areg_int r₁ m) (areg_int r₂ n))))
        [(i, IArith op r₁ r₂)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (areg_int r₁ m) (areg_int r₂ ((eval_arith_op op) n m))))).
  Proof. Admitted.

  Theorem hoare_arith_one: ∀ {i op r n},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (areg_int r n)))
        [(i, IArith op r r)]
        (↑(asepcon (areg_int PC (i + 3)) (areg_int r ((eval_arith_op op) n n)))).
  Proof. Admitted.

  Theorem hoare_load_two: ∀ {i r₁ r₂ a n q},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (⇑(astore_int_q a q n)) (asepcon (areg_int r₁ a) (areg_uninit r₂)))))
        [(i, ILoad r₁ r₂)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (⇑(astore_int_q a q n)) (asepcon (areg_int r₁ a) (areg_int r₂ n))))).
  Proof. Admitted.

  Theorem hoare_load_one: ∀ {i r a n q},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (⇑(astore_int_q a q n)) (areg_int r a))))
        [(i, ILoad r r)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (⇑(astore_int_q a q n)) (areg_int r n)))).
  Proof. Admitted.

  Theorem hoare_store_two: ∀ {i r₁ r₂ a n},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (⇑(astore_uninit a)) (asepcon (areg_int r₁ n) (areg_int r₂ a)))))
        [(i, ILoad r₁ r₂)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (⇑(astore_int_q a I1 n)) (asepcon (areg_int r₁ n) (areg_int r₂ a))))).
  Proof. Admitted.

  Theorem hoare_store_one: ∀ {i r a},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (⇑(astore_uninit a)) (areg_int r a))))
        [(i, ILoad r r)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (⇑(astore_int_q a I1 a)) (areg_int r a)))).
  Proof. Admitted.

  Theorem hoare_load_stack_two: ∀ {i r₁ r₂ a n},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (astack_int a n) (asepcon (areg_int r₁ a) (areg_uninit r₂)))))
        [(i, ILoad r₁ r₂)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (astack_int a n) (asepcon (areg_int r₁ a) (areg_int r₂ n))))).
  Proof. Admitted.

  Theorem hoare_load_stack_one: ∀ {i r a n},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (astack_int a n) (areg_int r a))))
        [(i, ILoad r r)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (astack_int a n) (areg_int r n)))).
  Proof. Admitted.

  Theorem hoare_store_stack_two: ∀ {i r₁ r₂ a n},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (astack_uninit a) (asepcon (areg_int r₁ n) (areg_int r₂ a)))))
        [(i, ILoad r₁ r₂)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (astack_int a n) (asepcon (areg_int r₁ n) (areg_int r₂ a))))).
  Proof. Admitted.

  Theorem hoare_store_stack_one: ∀ {i r a},
      hoare_code_steps
        (↑(asepcon (areg_int PC i) (asepcon (astack_uninit a) (areg_int r a))))
        [(i, ILoad r r)]
        (↑(asepcon (areg_int PC (i + 3)) (asepcon (astack_int a a) (areg_int r a)))).
  Proof. Admitted.

End hoare_mach.

Arguments hoare_final {χ_ok} {χ_er}.

Definition HoareFinal Δ P Q := ∀ χ_ok χ_er, @hoare_final χ_ok χ_er Δ P Q.

(* Machine Code Logic End. *)

Definition provable_fun (Δ: prog_spec) (p: prog) :=
  ∀ f e Φ Ψ vs,
    In (f, e) p → (f, FunSpec Φ Ψ) ∈ fst Δ
  → Hoare Δ (eval_assn (Φ vs)) (e Z expr_sem vs) (λ n, eval_assn (Ψ vs n)).

Definition provable_mach (Δ: prog_spec) :=
  ∀ Φ Ψ,
    MachSpec Φ Ψ ∈ snd Δ
  → HoareFinal Δ (eval_assn Φ) (eval_assn Ψ).

Definition provable Δ p := provable_fun Δ p ∧ provable_mach Δ.

Lemma spec_include_refl: ∀ {Δ}, spec_include Δ Δ.
Proof. intros. split; apply Sets_included_refl. Qed.

Lemma hoare_ok_iter1: ∀ {Δ χ_ok χ_er} {p: prog},
    hoare_prog Δ χ_ok χ_er
  → provable Δ p
  → hoare_prog Δ (eval_prog_ok χ_ok χ_er p) χ_er.
Proof.
  intros ???? H Hfs.
  unfold hoare_prog.
  split.
  - unfold hoare_prog_fun, eval_prog_ok.
    intros ??????? Hin HP HJ.
    split.
    + eapply H; eauto.
    + intros ?? [Hn|Imposible].
      2: { destruct Imposible as (?&?&?&_).
           discriminate H0. }
      destruct Hn as (?&?&?&?&?&(f'&e)&Heq1&Heq2&HIn&Hn).
      injection Heq1; injection Heq2; intros.
      subst x x0 x1 x2 x3; clear Heq1 Heq2.
      unfold eval_fun_ok in Hn.
      destruct Hn as [H0 Hn]; simpl in H0; subst f'.
      destruct Hfs as [Hfs _]; unfold provable_fun in Hfs.
      specialize (Hfs _ _ _ _ vs HIn Hin).
      unfold Hoare, hoare in Hfs.
      specialize (Hfs _ _ _ _ _ _ spec_include_refl H HP HJ).
      apply Hfs.
      exact Hn.
  - unfold hoare_prog_mach, eval_prog_ok.
    intros ????? Hin HP HJ.
    split.
    + eapply H; eauto.
    + intros ? [Impossible|Hn].
      { destruct Impossible as (?&?&?&?&?&?&?&_).
        discriminate H0. }
      destruct Hn as (?&?&Heq1&Heq2&Hn).
      injection Heq1; injection Heq2; intros.
      subst x x0; clear Heq1 Heq2.
      unfold eval_mach_ok in Hn.
      destruct Hn as [x Hn].
      destruct Hfs as [_ Hfs]; unfold provable_mach in Hfs.
      specialize (Hfs _ _ Hin).
      unfold HoareFinal, hoare_final in Hfs.
      specialize (Hfs _ _ _ _ _ _ spec_include_refl H HP HJ).
      apply Hfs.
      unfold eval_mach_ok; sets_unfold.
      exists x.
      exact Hn.
Qed.

Lemma hoare_er_iter1: ∀ {Δ χ_ok χ_er} {p: prog},
    hoare_prog Δ χ_ok χ_er
  → provable Δ p
  → hoare_prog Δ χ_ok (eval_prog_er χ_ok χ_er p).
Proof.
  intros ???? H Hfs.
  unfold hoare_prog.
  split.
  - unfold hoare_prog_fun, eval_prog_er.
    intros ??????? Hin HP HJ.
    split.
    + sets_unfold.
      intros [Hn|Imposible].
      2: { destruct Imposible as (?&?&?&_).
           discriminate H0. }
      destruct Hn as (?&?&?&(f'&e)&Heq1&HIn&Hn).
      injection Heq1; intros.
      subst x x0 x1; clear Heq1.
      unfold eval_fun_er in Hn.
      destruct Hn as [H0 Hn]; simpl in H0; subst f'.
      destruct Hfs as [Hfs _]; unfold provable_fun in Hfs.
      specialize (Hfs _ _ _ _ vs HIn Hin).
      unfold Hoare, hoare in Hfs.
      specialize (Hfs _ _ _ _ _ _ spec_include_refl H HP HJ).
      apply Hfs.
      exact Hn.
    + eapply H; eauto.
  - unfold hoare_prog_mach, eval_prog_er.
    intros ????? Hin HP HJ.
    split.
    + intros [Impossible|Hn].
      { destruct Impossible as (?&?&?&?&?&?&?&_).
        discriminate H0. }
      destruct Hn as (?&Heq&Hn).
      injection Heq; intros.
      subst x; clear Heq.
      unfold eval_mach_ok in Hn.
      destruct Hn as [x Hn].
      destruct Hfs as [_ Hfs]; unfold provable_mach in Hfs.
      specialize (Hfs _ _ Hin).
      unfold HoareFinal, hoare_final in Hfs.
      specialize (Hfs _ _ _ _ _ _ spec_include_refl H HP HJ).
      apply Hfs.
      unfold eval_mach_ok; sets_unfold.
      exists x.
      exact Hn.
    + eapply H; eauto.
Qed.

(* rephrase so that χ_ok (and consequently Lfix) only appears once *)
Definition hoare_prog_ok (Δ: prog_spec) (χ_ok: sem_ok) :=
  ∀ x y,
    (x, y) ∈ χ_ok
  → match x, y with
    | inl (f, vs, σ), inl (n, σ') =>
        ∀ Φ Ψ h g,
          (f, FunSpec Φ Ψ) ∈ fst Δ
        → eval_assn (Φ vs) (Δ, h) → join h g (lift_heap σ)
        → ∃ h', eval_assn (Ψ vs n) (Δ, h') ∧ join h' g (lift_heap σ')
    | inr σ, inr σ' =>
        ∀ Φ Ψ h g,
          MachSpec Φ Ψ ∈ snd Δ
        → eval_assn Φ (Δ, h) → join h g (lift_LΣ σ)
        → ∃ h', eval_assn Ψ (Δ, h') ∧ join h' g (lift_LΣ σ')
    | _, _ => True
    end.

Lemma hoare_prog_ok_iff: ∀ {Δ χ},
    hoare_prog_ok Δ χ ↔ hoare_prog Δ χ ∅.
Proof.
  intros ??.
  split.
  - intros H.
    unfold hoare_prog, hoare_prog_fun, hoare_prog_mach.
    split.
    + intros ??????? Hin HP HJ.
      split; [tauto|].
      intros ?? Hn.
      unfold hoare_prog_ok in H.
      specialize (H _ _ Hn).
      simpl in H.
      specialize (H _ _ _ _ Hin HP HJ).
      exact H.
    + intros ????? Hin HP HJ.
      split; [tauto|].
      intros ? Hn.
      unfold hoare_prog_ok in H.
      specialize (H _ _ Hn).
      simpl in H.
      specialize (H _ _ _ _ Hin HP HJ).
      exact H.
  - intros H.
    unfold hoare_prog_ok.
    intros ?? Hn.
    destruct x as [((f&v)&σ)|σ]; destruct y as [(n&σ')|σ']; auto.
    + intros ???? Hin HP HJ.
      unfold hoare_prog, hoare_prog_fun in H.
      apply (proj1 H _ _ _ _ _ _ _ Hin HP HJ).
      apply Hn.
    + intros ???? Hin HP HJ.
      unfold hoare_prog, hoare_prog_mach in H.
      apply (proj2 H _ _ _ _ _ Hin HP HJ).
      apply Hn.
Qed.

Lemma provable_hoare_ok: ∀ {Δ p},
    provable Δ p
  → hoare_prog_ok Δ (eval_ok p).
Proof.
  intros ?? H.
  unfold hoare_prog_ok.
  intros ?? Hn.
  unfold eval_ok, Lfix in Hn.
  destruct Hn as [i Hn].
  generalize dependent x.
  generalize dependent y.
  induction i.
  - intros.
    induction Hn.
  - intros ?? Hn.
    simpl in Hn.
    eapply hoare_prog_ok_iff.
    2: { apply Hn. }
    apply hoare_ok_iter1.
    + eapply hoare_prog_ok_iff.
      unfold hoare_prog_ok.
      intros ???.
      apply IHi.
      assumption.
    + assumption.
Qed.

Definition hoare_prog_er (Δ: prog_spec) (χ_er: sem_er) :=
  ∀ x,
    x ∈ χ_er
  → match x with
    | inl (f, vs, σ) =>
        ∀ Φ Ψ h g,
          (f, FunSpec Φ Ψ) ∈ fst Δ
        → eval_assn (Φ vs) (Δ, h) → join h g (lift_heap σ)
        → False
    | inr σ =>
        ∀ Φ Ψ h g,
          MachSpec Φ Ψ ∈ snd Δ
        → eval_assn Φ (Δ, h) → join h g (lift_LΣ σ)
        → False
    end.

Lemma hoare_prog_er_iff: ∀ {Δ p χ},
    hoare_prog_ok Δ (eval_ok p) →
    hoare_prog_er Δ χ ↔ hoare_prog Δ (eval_ok p) χ.
Proof.
  intros ??? Hok.
  split.
  - intros H.
    unfold hoare_prog, hoare_prog_fun, hoare_prog_mach.
    split.
    + intros ??????? Hin HP HJ.
      split.
      * intros Hn.
        unfold hoare_prog_er in H.
        specialize (H _ Hn).
        simpl in H.
        specialize (H _ _ _ _ Hin HP HJ).
        exact H.
      * apply hoare_prog_ok_iff in Hok.
        eapply Hok; eauto.
    + intros ????? Hin HP HJ.
      split.
      * intros Hn.
        unfold hoare_prog_er in H.
        specialize (H _ Hn).
        simpl in H.
        specialize (H _ _ _ _ Hin HP HJ).
        exact H.
      * apply hoare_prog_ok_iff in Hok.
        eapply Hok; eauto.
  - intros H.
    unfold hoare_prog_er.
    intros ? Hn.
    destruct x as [((f&v)&σ)|σ].
    + intros ???? Hin HP HJ.
      unfold hoare_prog, hoare_prog_fun in H.
      apply (proj1 H _ _ _ _ _ _ _ Hin HP HJ).
      apply Hn.
    + intros ???? Hin HP HJ.
      unfold hoare_prog, hoare_prog_mach in H.
      apply (proj2 H _ _ _ _ _ Hin HP HJ).
      apply Hn.
Qed.

Lemma provable_hoare_er: ∀ {Δ p},
    provable Δ p
  → hoare_prog_er Δ (eval_er p).
Proof.
  intros ?? H.
  pose proof provable_hoare_ok H as Hok.
  pose proof (λ χ, @hoare_prog_er_iff _ _ χ Hok) as Hiff.
  unfold hoare_prog_er.
  intros ? Hn.
  unfold eval_er, Lfix in Hn.
  destruct Hn as [i Hn].
  generalize dependent x.
  induction i.
  - intros.
    induction Hn.
  - intros ? Hn.
    simpl in Hn.
    eapply Hiff.
    2: { apply Hn. }
    apply hoare_er_iter1.
    + eapply hoare_prog_er_iff.
      assumption.
      unfold hoare_prog_er.
      intros ??.
      apply IHi.
      assumption.
    + assumption.
Qed.

Lemma provable_hoare: ∀ {Δ p},
    provable Δ p → hoare_prog Δ (eval_ok p) (eval_er p).
Proof.
  intros ?? H.
  apply hoare_prog_er_iff.
  - apply provable_hoare_ok.
    assumption.
  - apply provable_hoare_er.
    assumption.
Qed.

(* Logic End. *)

(* Derived Example. *)

Section hoare_cexpr.

  Variable χ_ok: sem_ok.
  Variable χ_er: sem_er.
  Variable Δ: prog_spec.

  Definition choare P ce Q := @hoare χ_ok χ_er Δ P (compile Z expr_sem ce) Q.

  Lemma hoare_frame_emp: ∀ {e P Q},
      @hoare χ_ok χ_er Δ aemp e Q
    → @hoare χ_ok χ_er Δ P e (λ v, (asepcon P (Q v))).
  Proof.
    intros.
    eapply hoare_conseq.
    eapply derivable_trans.
    eapply (proj1 emp_sepcon_unit).
    eapply sepcon_comm.
    intros; apply sepcon_comm.
    eapply hoare_frame.
    apply H.
  Qed.

  Lemma hoare_assume': ∀ {P e},
      @hoare χ_ok χ_er Δ P (EAssume e) (λ _, (asepcon P (aprop (e ≠ 0)))).
  Proof.
    intros.
    apply hoare_frame_emp.
    eapply hoare_assume.
  Qed.

  Lemma hoare_val': ∀ {P n},
      @hoare χ_ok χ_er Δ P (EVal n) (λ m, (asepcon P (aprop (n = m)))).
  Proof.
    intros.
    apply hoare_frame_emp.
    eapply hoare_val.
  Qed.

  Theorem hoare_comp': ∀ {op e₁ e₂ P},
      @hoare χ_ok χ_er Δ P (EComp op e₁ e₂) (λ n, (asepcon P (aprop ((eval_comp_op op) e₁ e₂ ∧ n = 1 ∨ (¬ (eval_comp_op op) e₁ e₂) ∧ n = 0)))).
  Proof.
    intros.
    apply hoare_frame_emp.
    eapply hoare_comp.
  Qed.

  Theorem hoare_skip': ∀ {P},
      @hoare χ_ok χ_er Δ P ESkip (λ _, P).
  Proof.
    intros.
    eapply hoare_conseq.
    eapply derivable_trans.
    eapply (proj1 emp_sepcon_unit).
    eapply sepcon_comm.
    intros.
    eapply derivable_trans.
    2: { eapply (proj2 emp_sepcon_unit). }
    apply sepcon_comm.
    eapply hoare_frame.
    eapply hoare_skip.
  Qed.

  Theorem choare_while: ∀ {c e I Q},
      choare I c Q
    → (∀ x, x ≠ 0 → choare (Q x) e (λ _, I))
    → choare I (CEWhile c e) (λ _, Q 0).
  Proof.
    intros ???? Hc He.
    unfold choare.
    simpl.
    eapply hoare_fix.
    intros x Hx.
    unfold EIf.
    eapply hoare_bind.
    apply Hc.
    intros v.
    eapply hoare_choice.
    eapply hoare_bind.
    eapply hoare_assume'.
    intros ?.
    simpl.
    eapply hoare_bind.
    apply hoare_prop.
    apply He.
    intros.
    simpl.
    apply Hx.
    eapply hoare_bind.
    eapply hoare_bind.
    eapply hoare_val'.
    intros.
    simpl.
    apply hoare_prop.
    intros.
    subst v0.
    eapply hoare_comp'.
    intros.
    simpl.
    eapply hoare_bind.
    eapply hoare_assume'.
    intros.
    simpl.
    apply hoare_prop.
    intros ?.
    apply hoare_prop.
    intros.
    destruct H0; [|tauto].
    destruct H0; subst v.
    apply hoare_skip'.
  Qed.

End hoare_cexpr.

(* Derived Example End. *)

(* TODO: proof theory: composability *)
