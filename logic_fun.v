Require Import Unicode.Utf8_core.
Require Import Strings.String.
Require Import ZArith.ZArith.

Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import FP.SetsFixedpoints.

Require Import thesis.interval.
Require Import thesis.lang.
Require Import thesis.semantics.
Require Import thesis.sepalg.
Require Import thesis.logic_prelude.

Local Open Scope Z.
Local Open Scope sets.

Set Default Proof Using "Type".

Section hoare_expr.

  Variable Δ: prog_spec.
  Variable ctx: ProofContext Δ.

  #[local] Notation "'χ_ok'" := (ctx.(ctx_χ_ok Δ)).
  #[local] Notation "'χ_er'" := (ctx.(ctx_χ_er Δ)).
  #[local] Notation "'Δ''" := (ctx.(ctx_Δ' Δ)).
  #[local] Notation "'Hsub'" := (ctx.(ctx_Hsub Δ)).
  #[local] Notation "'HΔ'" := (ctx.(ctx_HΔ Δ)).

  Definition hoare (P: assn ΣC) (e: expr Z expr_sem) (Q: Z → assn ΣC) :=
    ∀ h g σ,
      P (Δ', h) → join h g (lift_heap σ)
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
    intros ??? HP HJ.
    split.
    - simpl; sets_unfold.
      specialize (H1 _ _ _ HP HJ) as (H1e&H1n).
      intros [H|(n&σ'&Hn1&He2)].
      + apply H1e.
        exact H.
      + specialize (H1n _ _ Hn1) as (?&HQ&HJ').
        unfold hoare in H2.
        specialize (H2 _ _ _ _ HQ HJ').
        apply H2.
        exact He2.
    - simpl; sets_unfold.
      intros ?? (m&σ'&Hn1&Hn2).
      unfold hoare in H1.
      specialize (H1 _ _ _ HP HJ) as (_&H1n).
      specialize (H1n _ _ Hn1) as (?&HQ&HJ').
      unfold hoare in H2.
      specialize (H2 _ _ _ _ HQ HJ') as (?&H2n).
      apply H2n.
      exact Hn2.
  Qed.

  Definition hoare_ok (P: assn ΣC) (e: expr Z expr_sem) (Q: Z → assn ΣC) :=
    ∀ h g σ,
      P (Δ', h) → join h g (lift_heap σ)
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
    intros ??? HI HJ.
    simpl; unfold Lfix.
    intros ?? [i Hn].
    generalize dependent Hn.
    generalize dependent HJ.
    generalize dependent HI.
    generalize dependent σ'.
    generalize dependent n.
    generalize dependent σ.
    generalize dependent g.
    generalize dependent h.
    induction i.
    + simpl.
      intros.
      tauto.
    + simpl Nat.iter.
      intros ????? HI HJ Hn.
      unfold hoare in H.
      eapply H; eauto.
      2: { apply Hn. }
      intros.
      split; [tauto|].
      intros.
      eapply IHi; eauto.
  Qed.

  Theorem hoare_fix: ∀ {I Q e},
      (∀ x, hoare I (EFixVar x) Q → hoare I (e x) Q)
    → hoare I (EFix e) Q.
  Proof.
    intros ??? H.
    unfold hoare.
    simpl.
    intros ??? HI HJ.
    split.
    - simpl; unfold Lfix.
      intros [i Hn].
      generalize dependent Hn.
      generalize dependent HJ.
      generalize dependent HI.
      generalize dependent σ.
      generalize dependent g.
      generalize dependent h.
      induction i.
      + simpl.
        tauto.
      + simpl.
        intros ??? HI HJ Hn.
        unfold hoare in H.
        eapply H; simpl; eauto.
        2: { apply Hn. }
        simpl.
        clear h g σ HI HJ Hn.
        intros ??? HI HJ.
        pose proof hoare_fix_ok H.
        split.
        * eauto.
        * eapply H0; eauto.
    - eapply hoare_fix_ok; eauto.
  Qed.

  Theorem hoare_var: ∀ {x},
      hoare aemp (EVar x) (λ m, ⦃ ⟨ x = m ⟩ ⦄).
  Proof.
    intros.
    unfold hoare.
    intros ??? HP HJ.
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
      hoare aemp (EVal n) (λ m, ⦃ ⟨ n = m ⟩ ⦄).
  Proof.
    intros.
    unfold hoare.
    intros ??? HP HJ.
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
      hoare aemp (EArith op e₁ e₂) (λ n, ⦃ ⟨ n = (eval_arith_op op) e₁ e₂ ⟩ ⦄).
  Proof.
    intros.
    unfold hoare.
    intros ??? HP HJ.
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
            (λ n, ⦃ ⟨ (eval_comp_op op) e₁ e₂ ∧ n = 1 ∨ (¬ (eval_comp_op op) e₁ e₂) ∧ n = 0⟩ ⦄).
  Proof.
    intros.
    unfold hoare.
    intros ??? HP HJ.
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
    intros ??? HP HJ.
    split.
    - simpl.
      intros [Hn1|Hn2].
      + apply (H1 _ _ _ HP HJ).
        exact Hn1.
      + apply (H2 _ _ _ HP HJ).
        exact Hn2.
    - intros ?? [Hn1|Hn2].
      + apply (H1 _ _ _ HP HJ).
        exact Hn1.
      + apply (H2 _ _ _ HP HJ).
        exact Hn2.
  Qed.

  Theorem hoare_assume: ∀ {e},
      hoare aemp (EAssume e) (λ _, ⦃ ⟨ e ≠ 0 ⟩ ⦄).
  Proof.
    intros ?.
    unfold hoare.
    intros ??? HP HJ.
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
    intros ??? HP HJ.
    split.
    + tauto.
    + simpl; sets_unfold.
      intros ?? Hn.
      subst σ'.
      eexists.
      apply (conj HP HJ).
  Qed.

  Theorem hoare_fun_addr: ∀ {f Φ Ψ},
      (f, FunSpec Φ Ψ) ∈ fst Δ
    → hoare aemp (EFunAddr f) (λ v, ⦃ 𝔉 {{{Φ}}} v {{{Ψ}}} ⦄).
  Proof.
    intros ??? HH.
    unfold hoare.
    intros ??? HP HJ.
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
        apply lift_heap_fun in H0.
        pose proof (MSA_positive' (HJ n) (fun_empty H0)).
        simpl.
        rewrite (proj1 H1).
        apply Hsub in HH.
        tauto.
      + apply HJ.
  Qed.

  Theorem hoare_call: ∀ {l Φ Ψ vs},
      hoare ⦃ 𝔉 {{{Φ}}} l {{{Ψ}}} * ⟦Φ vs⟧ ⦄
            (ECall l vs)
            (λ n, ⟦Ψ vs n⟧).
  Proof.
    intros ????.
    unfold hoare.
    intros ??? HP HJ.
    pose proof destruct_sepcon_liftΣ HP as (h₁&h₂&HF&HP'&HJ').
    unfold astore_fun in HF.
    destruct HF as (f&Hl&HH&Hemp).
    pose proof MSA_join_empty HJ' (proj2 (MSA_prod_empty Hemp)) as H1.
    subst h₂.
    pose proof HΔ as HΔ.
    unfold hoare_prog in HΔ.
    unfold hoare_prog_fun in HΔ.
    specialize (proj1 HΔ _ _ _ _ _ _ _ HH HP' HJ) as HΔ0.
    pose proof join_fun (HJ' l) Hl as [H3 _].
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
      hoare ⦃ [l ↦ -] ⦄
            (EStore l v)
            (λ _, ⦃ [l ↦ v] ⦄).
  Proof.
    intros ??.
    unfold hoare.
    intros ??? HP HJ.
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
        * rewrite<- (proj1 lift_heap_eq (Hemp _ n0)).
          apply Z.eqb_neq in n0; rewrite n0.
          apply HJ.
  Qed.

  Theorem hoare_load: ∀ {l q v},
      hoare ⦃ [l ↦[q] v] ⦄
            (ELoad l)
            (λ n, ⦃ [l ↦[q] v] * ⟨n = v⟩ ⦄).
  Proof.
    intros ???.
    unfold hoare.
    intros ??? HP HJ.
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
    → hoare ⦃ P * F ⦄ e (λ n, ⦃ Q n * F ⦄).
  Proof.
    intros ???? H.
    unfold hoare.
    intros ??? HP HJ.
    unfold asepcon in HP.
    pose proof destruct_sepcon_liftΣ HP as (h₁&h₂&HP'&HF&HJ').
    pose proof MSA_assoc HJ' HJ as [f H1].
    unfold hoare in H.
    specialize (H _ _ _ HP' (proj2 H1)).
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
        exists (Δ', h'), (Δ', h₂).
        apply MSA_comm in H4.
        simpl join.
        tauto.
      + apply MSA_comm.
        tauto.
  Qed.

  Theorem hoare_conseq: ∀ {P Q' Q e},
      (∀ n, (Q' n) ⊢ (Q n))
    → hoare P e Q'
    → hoare P e Q.
  Proof.
    intros ???? H2 H.
    unfold hoare.
    intros ??? HP HJ.
    specialize (H _ _ _ HP HJ).
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

  Definition wp (e: expr Z expr_sem) (Q: Z → assn ΣC): assn ΣC :=
    λ h, ∀ g σ,
        join h g (Δ', lift_heap σ)
      → ¬ σ ∈ er (eval_expr' χ_ok χ_er e)
      ∧ ∀ n σ',
          (σ, n, σ') ∈ ok (eval_expr' χ_ok χ_er e)
        → ∃ h', Q n h' ∧ join h' g (Δ', lift_heap σ').

  Lemma wp_hoare: ∀ {P e Q},
      P ⊢ (wp e Q) ↔ hoare P e Q.
  Proof.
    intros ???.
    split; intros H.
    - unfold hoare.
      intros ??? HP HJ.
      apply H in HP.
      unfold wp in HP.
      specialize (HP _ _ (conj (conj eq_refl eq_refl) HJ
                      : join (Δ', h) (Δ', g) (Δ', lift_heap σ))).
      split; [apply HP|].
      intros ?? Hn.
      pose proof (proj2 HP _ _ Hn) as ((?&h')&HQ&HJ').
      pose proof (proj1 HJ') as [H0 ?].
      pose proof (proj2 HJ') as H0'.
      simpl in H0, H0'.
      subst p.
      exists h'.
      easy.
    - unfold derivable, wp.
      intros (?&h) HP (?&g) ? HJ.
      pose proof proj1 HJ as [H0 H1]; simpl in H0, H1; subst p p0.
      unfold hoare in H.
      specialize (H _ _ _ HP (proj2 HJ)).
      split; [apply H|].
      intros ?? Hn.
      pose proof (proj2 H _ _ Hn) as [h' [HQ HJ']].
      exists (Δ', h').
      easy.
  Qed.

  Theorem hoare_conseq': ∀ {P P' Q e},
      P ⊢ P'
    → hoare P' e Q
    → hoare P e Q.
  Proof.
    intros.
    rewrite<- wp_hoare in H0.
    rewrite<- wp_hoare.
    eapply derivable_trans.
    apply H.
    exact H0.
  Qed.

  Theorem hoare_prop: ∀ {P e Q} {p: Prop},
      hoare ⦃ P * ⟨p⟩ ⦄ e Q
    ↔ (p → hoare P e Q).
  Proof.
    intros.
    rewrite<-! wp_hoare.
    exact derivable_prop_l.
  Qed.

  Theorem hoare_exist: ∀ {A} {P: A → assn ΣC} {e Q} {p: Prop},
      hoare ⦃ ∃ x, P x ⦄ e Q
    ↔ ∀ x, hoare (P x) e Q.
  Proof.
    intros.
    setoid_rewrite<- wp_hoare.
    exact derivable_exist_l.
  Qed.

  Theorem hoare_disj: ∀ {P Q R} {e},
    hoare ⦃ P ∨ R ⦄ e Q
  ↔ hoare P e Q ∧ hoare R e Q.
  Proof.
    intros.
    rewrite<-! wp_hoare.
    exact derivable_disj_l.
  Qed.

End hoare_expr.

Arguments hoare _ {ctx}.

Definition Hoare Δ P e Q := ∀ ctx, @hoare Δ ctx P e Q.

(* Derived Example. *)

Section hoare_cexpr.

  Variable Δ: prog_spec.
  Variable ctx: ProofContext Δ.

  Definition choare P ce Q := @hoare Δ ctx P (compile Z expr_sem ce) Q.

  Lemma hoare_frame_emp: ∀ {e P Q},
      @hoare Δ ctx aemp e Q
    → @hoare Δ ctx P e (λ v, (asepcon P (Q v))).
  Proof.
    intros.
    eapply hoare_conseq'.
    eapply derivable_trans.
    eapply (proj1 emp_sepcon_unit).
    eapply sepcon_comm.
    eapply hoare_conseq.
    intros; apply sepcon_comm.
    eapply hoare_frame.
    apply H.
  Qed.

  Lemma hoare_assume': ∀ {P e},
      @hoare Δ ctx P (EAssume e) (λ _, (asepcon P (aprop (e ≠ 0)))).
  Proof.
    intros.
    apply hoare_frame_emp.
    eapply hoare_assume.
  Qed.

  Lemma hoare_val': ∀ {P n},
      @hoare Δ ctx P (EVal n) (λ m, (asepcon P (aprop (n = m)))).
  Proof.
    intros.
    apply hoare_frame_emp.
    eapply hoare_val.
  Qed.

  Theorem hoare_comp': ∀ {op e₁ e₂ P},
      @hoare Δ ctx P (EComp op e₁ e₂) (λ n, (asepcon P (aprop ((eval_comp_op op) e₁ e₂ ∧ n = 1 ∨ (¬ (eval_comp_op op) e₁ e₂) ∧ n = 0)))).
  Proof.
    intros.
    apply hoare_frame_emp.
    eapply hoare_comp.
  Qed.

  Theorem hoare_skip': ∀ {P},
      @hoare Δ ctx P ESkip (λ _, P).
  Proof.
    intros.
    eapply hoare_conseq.
    intros. apply emp_sepcon_unit.
    apply hoare_frame_emp.
    apply hoare_skip.
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

