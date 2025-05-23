Require Import Unicode.Utf8_core.
Require Import Strings.String.
Require Import ZArith.ZArith.
Require Import Lia.

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
      + unfold astore_fun.
        exists f.
        apply lift_heap_fun in H0.
        pose proof (MSA_positive' (HJ n) (fun_empty H0)).
        simpl.
        rewrite (proj1 H).
        apply Hsub in HH.
        tauto.
      + apply HJ.
  Qed.

  Theorem hoare_call_fun: ∀ {l Φ Ψ vs},
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
    pose proof MSA_join_empty HJ' (proj2 Hemp) as H1.
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

  Theorem hoare_call_mach: ∀ {l vs Φ Ψ},
      hoare ⦃ ⇓⟦Φ vs⟧ * (∀ a, 𝔐 {{{ ⌈PC r↦ l⌉ * ⌈prologue a vs⌉ * Φ vs }}}
                                {{{ ∃ n, ⌈PC r↦ -⌉ * ⌈epilogue a n⌉ * Ψ vs n }}}) ⦄
            (ECall l vs)
            (λ n, ⦃ ⇓⟦Ψ vs n⟧ ⦄).
  Proof. Admitted.

  Theorem hoare_store: ∀ {l v},
      hoare ⦃ ⌈l ↦ -⌉ ⦄
            (EStore l v)
            (λ _, ⦃ ⌈l ↦ v⌉ ⦄).
  Proof.
    intros ??.
    unfold hoare.
    intros ??? [_ HP] HJ.
    unfold astore_uninit in HP; simpl in HP.
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
      + unfold lift_assn_prod, astore_int_q.
        simpl.
        split; [tauto|split].
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
      hoare ⦃ ⌈l ↦[q] v⌉ ⦄
            (ELoad l)
            (λ n, ⦃ ⌈l ↦[q] v⌉ * ⟨n = v⟩ ⦄).
  Proof.
    intros ???.
    unfold hoare.
    intros ??? [_ HP] HJ.
    unfold astore_int_q in HP.
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
      unfold lift_assn_prod, astore_int_q.
      simpl snd in HP |- *.
      unfold aprop.
      rewrite (proj1 (proj2 lift_heap_int H)) in Hn; injection Hn as Hn.
      easy.
  Qed.

  Theorem hoare_alloc: ∀ {n},
      n >= 0
    → hoare ⦃ emp ⦄
            (EAlloc n)
            (λ a, ⦃ ⌈a ↦.. n×-⌉ ⦄).
  Proof.
    intros ? Hpos.
    unfold hoare.
    intros ??? HP HJ.
    split.
    - simpl; sets_unfold.
      lia.
    - intros a ? Hn.
      simpl in Hn; sets_unfold in Hn.
      destruct Hn as [_ [Hin Hout]].
      exists (λ l, if a <=? l then if l <? a + n then CFUndef else h l else h l).
      split.
      + unfold lift_assn_prod, astore_uninit_array.
        simpl.
        split; [tauto|split;[tauto|split]].
        * intros ? HIN.
          specialize (Hin _ HIN).
          rewrite (proj2 (Z.leb_le _ _) (proj1 HIN)).
          rewrite (proj2 (Z.ltb_lt _ _) (proj2 HIN)).
          unfold frag_writable; tauto.
        * intros ? HOUT.
          specialize (Hout _ HOUT).
          destruct HOUT as [HOUT|HOUT].
          { assert (¬ a <= l) by lia.
            apply Z.leb_nle in H.
            rewrite H.
            apply HP. }
          { assert (¬ l < a + n) by lia.
            apply Z.ltb_nlt in H.
            rewrite H.
            destruct (a <=? l); apply HP. }
      + intros l.
        destruct (Z.le_decidable a l).
        * rewrite (proj2 (Z.leb_le _ _) H).
          destruct (Z.lt_decidable l (a + n)).
          { rewrite (proj2 (Z.ltb_lt _ _) H0).
            rewrite (proj1 lift_heap_undef (proj2 (Hin _ (conj H H0)))).
            specialize (HJ l).
            rewrite (proj1 lift_heap_emp (proj1 (Hin _ (conj H H0)))) in HJ.
            pose proof MSA_positive' HJ (emp_empty eq_refl).
            rewrite (proj2 H1).
            constructor. }
          { rewrite (proj2 (Z.ltb_nlt _ _) H0).
            assert (l < a ∨ l >= a + n) by lia.
            rewrite<- (proj1 lift_heap_eq (Hout _ H1)).
            apply HJ. }
        * rewrite (proj2 (Z.leb_nle _ _) H).
          assert (l < a ∨ l >= a + n) by lia.
          rewrite<- (proj1 lift_heap_eq (Hout _ H0)).
          apply HJ.
  Qed.

  Theorem hoare_dealloc: ∀ {a n},
      hoare ⦃ ⌈a ↦.. n×-⌉ ⦄
            (EDealloc a n)
            (λ _, ⦃ emp ⦄).
  Proof.
    intros ??.
    unfold hoare.
    intros ??? [_ HP] HJ.
    unfold astore_uninit_array in HP.
    destruct HP as [Hpos[Hin Hout]].
    split.
    - simpl; sets_unfold.
      intros [H|[l H]].
      + lia.
      + specialize (Hin _ (proj1 H)).
        pose proof join_writable (HJ _) Hin.
        simpl snd in Hin; rewrite (proj2 H0) in Hin.
        apply lift_heap_writable in Hin.
        tauto.
    - intros m ? Hn.
      simpl in Hn; sets_unfold in Hn.
      exists (λ l, if a <=? l then if l <? a + n then CFEmp else h l else h l).
      split.
      + unfold aemp.
        split; [simpl;tauto|].
        intros l; simpl snd.
        destruct (Z.le_decidable a l).
        * rewrite (proj2 (Z.leb_le _ _) H).
          destruct (Z.lt_decidable l (a + n)).
          { rewrite (proj2 (Z.ltb_lt _ _) H0).
            constructor. }
          { rewrite (proj2 (Z.ltb_nlt _ _) H0).
            assert (l < a ∨ l >= a + n) by lia.
            apply (Hout _ H1). }
        * rewrite (proj2 (Z.leb_nle _ _) H).
          assert (l < a ∨ l >= a + n) by lia.
          apply (Hout _ H0).
      + intros l.
        destruct (Z.le_decidable a l).
        * rewrite (proj2 (Z.leb_le _ _) H).
          destruct (Z.lt_decidable l (a + n)).
          { rewrite (proj2 (Z.ltb_lt _ _) H0).
            pose proof (Hin _ (conj H H0)).
            pose proof (join_writable (HJ _) H1).
            rewrite (proj1 H2).
            rewrite (proj1 lift_heap_emp (proj2 (proj1 (proj2 Hn) l (ltac:(lia))))).
            constructor. }
          { rewrite (proj2 (Z.ltb_nlt _ _) H0).
            assert (l < a ∨ l >= a + n) by lia.
            rewrite<- (proj1 lift_heap_eq (proj2 (proj2 Hn) _ H1)).
            apply HJ. }
        * rewrite (proj2 (Z.leb_nle _ _) H).
          assert (l < a ∨ l >= a + n) by lia.
          rewrite<- (proj1 lift_heap_eq (proj2 (proj2 Hn) _ H0)).
          apply HJ.
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
    ⦃ ∃ P, P * ⟨hoare P e Q⟩ ⦄.

  Lemma wp_hoare: ∀ {P e Q},
      P ⊢ (wp e Q) ↔ hoare P e Q.
  Proof.
    unfold wp.
    intros ???.
    split; intros H.
    - unfold hoare.
      intros ??? HP HJ.
      apply H in HP.
      unfold aex, asepcon, aprop in HP.
      destruct HP as (R&σ₁&σ₂&HJ'&HR&H1&Hemp).
      apply MSA_comm in HJ'.
      pose proof MSA_join_empty HJ' Hemp.
      subst σ₁.
      eapply H1; eauto.
    - assert (P ⊢ ⦃ P * ⟨hoare P e Q⟩ ⦄).
      + unfold derivable.
        intros ? H1.
        unfold asepcon, aprop.
        pose proof MSA_unit σ as [u X].
        pose proof MSA_unit_empty X.
        apply MSA_comm in X.
        exists σ, u.
        tauto.
      + eapply derivable_trans; [apply H0|].
        apply (@derivable_exist_r _ _ _ (λ P, ⦃ P * ⟨ hoare P e Q ⟩ ⦄) P).
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

  Theorem hoare_exist: ∀ {A} {P: A → assn ΣC} {e Q},
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

Ltac hoare_pre X := (eapply hoare_conseq'; [eapply X|]).
Ltac hoare_post X := (eapply hoare_conseq; [intros ?; eapply X|]).
(* Ltac hoare_exec X := *)
(*   ((((eapply hoare_frame_l) + *)
(*      (hoare_pre @sepcon_add_unit; eapply hoare_frame_l)); *)
(*     eapply X) + *)
(*   ((eapply hoare_conseq; [|(((eapply hoare_frame_l) + (hoare_pre @sepcon_add_unit; eapply hoare_frame_l)); eapply X)]); intros; simpl)). *)

Arguments hoare _ {ctx}.

Definition Hoare Δ P e Q := ∀ ctx, @hoare Δ ctx P e Q.

