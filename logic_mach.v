(* Machine Code Logic. See Magnus O. Myreen,
   'Verified Just-In-Time Compiler on x86'. *)

Require Import Unicode.Utf8_core.
Require Import Lists.List. Import ListNotations.
Require Import ZArith.ZArith.
Require Import QArith.QArith.
Require Import Psatz.

Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import FP.SetsFixedpoints.

Require Import thesis.interval.
Require Import thesis.lang.
Require Import thesis.semantics.
Require Import thesis.sepalg.
Require Import thesis.logic_prelude.

Local Open Scope Z.
Local Open Scope sets.
Local Open Scope list.

Set Default Proof Using "Type".

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

  Variable Δ: prog_spec.
  Variable ctx: ProofContext Δ.

  #[local] Notation "'χ_ok'" := (ctx.(ctx_χ_ok Δ)).
  #[local] Notation "'χ_er'" := (ctx.(ctx_χ_er Δ)).
  #[local] Notation "'Δ''" := (ctx.(ctx_Δ' Δ)).
  #[local] Notation "'Hsub'" := (ctx.(ctx_Hsub Δ)).
  #[local] Notation "'HΔ'" := (ctx.(ctx_HΔ Δ)).

  Definition hoare_final (P Q: assn ΣA) :=
    ∀ h g σ,
       P (Δ', h) → join h g (lift_LΣ σ)
     → ¬ σ ∈ eval_mach_er χ_ok χ_er
     ∧ ∀ σ',
         (σ, σ') ∈ eval_mach_ok χ_ok
       → ∃ h', Q (Δ', h') ∧ join h' g (lift_LΣ σ').

  Definition hoare (P Q: assn ΣA) :=
    ∀ h g σ σ₁ (x: steps χ_ok σ σ₁),
      P (Δ', h) → join h g (lift_LΣ σ)
    → abort χ_er σ₁ ∨ final σ₁
    → ∃ h' σ',
        nontrivial_split x σ'
      ∧ Q (Δ', h') ∧ join h' g (lift_LΣ σ').

  (* Inductive hoare_sb A (Φ Ψ: A → assn ΣA): assn ΣA → assn ΣA → Prop := *)
  (*   HoareSB: ∀ P Q, hoare P ⦃ Q ∨ ∃ a, Φ a * ⟨Ψ a ⟛ Q ∨ hoare_sb A Φ Ψ (Ψ a) Q⟩ ⦄ *)
  (*                   → hoare_sb A Φ Ψ P Q. *)

  Definition hoare_code_final P c Q :=
    ∀ q, hoare_final ⦃ P * ⌈⌈↦c[q] c⌉⌉ ⦄ ⦃ Q * ⌈⌈↦c[q] c⌉⌉ ⦄.

  Definition hoare_code P c Q :=
    ∀ q, hoare ⦃ P * ⌈⌈↦c[q] c⌉⌉ ⦄ ⦃ Q * ⌈⌈↦c[q] c⌉⌉ ⦄.

  Theorem hoare_seq: ∀ {P Q R},
      hoare P Q → hoare Q R
    → hoare P R.
  Proof.
    intros ??? H1 H2.
    unfold hoare.
    intros ????? HP HJ Hend.
    specialize (H1 _ _ _ _ x HP HJ Hend).
    destruct H1 as (h₂&σ₂&Hsplt&HQ&HJ').
    unfold nontrivial_split in Hsplt.
    destruct Hsplt as (σ₃&H3&y&z&Happ).
    specialize (H2 _ _ _ _ z HQ HJ' Hend).
    destruct H2 as (h'&σ'&Hsplt'&HR&HJ'').
    exists h', σ'.
    split; [|tauto].
    rewrite Happ.
    apply nontrivial_cons.
    apply nontrivial_app.
    exact Hsplt'.
  Qed.

  Theorem hoare_frame: ∀ {P Q R},
      hoare P Q
    → hoare ⦃ P * R ⦄ ⦃ Q * R ⦄.
  Proof.
    intros ??? H.
    unfold hoare in H |- *.
    intros ????? HPR HJσ Hend.
    pose proof destruct_sepcon_liftΣ HPR as (h₁&h₂&HP&HR&HJ').
    pose proof MSA_assoc HJ' HJσ as [h₃ [H1 H2]].
    specialize (H _ _ _ _ x HP H2 Hend) as (h'&σ'&HS&HQ&HJ'').
    apply MSA_comm in HJ'', H1.
    pose proof MSA_assoc H1 HJ'' as [h₄ H3].
    exists h₄ ,σ'.
    pose proof (MSA_comm (proj1 H3)).
    pose proof (MSA_comm (proj2 H3)).
    clear Hend.
    intuition.
    unfold asepcon.
    exists (Δ', h'), (Δ', h₂).
    intuition.
    split; simpl; auto.
  Qed.

  Theorem hoare_conseq: ∀ {P Q Q'},
      Q' ⊢ Q
    → hoare P Q'
    → hoare P Q.
  Proof.
    intros ??? H1 H.
    unfold hoare.
    intros ????? HP HJ HE.
    specialize (H _ _ _ _ x HP HJ HE) as (?&?&?).
    exists x0, x1.
    intuition.
  Qed.

  Definition wp (Q: assn ΣA): assn ΣA :=
    ⦃ ∃ P, P * ⟨hoare P Q⟩ ⦄.

  Lemma wp_hoare: ∀ {P Q},
      P ⊢ (wp Q) ↔ hoare P Q.
  Proof.
    unfold wp.
    intros ??.
    split; intros H.
    - unfold hoare.
      intros ????? HP HJ.
      apply H in HP.
      unfold aex, asepcon, aprop in HP.
      destruct HP as (R&σ₂&?&HJ'&HR&H1&Hemp).
      apply MSA_comm in HJ'.
      pose proof MSA_join_empty HJ' Hemp.
      subst σ₂.
      eapply H1; eauto.
    - assert (P ⊢ ⦃ P * ⟨hoare P Q⟩ ⦄).
      + unfold derivable.
        intros ? H1.
        unfold asepcon, aprop.
        pose proof MSA_unit σ as [u X].
        pose proof MSA_unit_empty X.
        apply MSA_comm in X.
        exists σ, u.
        tauto.
      + eapply derivable_trans; [apply H0|].
        apply (@derivable_exist_r _ _ _ (λ P, ⦃ P * ⟨ hoare P Q ⟩ ⦄) P).
  Qed.

  Theorem hoare_conseq': ∀ {P P' Q},
      P ⊢ P'
    → hoare P' Q
    → hoare P Q.
  Proof.
    intros.
    rewrite<- wp_hoare in H0.
    rewrite<- wp_hoare.
    eapply derivable_trans.
    apply H.
    exact H0.
  Qed.

  Theorem hoare_prop: ∀ {P Q} {p: Prop},
      hoare ⦃ P * ⟨p⟩ ⦄ Q
    ↔ (p → hoare P Q).
  Proof.
    intros.
    rewrite<-! wp_hoare.
    exact derivable_prop_l.
  Qed.

  Theorem hoare_exist: ∀ {A} {P: A → assn ΣA} {Q},
      hoare ⦃ ∃ x, P x ⦄ Q
    ↔ ∀ x, hoare (P x) Q.
  Proof.
    intros.
    setoid_rewrite<- wp_hoare.
    exact derivable_exist_l.
  Qed.

  Theorem hoare_disj: ∀ {P Q R},
    hoare ⦃ P ∨ R ⦄ Q
  ↔ hoare P Q ∧ hoare R Q.
  Proof.
    intros.
    rewrite<-! wp_hoare.
    exact derivable_disj_l.
  Qed.

  (* Lemma sepcon_store_code_union: ∀ {q c e}, *)
      (* ⦃ [⌈code[q] c⌉] * [⌈code[q] e⌉] ⦄ *)
      (* ⦃ [⌈code[q] c⌉] * [⌈code[q] e⌉] ⦄. *)

  (* Theorem hoare_extend: ∀ {. *)

  Fact Q_split: ∀ q, (q/2 + q/2 == q)%Q.
  Proof.
    intros.
    assert (∀ p, p + p == 2 * p)%Q.
    { intros p; psatz Q. }
    specialize (H (q/2)%Q).
    rewrite H.
    apply Qmult_div_r.
    psatz Q.
  Qed.

  Lemma I_split: ∀ q, ∃ p, Iadd p p q.
  Proof.
    intros.
    invI q.
    pose proof I_toH x.
    pose proof (Q_split (I_toQ x)).
    assert (0 < (I_toQ x) / 2 <= 1)%Q by psatz Q.
    exists (liftI (exist _ (I_toQ x / 2)%Q H1)).
    apply IaddE.
    simpl.
    assumption.
  Qed.

  Theorem hoare_self: ∀ {P Q c},
      (∀ q, hoare_code ⦃ P * ⌈⌈↦c[q] c⌉⌉ ⦄ c ⦃ Q * ⌈⌈↦c[q] c⌉⌉ ⦄)
    → hoare_code P c Q.
  Proof.
    intros ??? H.
    unfold hoare_code.
    intros q.
    unfold hoare_code in H.
    pose proof (I_split q) as [p Hp].
    specialize (H p p).
    eapply hoare_conseq; [|eapply hoare_conseq'].
    3: { apply H. }
    - deriv_step @sepcon_assoc.
      eapply @sepcon_mono_r.
      deriv_step @lift_assn_prod_sepcon_distr.
      deriv_step @lift_assn_prod_mono.
      apply lift_assn_prod_sepcon_distr.
      eapply lift_assn_prod_mono.
      eapply lift_assn_prod_mono.
      apply (store_code_q_split Hp).
    - deriv_step @sepcon_mono_r.
      deriv_step @lift_assn_prod_mono.
      eapply lift_assn_prod_mono.
      eapply (store_code_q_split Hp).
      deriv_step @lift_assn_prod_mono.
      apply lift_assn_prod_sepcon_distr.
      apply lift_assn_prod_sepcon_distr.
      apply sepcon_assoc.
  Qed.

  Theorem hoare_inv: ∀ {I Q},
      hoare I ⦃ I ∨ Q ⦄ → hoare I Q.
  Proof.
    unfold hoare.
    intros ?? H.
    intros ?????.
    revert h g.
    induction σ, σ₁, x using (steps_ind_by_len _).
    intros ?? HI HJ Hend.
    specialize (H _ _ _ _ x HI HJ Hend).
    destruct H as (h₁&σ₁&Hsplt&HIQ&HJ').
    destruct HIQ.
    - unfold nontrivial_split in Hsplt.
      destruct Hsplt as (σ₂&Hstep&y&z&Hx).
      assert (steps_len z < steps_len x)%nat as Hlt.
      { rewrite Hx.
        simpl.
        pose proof steps_app_len y z.
        lia. }
      specialize (H0 _ _ _ Hlt _ _ H HJ' Hend).
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

  Theorem hoare_const: ∀ {r n i},
      hoare_code ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ -⌉ ⦄
                       [(i, IConst n r)]
                       ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ n⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_nop: ∀ {i},
      hoare_code ⦃ ⌈PC r↦ i⌉ ⦄
                       [(i, INop)]
                       ⦃ ⌈PC r↦ ⦅i + 1⦆⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_jmp_jump: ∀ {i r x n},
      x > 0
    → hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ x⌉ ⦄
        [(i, IJmp r n)]
        ⦃ ⌈PC r↦ ⦅i + n⦆⌉ * ⌈r r↦ x⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_jmp_next: ∀ {i r x n},
      x <= 0
    → hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ x⌉ ⦄
        [(i, IJmp r n)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ x⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_arith_two: ∀ {i op r₁ r₂ n m},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r₁ r↦ m⌉ * ⌈r₂ r↦ n⌉ ⦄
        [(i, IArith op r₁ r₂)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r₁ r↦ m⌉ * ⌈r₂ r↦ eval_arith_op op n m⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_arith_one: ∀ {i op r n},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ n⌉ ⦄
        [(i, IArith op r r)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ eval_arith_op op n n⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_load_two: ∀ {i r₁ r₂ a n q},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r₁ r↦ a⌉ * ⌈r₂ r↦ -⌉ * ⌈⌈a ↦[q] n⌉⌉ ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r₁ r↦ a⌉ * ⌈r₂ r↦ n⌉ * ⌈⌈a ↦[q] n⌉⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_load_one: ∀ {i r a n q},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ a⌉ * ⌈⌈a ↦[q] n⌉⌉ ⦄
        [(i, ILoad r r)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ n⌉ * ⌈⌈a ↦[q] n⌉⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_store_two: ∀ {i r₁ r₂ a n},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r₁ r↦ n⌉ * ⌈r₂ r↦ a⌉ * ⌈⌈a ↦ -⌉⌉ ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r₁ r↦ n⌉ * ⌈r₂ r↦ a⌉ * ⌈⌈a ↦ n⌉⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_store_one: ∀ {i r a},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ a⌉ * ⌈⌈a ↦ -⌉⌉ ⦄
        [(i, ILoad r r)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ a⌉ * ⌈⌈a ↦ a⌉⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_load_stack_two: ∀ {i r₁ r₂ a n},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r₁ r↦ a⌉ * ⌈r₂ r↦ -⌉ * ⌈a s↦ n⌉ ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r₁ r↦ a⌉ * ⌈r₂ r↦ n⌉ * ⌈a s↦ n⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_load_stack_one: ∀ {i r a n},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ a⌉ * ⌈a s↦ n⌉ ⦄
        [(i, ILoad r r)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ n⌉ * ⌈a s↦ n⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_store_stack_two: ∀ {i r₁ r₂ a n},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r₁ r↦ n⌉ * ⌈r₂ r↦ a⌉ * ⌈a s↦ -⌉ ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r₁ r↦ n⌉ * ⌈r₂ r↦ a⌉ * ⌈a s↦ n⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_store_stack_one: ∀ {i r a},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ a⌉ * ⌈a s↦ -⌉ ⦄
        [(i, ILoad r r)]
        ⦃ ⌈PC r↦ ⦅i + 3⦆⌉ * ⌈r r↦ a⌉ * ⌈a s↦ a⌉ ⦄.
  Proof. Admitted.

  Theorem hoare_call_mach: ∀ {i r p Φ Ψ P},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ p⌉ * (⌈PC r↦ p⌉ * ⌈r r↦ p⌉ -* P * ⟦Φ⟧)
        * 𝔐 {{{Φ}}} {{{Ψ}}} ⦄
        [(i, ICall r)]
        ⦃ ⌈PC r↦ ⦅i + 2⦆⌉ * P * (∃ p', ⌈PC r↦ p'⌉ -* ⟦Ψ⟧) ⦄.
  Proof. Admitted.

  Theorem hoare_call_fun: ∀ {i r a Φ Ψ P l vs},
      hoare_code
        ⦃ ⌈PC r↦ i⌉ * ⌈r r↦ a⌉ * (⌈r r↦ a⌉ -* P * ⌈prologue l vs⌉ * ⇑⟦Φ vs⟧)
        * ⇑(𝔉 {{{Φ}}} a {{{Ψ}}}) ⦄
        [(i, ICall r)]
        ⦃ ∃ n, ⌈PC r↦ ⦅i + 2⦆⌉ * P * ⌈epilogue l n⌉ * ⇑⟦Ψ vs n⟧ ⦄.
    Proof. Admitted.

End hoare_mach.

Arguments hoare _ {ctx}.
Arguments hoare_final _ {ctx}.

Definition HoareFinal Δ P Q := ∀ ctx, @hoare_final Δ ctx P Q.

(* Machine Code Logic End. *)
