(* Machine Code Logic. See Magnus O. Myreen,
   'Verified Just-In-Time Compiler on x86'. *)

Require Import Unicode.Utf8_core.
Require Import Lists.List. Import ListNotations.
Require Import ZArith.ZArith.

Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import FP.SetsFixedpoints.

(* Require Import thesis.interval. *)
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

  Definition hoare (P Q: assn ΣA) :=
    ∀ h g σ,
       P (Δ', h) → join h g (lift_LΣ σ)
     → ¬ σ ∈ eval_mach_er χ_ok χ_er
     ∧ ∀ σ',
         (σ, σ') ∈ eval_mach_ok χ_ok
       → ∃ h', Q (Δ', h') ∧ join h' g (lift_LΣ σ').

  Definition hoare_steps (P Q: assn ΣA) :=
    ∀ h g σ σ₁ (x: steps χ_ok σ σ₁),
      P (Δ', h) → join h g (lift_LΣ σ)
    → abort χ_er σ₁ ∨ final σ₁
    → ∃ h' σ',
        nontrivial_split x σ'
      ∧ Q (Δ', h') ∧ join h' g (lift_LΣ σ').

  Definition hoare_code P c Q :=
    ∀ q, hoare ⦃ P * [⌈c↦[q] c⌉] ⦄ ⦃ Q * [⌈c↦[q] c⌉] ⦄.

  Definition hoare_code_steps P c Q :=
    ∀ q, hoare_steps ⦃ P * [⌈c↦[q] c⌉] ⦄ ⦃ Q * [⌈c↦[q] c⌉] ⦄.

  Theorem hoare_seq: ∀ {P Q R},
      hoare_steps P Q → hoare_steps Q R
    → hoare_steps P R.
  Proof.
    intros ??? H1 H2.
    unfold hoare_steps.
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
      hoare_steps P Q
    → hoare_steps ⦃ P * R ⦄ ⦃ Q * R ⦄.
  Proof.
    intros ??? H.
    unfold hoare_steps in H |- *.
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

  Theorem hoare_conseq: ∀ {P P' Q' Q},
      P ⊢ P'
    → Q' ⊢ Q
    → hoare_steps P' Q'
    → hoare_steps P Q.
  Proof.
    intros ???? H1 H2 H.
    unfold hoare_steps in H |- *.
    intros ????? HP HJ Hend.
    specialize (H _ _ _ _ x (H1 _ HP) HJ Hend)as (?&?&?&HQ&?).
    eexists; eexists; intuition eauto.
  Qed.

  (* Theorem hoare_prop: ∀ {}. *)

  (* Theorem hoare_exist:. *)

  (* Theorem hoare_disj:. *)

  (* Lemma sepcon_store_code_union: ∀ {q c e}, *)
      (* ⦃ [⌈code[q] c⌉] * [⌈code[q] e⌉] ⦄ *)
      (* ⦃ [⌈code[q] c⌉] * [⌈code[q] e⌉] ⦄. *)

  (* Theorem hoare_extend: ∀ {. *)

  

  Theorem hoare_self: ∀ {P Q c},
      (∀ q, hoare_code_steps ⦃ P * [⌈c↦[q] c⌉] ⦄ c ⦃ Q * [⌈c↦[q] c⌉] ⦄)
    → hoare_code_steps P c Q.
  Proof.
    intros ??? H.
    unfold hoare_code_steps.
    intros q.
    unfold hoare_code_steps in H.

  Theorem hoare_inv: ∀ {I Q},
      hoare_steps I ⦃ I ∨ Q ⦄ → hoare_steps I Q.
  Proof.
    unfold hoare_steps.
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
      hoare_code_steps ⦃ [PC r↦ i] * [r r↦ -] ⦄
                       [(i, IConst n r)]
                       ⦃ [PC r↦ ⦅i + 3⦆] * [r r↦ n] ⦄.
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
      hoare_code_steps ⦃ [PC r↦ i] ⦄
                       [(i, INop)]
                       ⦃ [PC r↦ ⦅i + 1⦆] ⦄.
  Proof. Admitted.

  Theorem hoare_jmp_jump: ∀ {i r x n},
      x > 0
    → hoare_code_steps
        ⦃ [PC r↦ i] * [r r↦ x] ⦄
        [(i, IJmp r n)]
        ⦃ [PC r↦ ⦅i + n⦆] * [r r↦ x] ⦄.
  Proof. Admitted.

  Theorem hoare_jmp_next: ∀ {i r x n},
      x <= 0
    → hoare_code_steps
        ⦃ [PC r↦ i] * [r r↦ x] ⦄
        [(i, IJmp r n)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [r r↦ x] ⦄.
  Proof. Admitted.

  Theorem hoare_arith_two: ∀ {i op r₁ r₂ n m},
      hoare_code_steps
        ⦃ [PC r↦ i] * [r₁ r↦ m] * [r₂ r↦ n] ⦄
        [(i, IArith op r₁ r₂)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [r₁ r↦ m] * [r₂ r↦ ⦅(eval_arith_op op) n m⦆] ⦄.
  Proof. Admitted.

  Theorem hoare_arith_one: ∀ {i op r n},
      hoare_code_steps
        ⦃ [PC r↦ i] * [r r↦ n] ⦄
        [(i, IArith op r r)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [r r↦ ⦅(eval_arith_op op) n n⦆] ⦄.
  Proof. Admitted.

  Theorem hoare_load_two: ∀ {i r₁ r₂ a n q},
      hoare_code_steps
        ⦃ [PC r↦ i] * [⌈a ↦[q] n⌉] * [r₁ r↦ a] * [r₂ r↦ -] ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [⌈a ↦[q] n⌉] * [r₁ r↦ a] * [r₂ r↦ n] ⦄.
  Proof. Admitted.

  Theorem hoare_load_one: ∀ {i r a n q},
      hoare_code_steps
        ⦃ [PC r↦ i] * [⌈a ↦[q] n⌉] * [r r↦ a] ⦄
        [(i, ILoad r r)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [⌈a ↦[q] n⌉] * [r r↦ n] ⦄.
  Proof. Admitted.

  Theorem hoare_store_two: ∀ {i r₁ r₂ a n},
      hoare_code_steps
        ⦃ [PC r↦ i] * [⌈a ↦ -⌉] * [r₁ r↦ n] * [r₂ r↦ a] ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [⌈a ↦ n⌉] * [r₁ r↦ n] * [r₂ r↦ a] ⦄.
  Proof. Admitted.

  Theorem hoare_store_one: ∀ {i r a},
      hoare_code_steps
        ⦃ [PC r↦ i] * [⌈a ↦ -⌉] * [r r↦ a] ⦄
        [(i, ILoad r r)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [⌈a ↦ a⌉] * [r r↦ a] ⦄.
  Proof. Admitted.

  Theorem hoare_load_stack_two: ∀ {i r₁ r₂ a n},
      hoare_code_steps
        ⦃ [PC r↦ i] * [a s↦ n] * [r₁ r↦ a] * [r₂ r↦ -] ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [a s↦ n] * [r₁ r↦ a] * [r₂ r↦ n] ⦄.
  Proof. Admitted.

  Theorem hoare_load_stack_one: ∀ {i r a n},
      hoare_code_steps
        ⦃ [PC r↦ i] * [a s↦ n] * [r r↦ a] ⦄
        [(i, ILoad r r)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [a s↦ n] * [r r↦ n] ⦄.
  Proof. Admitted.

  Theorem hoare_store_stack_two: ∀ {i r₁ r₂ a n},
      hoare_code_steps
        ⦃ [PC r↦ i] * [a s↦ -] * [r₁ r↦ n] * [r₂ r↦ a] ⦄
        [(i, ILoad r₁ r₂)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [a s↦ n] * [r₁ r↦ n] * [r₂ r↦ a] ⦄.
  Proof. Admitted.

  Theorem hoare_store_stack_one: ∀ {i r a},
      hoare_code_steps
        ⦃ [PC r↦ i] * [a s↦ -] * [r r↦ a] ⦄
        [(i, ILoad r r)]
        ⦃ [PC r↦ ⦅i + 3⦆] * [a s↦ a] * [r r↦ a] ⦄.
  Proof. Admitted.

  Theorem hoare_call_mach: ∀ {i r p Φ Ψ' Ψ P F},
      ⦃ P * [PC r↦ p] * [r r↦ p] ⦄ ⊢ ⦃ F * ⟦Φ⟧ ⦄
    → ⟦Ψ⟧ ⊢ ⦃ [PC r↦ -] * Ψ' ⦄
    → hoare_code_steps
        ⦃ 𝔐 {{{Φ}}} {{{Ψ}}} * P * [PC r↦ i] * [r r↦ p] ⦄
        [(i, ICall r)]
        ⦃ F * [PC r↦ ⦅i + 2⦆] * Ψ' ⦄.
  Proof. Admitted.

End hoare_mach.

Arguments hoare _ {ctx}.

Definition Hoare Δ P Q := ∀ ctx, @hoare Δ ctx P Q.

(* Machine Code Logic End. *)
