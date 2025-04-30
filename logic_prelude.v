Require Import Unicode.Utf8_core.
Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
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
Notation "f a" := (f a) (in custom Assn at level 0, a at level 0). (* ok? *)
(* Notation "⦅ x ⦆" := x (in custom Assn, x constr). *)

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
  | n :: l' => asepcon (astore_int_q a q n) (astore_array_q (a + 1) q l')
  end.

Definition astore_array a l := astore_array_q a I1 l.

Definition astore_ins_q a q i: assn fic_heap :=
  astore_array_q a q (encode i).

Fixpoint astore_code_q q (c: code): assn fic_heap :=
  match c with
  | [] => aemp
  | (a, i) :: c' => asepcon (astore_ins_q a q i) (astore_code_q q c')
  end.

Definition astore_code c := astore_code_q I1 c.

Notation "'c↦' [ q ] c" := (astore_code_q q c) (in custom assn at level 50, q constr).
Notation "'c↦' c" := (astore_code c) (in custom assn at level 50).

Definition lift_assn_heap_ΣA_base (P: assn fic_heap): assn fic_LΣ :=
  λ σ, MSA_empty (rg σ) ∧ MSA_empty (st σ) ∧ P (hp σ).

Notation "⌈ P ⌉" := (lift_assn_heap_ΣA_base P) (in custom assn, P at level 100).

Definition areg_int (r: reg) (n: Z): assn fic_LΣ :=
  λ σ, rg σ r = Some n ∧ (∀ r', r ≠ r' → rg σ r' = None)
       ∧ MSA_empty (st σ) ∧ MSA_empty (hp σ).

Definition areg_any r := aex (λ n, areg_int r n).

Definition astack_int (a n: Z): assn fic_LΣ :=
  λ σ, st σ a = Some n ∧ (∀ a', a ≠ a' → st σ a' = None)
       ∧ MSA_empty (rg σ) ∧ MSA_empty (hp σ).

Definition astack_any a := aex (λ n, astack_int a n).

Notation "a r↦ v" := (areg_int a v) (in custom assn at level 50).
Notation "a r↦ -" := (areg_any a) (in custom assn at level 50).
Notation "a s↦ v" := (astack_int a v) (in custom assn at level 50).
Notation "a s↦ -" := (astack_any a) (in custom assn at level 50).

Definition amach_spec_mach (H: mach_spec): assn ΣA :=
  λ σ, H ∈ snd (spec σ) ∧ MSA_empty (low σ).

Notation "'𝔐' {{{ Φ }}} {{{ Ψ }}}" := (amach_spec_mach (MachSpec Φ Ψ)) (in custom assn at level 50).

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

