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
Require Import thesis.logic_prelude.
Require thesis.logic_fun.
Require thesis.logic_mach.

Module F := logic_fun.
Module M := logic_mach.

Local Open Scope Z.
Local Open Scope sets.
Local Open Scope list.

Definition provable_fun (Δ: prog_spec) (p: prog) :=
  ∀ f e Φ Ψ vs,
    In (f, e) p → (f, FunSpec Φ Ψ) ∈ fst Δ
  → F.Hoare Δ (eval_assn (Φ vs)) (e Z expr_sem vs) (λ n, eval_assn (Ψ vs n)).

Definition provable_mach (Δ: prog_spec) :=
  ∀ Φ Ψ,
    MachSpec Φ Ψ ∈ snd Δ
  → M.Hoare Δ (eval_assn Φ) (eval_assn Ψ).

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
      unfold F.Hoare, F.hoare in Hfs.
      pose (mkProofContext Δ χ_ok χ_er Δ spec_include_refl H) as ctx.
      specialize (Hfs ctx _ _ _ HP HJ).
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
      unfold M.Hoare, M.hoare in Hfs.
      pose (mkProofContext Δ χ_ok χ_er Δ spec_include_refl H) as ctx.
      specialize (Hfs ctx _ _ _ HP HJ).
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
      unfold F.Hoare, F.hoare in Hfs.
      pose (mkProofContext Δ χ_ok χ_er Δ spec_include_refl H) as ctx.
      specialize (Hfs ctx _ _ _ HP HJ).
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
      unfold M.Hoare, M.hoare in Hfs.
      pose (mkProofContext Δ χ_ok χ_er Δ spec_include_refl H) as ctx.
      specialize (Hfs ctx _ _ _ HP HJ).
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

(* TODO: proof theory: composability *)
