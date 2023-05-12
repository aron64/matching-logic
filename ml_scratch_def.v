
Inductive EV : Set :=
| x
| y
| z
.

Inductive SV : Set :=
| X
| Y
| Z
.

Inductive Σ : Set :=
| σ₁
| σ₂
| σ₃
.

Inductive φ : Type :=
| χ (e : EV)
| Χ (s : SV)
| σ (σₓ : Σ)
| App (φ₁ φ₂ : φ)
| Btm 
| Arr (φ₁ φ₂ : φ)
| E (χφ₁ : (EV -> φ))
| mu (Χφ₁ : (SV -> φ))
.

Print φ.
Fail Goal Χ = X.


Notation "⊥" := Btm.

(* it sounds like a better practice to use definitions instead of notating only, so unfold works *)

Definition MLarr (φ₁ φ₂ : φ) := Arr φ₁ φ₂.
Notation "φ₁ → φ₂" := (MLarr φ₁ φ₂) (at level 1, left associativity).

Definition MLneg (φ₁ : φ) := φ₁ → ⊥.
Notation "¬ φ₁" := (MLneg φ₁) (at level 10).


Definition MLor (φ₁ φ₂ : φ) := ((¬φ₁) → φ₂).
Notation "φ₁ ∨ φ₂" := (MLor φ₁ φ₂) (at level 50).

Definition MLand (φ₁ φ₂ : φ) := (¬(¬φ₁ ∨ ¬φ₂)).
Notation "φ₁ ∧ φ₂" := (MLand φ₁ φ₂) (at level 50).

Definition MLequiv (φ₁ φ₂ : φ) := ((φ₁ → φ₂) ∧ (φ₂ → φ₁)).
Notation "φ₁ ⇔ φ₂" := (MLequiv φ₁ φ₂) (at level 50).

Definition MLtop := (¬ ⊥). 
Notation "⊤" := MLtop.
Goal ⊤ = ⊤. unfold MLtop. unfold MLneg. unfold MLarr. reflexivity. Qed. (* nice *)

Definition MLexists (χφ₁ : (EV -> φ)) := (E χφ₁).
Notation "∃ χ .. χ₂ ; φ" :=
         (MLexists (fun χ => .. (MLexists (fun χ₂ => φ)) ..))
         (at level 200, χ binder, χ₂ binder, φ at level 50, right associativity).


Definition MLforall (χφ₁ : (EV -> φ)) := ¬ (E (fun (χ₁ : EV) => ¬ (χφ₁ χ₁))).
Notation "∀ χ .. χ₂ ; φ" :=
         (MLforall (fun χ => .. (MLforall (fun χ₂ => φ)) ..))
         (at level 200, χ binder, χ₂ binder, φ at level 50, right associativity).

(*
 * Notation "∀ χ ; φ" := (¬MLexists (fun (χ : EV) => ¬φ)) 
 * Notation "∀ c ; φ" := (¬(∃ c ; ¬φ)) 
 *)

Definition MLsmallfix (Χφ₁ : (SV -> φ)) := mu Χφ₁.
Notation "'μ' Χ ; φ" := (MLsmallfix (fun (Χ : SV) => φ)) (at level 200, Χ binder, φ at level 50, right associativity).


From Coq Require Import Logic.FunctionalExtensionality
                        Logic.Eqdep_dec.


Theorem eq_dec_EV (e1 e2 : EV) : (e1 = e2 \/ ~(e1 = e2)).
Proof.
induction e1; induction e2; try (left; reflexivity);
                            try (right; intuition; inversion H).
Qed.
Theorem eq_dec_SV (s1 s2 : SV) : (s1 = s2 \/ ~(s1 = s2)).
Proof.
induction s1; induction s2; try (left; reflexivity);
                            try (right; intuition; inversion H).
Qed.
Theorem eq_dec_Σ (σ₁ σ₂ : Σ) : (σ₁ = σ₂ \/ ~(σ₁ = σ₂)).
Proof.
induction σ₁; induction σ₂; try (left; reflexivity);
                            try (right; intuition; inversion H).
Qed.


Theorem eq_dec_φ : forall (φ₁ φ₂ : φ), (φ₁ = φ₂ \/ ~(φ₁ = φ₂)).
Proof.

induction φ₁;induction φ₂;
(* simple cases when we compare φ's with different root constructors.*)
try(right; intuition; now inversion H);
try(right; intuition; now inversion H0);
try(right; intuition; now inversion H1).

+ pose proof (eq_dec_EV e e0). destruct H.  
++ left. rewrite H. reflexivity.
++ right. intuition. inversion H0. apply (H H2).

+ pose proof (eq_dec_SV s s0). destruct H.
++ left. rewrite H. reflexivity.
++ right. intuition. inversion H0. apply (H H2).

+ pose proof (eq_dec_Σ σₓ σₓ0). destruct H.
++ left. rewrite H. reflexivity.
++ right. intuition. inversion H0. apply (H H2).

+ specialize (IHφ₁1 φ₂1). specialize (IHφ₁2 φ₂2). destruct IHφ₁1.
++ destruct IHφ₁2.
+++ left. subst. reflexivity.
+++ right. subst. unfold not. intros. inversion H. contradiction.
++ right. unfold not. intros. inversion H0. contradiction.

+ left. reflexivity.

+ specialize (IHφ₁1 φ₂1). specialize (IHφ₁2 φ₂2). destruct IHφ₁1.
++ destruct IHφ₁2.
+++ left. subst. reflexivity.
+++ right. subst. unfold not. intros. inversion H. contradiction.
++ right. unfold not. intros. inversion H0. contradiction.

+ clear H0. pose proof (functional_extensionality χφ₁ χφ₁0).
pose proof (H x (χφ₁0 x));
pose proof (H y (χφ₁0 y));
pose proof (H z (χφ₁0 z)).
destruct H1.
++ destruct H2.
+++ destruct H3.
++++ elim H0.
+++++ left. reflexivity.
+++++ intros. destruct x0; assumption.
++++ right. unfold not. intros.
     inversion H4. pose proof (equal_f H6 z). contradiction.
+++ right. unfold not. intros.
   inversion H4. pose proof (equal_f H6 y). contradiction.
++ right. unfold not. intros.
   inversion H4. pose proof (equal_f H6 x). contradiction.

+ clear H0. pose proof (functional_extensionality Χφ₁ Χφ₁0).
pose proof (H X (Χφ₁0 X));
pose proof (H Y (Χφ₁0 Y));
pose proof (H Z (Χφ₁0 Z)).
 destruct H1.
++ destruct H2.
+++ destruct H3.
++++ elim H0.
+++++ left. reflexivity.
+++++ intros. destruct x0; assumption.
++++ right. unfold not. intros. inversion H4.
     pose proof (equal_f H6 Z). contradiction.
+++ right. unfold not. intros. inversion H4.
    pose proof (equal_f H6 Y). contradiction.
++ right. unfold not. intros. inversion H4.
   pose proof (equal_f H6 X). contradiction.
Qed.

(* 
Definition MLsubst (φ₁ : φ) (χφ₁ : EV -> φ) (ψ : EV) : φ :=...

φ[ψ/χ] : φ, ertelmezese?

replace bound variable 
 (χ : EV -> φ) with (ψ : EV -> φ),
substitution eg. application inside E,
 ((EV -> φ) ψ) : φ, if ψ:EV, (need to lookup χ)
--variable capture : no case, shallow embed

Definition MLsubst (φ₁ : φ) (χφ₁ : SV -> φ) (ψ : SV) : φ := ...
*)

(*
Notation "'ν' Χ₁ ; φ" := (¬ (μ Χ₁ ; (¬(φ[¬Χ₁\Χ₁])))) (at level 200, Χ₁ binder, φ at level 50, right associativity).
whhaaa *)

Definition ex1 := χ x.
Print ex1.
Definition ex2 := (∃ x1 ; (∃ x2 ; ⊥)).
Print ex2.
Compute ex2.
Check (E χ).
Definition ex3 := (∀ x1 ; ⊥).
Print ex3.
Compute ex3.
Definition ex4 := ∃ x1 ; χ x1.
Print ex4.
Compute ex4.
Definition ex5 := ∃ x1 ; (∃ x1 ; χ x1 ∧ χ x1).
Print ex5.
Compute ex5.
Definition ex6 := ∃ x1 ; (∃ x2 ; χ x1 ∧ χ x2).
Print ex6.
Compute ex6.

Goal (∀ x1 ; ⊥) = ¬(∃ x1 ; ⊤).
Proof.
unfold MLforall.
unfold MLexists.
unfold MLtop.
unfold MLneg.
unfold MLarr.
reflexivity.
Qed.

Theorem eq_arg (A B : Type) (f : A -> B) : (fun x => f x) = f.
Proof. reflexivity. Qed.

Goal E χ = ∃ x1 ; χ x1.
Proof.
unfold MLexists.
Fail rewrite <- (eq_arg EV φ).
reflexivity.
Qed.

Goal Arr (E (fun _ => Arr Btm Btm)) Btm = ¬∃ x1 ; ⊤.
Proof.
unfold MLexists.
unfold MLtop.
unfold MLneg.
unfold MLarr.
reflexivity.
Qed.



Definition ρ :=  EV -> nat. (* EV -> M; ignoring EV U SV -> M U (P(M)) for now *)

Definition beq_ev (e1 e2 : EV) : bool :=
match e1, e2 with
 | x, x => true
 | y, y => true
 | z, z => true
 | _, _ => false
end.

(* ρ[a/x] = ρ', such that ρ'(x) = a, ρ'(y) = ρ(y) for y ∊ EV where y ≠ x *)
Definition ρ' (ρ₀ : ρ) (e : EV) (n : nat) : ρ :=
fun e' =>  if beq_ev e e' then n else ρ₀ e'.

Notation "ρ [ a / x ]" := (ρ' ρ x a) (at level 200).

