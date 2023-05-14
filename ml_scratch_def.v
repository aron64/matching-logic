Module ML.
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
++++ right. unfold not. intros. inversion H4.
     pose proof (equal_f H6 z). contradiction.
+++ right. unfold not. intros. inversion H4.
   pose proof (equal_f H6 y). contradiction.
++ right. unfold not. intros. inversion H4.
   pose proof (equal_f H6 x). contradiction.

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

Search "\/".
Theorem eq_dec_EV_sumb (e1 e2 : EV) : ({(e1 = e2)} + {~(e1 = e2)}).
Proof.
induction e1; induction e2; try (left; reflexivity);
                            try (right; intuition; inversion H).
Qed.
Theorem eq_dec_SV_sumb (s1 s2 : SV) : ({(s1 = s2)} + {~(s1 = s2)}).
Proof.
induction s1; induction s2; try (left; reflexivity);
                            try (right; intuition; inversion H).
Qed.
Theorem eq_dec_Σ_sumb (σ₁ σ₂ : Σ) : ({σ₁ = σ₂} + {~(σ₁ = σ₂)}).
Proof.
induction σ₁; induction σ₂; try (left; reflexivity);
                            try (right; intuition; inversion H).
Qed.

Theorem eq_dec_φ_sumb : forall (φ₁ φ₂ : φ), ({φ₁ = φ₂} + {~(φ₁ = φ₂)}).
Proof.
induction φ₁;induction φ₂;
(* simple cases when we compare φ's with different root constructors.*)
try(right; intuition; now inversion H);
try(right; intuition; now inversion H0);
try(right; intuition; now inversion H1).

+ pose proof (eq_dec_EV_sumb e e0). destruct H.  
++ left. rewrite e1. reflexivity.
++ right. intuition. inversion H. apply (n H1).

+ pose proof (eq_dec_SV_sumb s s0). destruct H.  
++ left. rewrite e. reflexivity.
++ right. intuition. inversion H. apply (n H1).

+ pose proof (eq_dec_Σ_sumb σₓ σₓ0). destruct H.
++ left. rewrite e. reflexivity.
++ right. intuition. inversion H. apply (n H1).

+ specialize (IHφ₁1 φ₂1). specialize (IHφ₁2 φ₂2). destruct IHφ₁1.
++ destruct IHφ₁2.
+++ left. subst. reflexivity.
+++ right. subst. unfold not. intros. inversion H. contradiction.
++ right. unfold not. intros. inversion H. contradiction.


+ left. reflexivity.

+ specialize (IHφ₁1 φ₂1). specialize (IHφ₁2 φ₂2). destruct IHφ₁1.
++ destruct IHφ₁2.
+++ left. subst. reflexivity.
+++ right. subst. unfold not. intros. inversion H. contradiction.
++ right. unfold not. intros. inversion H. contradiction.

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
++++ right. unfold not. intros. inversion H1.
     pose proof (equal_f H3 z). contradiction.
+++ right. unfold not. intros. inversion H1.
   pose proof (equal_f H4 y). contradiction.
++ right. unfold not. intros. inversion H1.
   pose proof (equal_f H5 x). contradiction.

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
++++ right. unfold not. intros. inversion H1.
     pose proof (equal_f H3 Z). contradiction.
+++ right. unfold not. intros. inversion H1.
   pose proof (equal_f H4 Y). contradiction.
++ right. unfold not. intros. inversion H1.
   pose proof (equal_f H5 X). contradiction.
Qed.

Theorem eq_dec_χφ₁ : forall (χφ₁ χφ₂ : (EV -> φ)), (χφ₁ = χφ₂ \/ ~(χφ₁ = χφ₂)).
Proof.
intros.
pose proof (functional_extensionality χφ₁ χφ₂).
pose proof (eq_dec_φ (χφ₁ x) (χφ₂ x));
pose proof (eq_dec_φ (χφ₁ y) (χφ₂ y));
pose proof (eq_dec_φ (χφ₁ z) (χφ₂ z)).
destruct H0.
+ destruct H1. 
++ destruct H2.
+++ elim H.
++++ left. reflexivity.
++++ intros. destruct x0; assumption.
+++ right. unfold not. intros. pose proof(equal_f H3 z). contradiction.
++ right. unfold not. intros. pose proof(equal_f H3 y). contradiction.
+ right. unfold not. intros. pose proof(equal_f H3 x). contradiction.
Qed.

Theorem eq_dec_Χφ₁ : forall ( Χφ₁ Χφ₂ : (SV -> φ)), (Χφ₁ = Χφ₂ \/ ~(Χφ₁ = Χφ₂)).
Proof.
intros.
pose proof (functional_extensionality Χφ₁ Χφ₂).
pose proof (eq_dec_φ (Χφ₁ X) (Χφ₂ X));
pose proof (eq_dec_φ (Χφ₁ Y) (Χφ₂ Y));
pose proof (eq_dec_φ (Χφ₁ Z) (Χφ₂ Z)).
destruct H0.
+ destruct H1. 
++ destruct H2.
+++ elim H.
++++ left. reflexivity.
++++ intros. destruct x0; assumption.
+++ right. unfold not. intros. pose proof(equal_f H3 Z). contradiction.
++ right. unfold not. intros. pose proof(equal_f H3 Y). contradiction.
+ right. unfold not. intros. pose proof(equal_f H3 X). contradiction.
Qed.

Theorem eq_dec_χφ₁_sumb : forall (χφ₁ χφ₂ : (EV -> φ)), ({χφ₁ = χφ₂} + {~(χφ₁ = χφ₂)}).
Proof.
intros.
pose proof (functional_extensionality χφ₁ χφ₂).
pose proof (eq_dec_φ (χφ₁ x) (χφ₂ x));
pose proof (eq_dec_φ (χφ₁ y) (χφ₂ y));
pose proof (eq_dec_φ (χφ₁ z) (χφ₂ z)).
Fail destruct H0. (* so then i made the sumbool versions *)
Restart.
intros.
pose proof (functional_extensionality χφ₁ χφ₂).
pose proof (eq_dec_φ_sumb (χφ₁ x) (χφ₂ x));
pose proof (eq_dec_φ_sumb (χφ₁ y) (χφ₂ y));
pose proof (eq_dec_φ_sumb (χφ₁ z) (χφ₂ z)).
destruct H0.
+ destruct H1. 
++ destruct H2.
+++ elim H.
++++ left. reflexivity.
++++ intros. destruct x0; assumption.
+++ right. unfold not. intros. pose proof(equal_f H0 z). contradiction.
++ right. unfold not. intros. pose proof(equal_f H0 y). contradiction.
+ right. unfold not. intros. pose proof(equal_f H0 x). contradiction.
Qed.


Theorem eq_dec_Χφ₁_sumb : forall (Χφ₁ Χφ₂ : (SV -> φ)), ({Χφ₁ = Χφ₂} + {~(Χφ₁ = Χφ₂)}).
Proof.
intros.
pose proof (functional_extensionality Χφ₁ Χφ₂).
pose proof (eq_dec_φ_sumb (Χφ₁ X) (Χφ₂ X));
pose proof (eq_dec_φ_sumb (Χφ₁ Y) (Χφ₂ Y));
pose proof (eq_dec_φ_sumb (Χφ₁ Z) (Χφ₂ Z)).
destruct H0.
+ destruct H1. 
++ destruct H2.
+++ elim H.
++++ left. reflexivity.
++++ intros. destruct x0; assumption.
+++ right. unfold not. intros. pose proof(equal_f H0 Z). contradiction.
++ right. unfold not. intros. pose proof(equal_f H0 Y). contradiction.
+ right. unfold not. intros. pose proof(equal_f H0 X). contradiction.
Qed.


(* are there any easier way to convert A\/B to be computationally usable, ie {A}+{B}
Inductive eq_χ_binder : (EV -> φ) -> (EV -> φ) -> Prop :=
  | yes (χφ₁ χφ₂ : (EV -> φ)) : (χφ₁ = χφ₂) -> eq_χ_binder χφ₁ χφ₂
  | no (χφ₁ χφ₂ : (EV -> φ)): ((χφ₁ = χφ₂) -> False) -> eq_χ_binder χφ₁ χφ₂
  .*)
  
Search "\/".

(*
Incorrect elimination of "eq_dec_χ_binder χ₁ ψ" in the inductive type "or":
the return type has sort "Set" while it should be "SProp" or "Prop".
Elimination of an inductive object of sort Prop is not allowed on a predicate in sort Set
because proofs can be eliminated only to build proofs.
 

φ[ψ/χ] : φ, how to interpret?

replace bound variable 
 (χ : EV -> φ) with (ψ : EV -> φ),
substitution eg. application inside E,
 ((EV -> φ) ψ) : φ, if ψ:EV, (need to lookup χ)
--variable capture : no case, shallow embed

*)
(*
Fixpoint MLErepl (φ₁ : φ) (χ₁ ψ: EV -> φ) : φ :=
match φ₁ with
 | E χφ₁ => E (match (eq_dec_χφ₁_sumb χ₁ χφ₁) with
             | left _ => ψ
             | right _  => χφ₁
            end)
 | App φ₁ φ₂ => App (MLErepl φ₁ χ₁ ψ) (MLErepl φ₂ χ₁ ψ)
 | Arr φ₁ φ₂ => Arr (MLErepl φ₁ χ₁ ψ) (MLErepl φ₂ χ₁ ψ)
 | mu Χφ₁ => mu (fun Χ₁ => MLErepl (Χφ₁ Χ₁) χ₁ ψ)
 | a => a
end.
*)

Fixpoint MLχsubst (φ₁ : φ) (e1 : EV) (ψ : φ) : φ :=
match φ₁ with
 | χ e => (match (eq_dec_EV_sumb e e1) with
 | left _ => ψ
 | right _ => χ e
end)
 | E χφ₁ => E (fun χ₂ => MLχsubst (χφ₁ χ₂) e1 ψ)
 | App φ₁ φ₂ => App (MLχsubst φ₁ e1 ψ) (MLχsubst φ₂ e1 ψ)
 | Arr φ₁ φ₂ => Arr (MLχsubst φ₁ e1 ψ) (MLχsubst φ₂ e1 ψ)
 | mu Χφ₁ => mu (fun Χ₁ =>  MLχsubst (Χφ₁ Χ₁) e1 ψ)
 | a => a
end.
(*
Fixpoint MLχrepl (φ₁ : φ) (χ₁ ψ : (EV -> φ)) : φ :=
match φ₁ with
 | χ e => χ e
 | E χφ₁ => E (match (eq_dec_χφ₁_sumb χ₁ χφ₁) with
             | left _ => ψ
             | right _  => χφ₁
            end)
 | App φ₁ φ₂ => App (MLχrepl φ₁ χ₁ ψ) (MLχrepl φ₂ χ₁ ψ)
 | Arr φ₁ φ₂ => Arr (MLχrepl φ₁ χ₁ ψ) (MLχrepl φ₂ χ₁ ψ)
 | mu Χφ₁ => mu (fun Χ₁ => MLχrepl (Χφ₁ Χ₁) χ₁ ψ)
 | a => a
end.

Fixpoint MLEsubst (φ₁ : φ) (χ₁ : EV -> φ) (ψ : EV) : φ :=
match φ₁ with
 | E χφ₁ =>  (match (eq_dec_χφ₁_sumb χ₁ χφ₁) with
             | left _ => χφ₁ ψ
             | right _  => E χφ₁
            end)
 | App φ₁ φ₂ => App (MLEsubst φ₁ χ₁ ψ) (MLEsubst φ₂ χ₁ ψ)
 | Arr φ₁ φ₂ => Arr (MLEsubst φ₁ χ₁ ψ) (MLEsubst φ₂ χ₁ ψ)
 | mu Χφ₁ => mu (fun Χ₁ =>  MLEsubst (Χφ₁ Χ₁) χ₁ ψ)
 | a => a
end.

Fixpoint MLSFrepl (φ₁ : φ) (Χ₁ ψ: SV -> φ) : φ :=
match φ₁ with
 | mu Χφ₁ => mu (match (eq_dec_Χφ₁_sumb Χ₁ Χφ₁) with
             | left _ => ψ
             | right _  => Χφ₁
            end)
 | App φ₁ φ₂ => App (MLSFrepl φ₁ Χ₁ ψ) (MLSFrepl φ₂ Χ₁ ψ)
 | Arr φ₁ φ₂ => Arr (MLSFrepl φ₁ Χ₁ ψ) (MLSFrepl φ₂ Χ₁ ψ)
 | E χφ₁ => E (fun χ₁ => MLSFrepl (χφ₁ χ₁) Χ₁ ψ)
 | a => a
end.
*)

Fixpoint MLΧsubst (φ₁ : φ) (s1 : SV) (ψ : φ) : φ :=
match φ₁ with
 | Χ s => match (eq_dec_SV_sumb s s1) with
 | left _ => ψ
 | right _ => Χ s
end
 | App φ₁ φ₂ => App (MLΧsubst φ₁ s1 ψ) (MLΧsubst φ₂ s1 ψ)
 | Arr φ₁ φ₂ => Arr (MLΧsubst φ₁ s1 ψ) (MLΧsubst φ₂ s1 ψ)
 | E χφ₁ => E (fun χ₁ => MLΧsubst (χφ₁ χ₁) s1 ψ)
 | mu Χφ₁ => mu (fun Χ₁ =>  MLΧsubst (Χφ₁ Χ₁) s1 ψ)
 | a => a
end. 
(*
Fixpoint MLΧsubst (φ₁ : φ) (Χ₁ : φ) (ψ : φ) : φ :=
match (eq_dec_φ_sumb φ₁ Χ₁) with
 | left _ => ψ
 | right _ => match φ₁ with
  | App φ₁ φ₂ => App (MLΧsubst φ₁ Χ₁ ψ) (MLΧsubst φ₂ Χ₁ ψ)
  | Arr φ₁ φ₂ => Arr (MLΧsubst φ₁ Χ₁ ψ) (MLΧsubst φ₂ Χ₁ ψ)
  | E χφ₁ => E (fun χ₁ => MLΧsubst (χφ₁ χ₁) Χ₁ ψ)
  | mu Χφ₁ => mu (fun Χ₂ =>  MLΧsubst (Χφ₁ Χ₂) Χ₁ ψ)
  | a => a
  end
end.*)


Class Subst (A B C : Type) := _subst : A -> B -> C -> A.
Notation "a [ c / b ]" := (_subst a b c) (at level 5, c at next level).

#[global] Instance χSubst : Subst φ EV φ := {_subst := MLχsubst}.
#[global] Instance ΧSubst : Subst φ SV φ := {_subst := MLΧsubst}.

(* Notation "φ₁ [ ψ / Χ₁ ]" := (MLΧsubst φ₁ Χ₁ ψ) (at level 5, ψ at next level). *)

(* Notation "φ₁ [ ψ / χ₁ ]" := (MLχsubst φ₁ χ₁ ψ) (at level 5, ψ at next level).*)

Check ((χ y) → (χ x))[⊥/x]. (* this would fail without class insts. due to notation overriding. *)

Definition ex_χsubst := ((χ y) → (χ x))[⊥/x].
Print ex_χsubst.
Compute ex_χsubst.
Definition ex_χsubsted := ¬(χ y).
Goal ex_χsubst = ex_χsubsted.
Proof.
unfold ex_χsubst. unfold ex_χsubsted.  unfold _subst. unfold χSubst.
simpl. destruct (eq_dec_EV_sumb y x).
+ inversion e.
+ destruct (eq_dec_EV_sumb x x).
++ unfold MLneg. unfold MLarr. reflexivity.
++ elim n0. reflexivity.
Qed.

Definition ex_χ_subst_deep_occ := ((∃ c1 ; (χ c1) → (χ z)) → ⊥)[(χ x)/y].
Print ex_χ_subst_deep_occ.
Compute ex_χ_subst_deep_occ.

(* χ₁ binder? 
Notation "φ₁ [ ψ / χ₁ ]" := ((fun (χ₁ : EV) => φ₁) ψ) (at level 5, χ₁ binder, ψ at next level).
Definition ee := ((χ c) → (χ x))[x/c].
Print ee.
Compute ee.
Definition eee := ((∃ c1 ; χ c) → ⊥)[x/c].
Print eee.
Compute eee.
Definition eeee := ((∃ c ; χ c) → ⊥)[x/c].
Print eeee.
Compute eeee.
*) 



Definition MLgreatfix (Χφ₁ : (SV -> φ)) :=
  ¬ (mu (fun (Χ₁ : SV) => ¬(Χφ₁ Χ₁)[(¬ (Χφ₁ Χ₁)) / Χ₁])).
Notation "'ν' Χ ; φ" := (MLgreatfix (fun (Χ : SV) => φ)) (at level 200, Χ binder, φ at level 50, right associativity).


Compute MLgreatfix.
  

Definition ex_nu := ν X1 ; Χ X.
Print ex_nu.
Compute ex_nu.

Definition ex1 := χ x.
Print ex1.
Definition ex2 := (∃ x1 ; (∃ x2 ; ⊥)).
Print ex2.
Compute ex2.
Definition ex3 := (∀ x1 ; ⊥).
Print ex3.
Compute ex3.
Definition ex4 := ∃ x1 ; χ x1.
Print ex4.
Compute ex4.
Compute (E χ).
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


#[global] Instance ρSubst : Subst ρ EV nat := {_subst := ρ'}.
(* Notation "ρ [ a / x ]" := (ρ' ρ x a) (at level 5, a at next level). *)

