Require Import Lia.
Require Import Relations.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Import String.
Require Import Cop.Copland.
Import Copland.Term.
Require Import Utils.Utilities.

Module Manifest.

(** ****************************
  * FORMALIZATION OF ATTESTATION PROTOCOL NEGOTIATION

  By: Anna Fritz and 
      Dr. Perry Alexander 
  Date: January 6th, 2023
************************************)

(** * Manifests 
    [Manifest] defines a single attestation manger and its interconnections.  
    Information includes: 
  asps:  a list of ASPs (measurement operations the AM can preform),
  M : can measure relation (other AMs the current AM knows of),  
  C : context relation (other AMs the current AM depends on),
  Policy : local policy specific to the current AM.
           Minimally includes privacy policy and may possibly include selection policy   

  Other information not necessary for reasoning includes: 
  [key] simulates public key 
  [address] simulates address information and 
  [tpm] simulates cruft necessary to initialize its TPM
*)
Record Manifest := {

   asps : list ASP ;
   K : list Plc ; 
   C : list Plc ; 
   Policy : ASP -> Plc -> Prop ;

(*
   ; key : string
   ; address : nat
   ; tpm_init : nat
*)
 }.

(** [Environment] is a set of AM's each defined by a [Manifest].
  The domain of an [Environment] provides names for each [Manifest].
  Names should be the hash of their public key, but this restriction
  is not enforced here. 
*)

Definition Environment : Type :=  Plc -> (option Manifest).

Definition e_empty : Environment := (fun _ => None).

Definition e_update (m : Environment) (x : Plc) (v : (option Manifest)) :=
  fun x' => if plc_dec x x' then v else m x'.

Theorem e_update_reduce: forall m x v y, x<>y -> (e_update m x v) y = m y.
Proof.
  intros m x v y.
  unfold e_update. intros H.
  destruct (plc_dec x y).
  contradiction.
  reflexivity.
Qed.

(** A [System] is all attestation managers in the enviornement *)

Definition System := list Environment.

(** ****************************
  * REASONING ABOUT MANIFESTS
*****************************)

(** Within the enviornment [e], does the AM at place [k] have ASP [a]? *)

Definition hasASPe(k:Plc)(e:Environment)(a:ASP):Prop :=
match (e k) with
| None => False
| Some m => In a m.(asps)
end.      

(** Within the system [s], does the AM located at place [k] have ASP [a]? *)

Fixpoint hasASPs(k:Plc)(s:System)(a:ASP):Prop :=
    match s with
    | [] => False
    | s1 :: s2 => (hasASPe k s1 a) \/ (hasASPs k s2 a)
    end.

(** Proof that hasASPe is decidable. This means, for any enviornment [e] 
   either the ASP [a] is present or it's not. *)

Theorem hasASPe_dec: forall k e a, {hasASPe k e a}+{~hasASPe k e a}.
Proof.
  intros k e a.
  unfold hasASPe.
  destruct (e k).
  + induction (asps m).
  ++ auto.
  ++ inverts IHl.
  +++ simpl. left. right. apply H.
  +++ simpl. assert (asp_dec : {a = a0} + {a<>a0}). 
           { repeat decide equality. }    
      inverts asp_dec.
  ++++ left. auto.
  ++++ right. unfold not. intros. inverts H1; auto.
  + auto.      
Defined.

(** prove hasASPs is decidable. This means, for any system [s] 
   either the ASP [a] is present or it's not. *)

Theorem hasASPs_dec: forall k e a, {hasASPs k e a}+{~hasASPs k e a}.
Proof.
  intros k e a.
  induction e.
  + simpl in *. right. unfold not. intros. apply H.
  + simpl in *. pose proof hasASPe_dec k a0 a. inverts H. 
  ++ left. left. apply H0.
  ++ inverts IHe.
  +++ left. right. apply H.
  +++ right. unfold not. intros. inverts H1; auto.
Defined. 

(** Determine if manifest [k] from [e] knows how to 
   communicate from [k] to [p]
*)

Definition knowsOfe(k:Plc)(e:Environment)(p:Plc):Prop :=
match (e k) with
| None => False
| Some m => In p m.(K)
end.

Print System.
Print Environment.

(** Determine if place [k] within the system [s] knows of [p] *)

Fixpoint knowsOfs(k:Plc)(s:System)(p:Plc):Prop :=
match s with
| [] => False
| s1 :: ss => (knowsOfe k s1 p) \/ (knowsOfs k ss p)
end.
(* need this second k to change.... *)


(** Prove knowsOfe is decidable. This means, for any enviornment [e] 
   either the current place [p] is aware of place [p] or it's not.  *)

Theorem knowsOfe_dec:forall k e p, {(knowsOfe k e p)}+{~(knowsOfe k e p)}.
Proof.
  intros k e p.
  unfold knowsOfe.
  destruct (e k); auto.
  + induction (K m).
  ++ auto.
  ++ assert (H: {p = a} + {p <> a}). {repeat decide equality. }
     inversion H.
  +++ simpl. left. auto.
  +++ simpl. inverts IHl; auto. right. unfold not. intros. inverts H2; auto.
Defined.

(** decidability of knowsOfs. For any system [s], either [k] knows 
   of [p] within the system or they do not. *)

Theorem knowsOfs_dec:forall k s p, {(knowsOfs k s p)}+{~(knowsOfs k s p)}.
Proof.
    intros k s p.
    induction s; simpl in *.
    + right. unfold not. intros. inversion H.     
    + pose proof knowsOfe_dec k a p. inverts H.
    ++ left. left. apply H0.
    ++ inverts IHs.
    +++ left. right. apply H.
    +++ right. unfold not. intros. inversion H1; auto.
Defined. 

(** Determine if place [k] within the environment [e]  
    depends on place [p] (the context relation) *)
Definition dependsOne (k:Plc)(e:Environment)(p:Plc):Prop :=
match (e k) with
| None => False
| Some m => In p m.(C)
end.

(** Determine if place [k] within the system [s] depends on place [p] (the context relation) *)

Fixpoint dependsOns (k:Plc)(s:System)(p:Plc):Prop :=
match s with
| [] => False
| s1 :: ss => (dependsOne k s1 p) \/ (dependsOns k ss p)
end.

(** decidability of dependsOne. For any enviornment [e], either the AM at place
   [k] depends on something at place [p] or it does not. *)

Theorem dependsOne_dec : forall k e p, {(dependsOne k e p)}+{~(dependsOne k e p)}.
Proof.
  intros k e p.
  unfold dependsOne.
  destruct (e k).
  +  induction (C m).
  ++ auto.
  ++ simpl. inversion IHl.
  +++  auto.
  +++ assert (H': {a = p } + { a <> p}). {repeat decide equality. } inversion H'.
  ++++ left. left. apply H0.
  ++++ right. unfold not. intros. inversion H1; auto.
  + auto.
Defined.

(** decidability of dependsOns. For any system [s], either the AM at place [k] depends on something at place [p] or it does not. *)

Theorem dependsOns_dec : forall k s p, {dependsOns k s p} + {~ dependsOns k s p}.
Proof.
  intros. induction s. 
  + simpl. auto.
  + simpl. pose proof dependsOne_dec k a p. inversion IHs.
  ++ left. right. apply H0. 
  ++ inversion H.
  +++ left. left. apply H1.
  +++ right. unfold not. intros. inversion H2; auto.
Defined. 

(** ***************************
    * EXECUTABILITY 
*****************************)


(** Is term [t] exectuable on the attestation manager named [k] in 
    environment [e]?  Are ASPs available at the right attesation managers
    and are necessary communications allowed? *)

Fixpoint executable(t:Term)(k:Plc)(e:Environment):Prop :=
match t with
| asp a  => hasASPe k e a
| att p t => knowsOfe k e p -> executable t p e
| lseq t1 t2 => executable t1 k e /\ executable t2 k e
| bseq _ t1 t2 => executable t1 k e /\ executable t2 k e
| bpar _ t1 t2 => executable t1 k e /\ executable t2 k e
end.

Ltac right_dest_contr H := right; unfold not; intros H; destruct H; contradiction.

(** executability of a term is decidable *)

Theorem executable_dec:forall t k e,{(executable t k e)}+{~(executable t k e)}.
intros.  generalize k. induction t; intros.
+ unfold executable. apply hasASPe_dec.
+ simpl. pose proof knowsOfe_dec k0 e p. destruct H.
++ destruct (IHt p).
+++ left; auto.
+++ right. unfold not. intros; auto.
++ destruct (IHt p).
+++ left; auto. 
+++ left. intros. congruence.
+ simpl. specialize IHt1 with k0. specialize IHt2 with k0. 
  destruct IHt1,IHt2; try right_dest_contr H. 
++ left. split ; assumption.
+ simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H. 
++ left. split ; assumption.
+ simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H.
++  left. split ; assumption.
Defined.

(** Is term [t] executable on the attestation mnanager named [k] in
  system [s]?  Are ASPs available at the right attestation managers
  and are necessary communications allowed? *)
Fixpoint executables(t:Term)(k:Plc)(s:System):Prop :=
  match t with
  | asp a  => hasASPs k s a
  | att p t => knowsOfs k s p -> executables t p s
  | lseq t1 t2 => executables t1 k s /\ executables t2 k s
  | bseq _ t1 t2 => executables t1 k s /\ executables t2 k s
  | bpar _ t1 t2 => executables t1 k s /\ executables t2 k s
end.

Ltac prove_exec :=
    match goal with
    | |- {executables (asp _) _ _} + {_} => unfold executables; apply hasASPs_dec
    | IHt1 : _ , IHt2 : _ |- {executables _ ?k ?s} + {_} => simpl; specialize IHt1 with k s; specialize IHt2 with k s; destruct IHt1,IHt2 ; try( left; split ; assumption)
    end.

Theorem executables_dec : forall t k s, {executables t k s} + {~executables t k s}.
Proof.
intros.  generalize k s. induction t; intros; try prove_exec; try right_dest_contr H.
+ simpl. destruct (IHt p s0).
++ auto.
++ pose proof knowsOfs_dec k0 s0 p. destruct H.
+++ right. unfold not; intros. intuition.
+++ left. intros. congruence.
Defined. 

(** ***************************
 * EXAMPLE SYSTEM 
 *****************************)

(** Motivated by the Flexible Mechanisms for Remote Attestation, 
 * we have three present parties in this attestation scheme. 
 * These are used for example purposes.
 *)

Notation P0 := "P0"%string.
Notation P1 := "P1"%string.
Notation P2 := "P2"%string.

(** Introducing three asps for testing purposes. *)
Notation aVC :=
  (ASPC ALL EXTD (asp_paramsC "aVC"%string ["x"%string] P1 P1)).
Notation aHSH :=
  (ASPC ALL EXTD (asp_paramsC "aHSH"%string ["x"%string] P1 P1)).
Notation aSFS :=
  (ASPC ALL EXTD (asp_paramsC "aSFS"%string ["x"%string] P2 P2)).

(** Below are relational definitions of Policy. Within the definition, we
 * list each ASP on the AM and state who can recieve a measurement of said
 * ASP (ie doesn't expose sensitive information in the context).
 * 
 * The relying party can share the measurement of aVC with p. 
 * The target can share the measurement aHSH with the appraiser and SIG
 * with anyone. The appraiser can share a hash with anyone. 
*)

Inductive rely_Policy : ASP -> Plc -> Prop :=
| p_rely : forall p, rely_Policy aVC p. 

Inductive tar_Policy : ASP -> Plc -> Prop := 
| p_aHSH : tar_Policy aHSH P2 
| p_SIG : forall p, tar_Policy SIG p. 

Inductive app_Policy : ASP -> Plc -> Prop := 
| p_HSH : forall p, app_Policy HSH p. 

Inductive P0_Policy : ASP -> Plc -> Prop :=.

Inductive P1_Policy : ASP -> Plc -> Prop :=
| aVC_p: P1_Policy aVC P0
| aHSH_p: P1_Policy aHSH P0.

Inductive P2_Policy : ASP -> Plc -> Prop :=
| aSFS_pL: P2_Policy aSFS P1.

Global Hint Constructors P0_Policy : core.
Global Hint Constructors P1_Policy : core.
Global Hint Constructors P2_Policy : core.

(** Definition of environments for use in examples and proofs.  
 * Note there are 3 AM's present... 
 * Relying Party, Target, and Appraiser, each have one AM.
 *)

Definition e0 := e_empty.
Definition e_P0 :=
    e_update e_empty P0 (Some {| asps := []; K:= [P1] ; C := [] ; Policy := P0_Policy |}).
Definition e_P1 :=
    e_update e_P0 P1 (Some {| asps := [aVC;  aHSH]; K:= [P2] ; C := [] ; Policy := P1_Policy|}).
Definition e_P2 :=
    e_update e_P1 P2 (Some {| asps := [aSFS] ; K:= [] ; C := [P1] ; Policy := P2_Policy |}).

(** In our example, the system includes the relying party, the target,
 * and the appraiser
 *)

Definition example_sys_1 := [e_P0; e_P1; e_P2]. 

(** ***************************
  * EXAMPLE SYSTEM PROPERTIES
  *****************************)

(** Prove the relying party has aVC in the relying party's enviornement *)

Example ex1: hasASPe P1 e_P1 aVC.
Proof. unfold hasASPe. simpl. left. reflexivity. Qed.

(** relying party does not have the ASP copy
 *)

Example ex2: hasASPe P0 e_P0 CPY -> False.
Proof. unfold hasASPe. simpl. intros. assumption. Qed.

(** Prove the Relying party has aHSH within the system
 *)

Example ex3: hasASPs P1 (example_sys_1) aHSH.
Proof. unfold hasASPs. unfold hasASPe. simpl. propositional. Qed.

(** the relying party knows of the target within system 1
 *)

Example ex4: knowsOfs P0 example_sys_1 P1.
Proof.
unfold knowsOfs. simpl. left. unfold knowsOfe. simpl.  auto.
Qed.

(** the relying party does not directly know of the appraiser
 *)

Example ex5: knowsOfe P0 e_P2 P2 -> False.
Proof.
  unfold knowsOfe. simpl. intros. destruct H. inversion H. assumption.
Qed.

(** the relying party does not knows of the appraiser within the system... 
 * should be that the relying party knows of the target and the target
 * knows of the appraiser....
 *)

Example ex5': knowsOfs P0 example_sys_1 P2 -> False.
Proof.
unfold knowsOfs. simpl. unfold knowsOfe. simpl. intros. inverts H. inverts H0. inverts H. apply H. inverts H0. destruct H. inverts H. apply H. destruct H. inverts H. inverts H0. apply H0. apply H.
Qed.

(** the relying party is aware of the target in system 1 *)

Example ex6: knowsOfs P0 example_sys_1 P1.
Proof.
unfold knowsOfs,knowsOfe. simpl. auto.
Qed.

(** if the relying party was it's own system, it would still be aware of
 * the target
 *)

Example ex7: knowsOfs P0 [e_P0] P1.
Proof.
unfold knowsOfs,knowsOfe. simpl. auto.
Qed.

(** the appriser depends on target *)

Example ex8 : dependsOne P2 e_P2 P1.
Proof.
unfold dependsOne. simpl. auto.
Qed.

(** within the system, we see that the appraiser depends on target *)

Example ex9 : dependsOns P2 example_sys_1 P1.
Proof. 
  unfold dependsOns.
  simpl.
  unfold dependsOne.
  simpl.
  auto.
Qed.

(** Proof tactic for executability
 *)
Ltac prove_exec' :=
    simpl; auto; match goal with
                 | |- hasASPe _ _ _ => cbv; propositional
                 | |- knowsOfe _ _ _ => unfold knowsOfe; simpl; propositional 
                 | |- _ /\ _ => split; prove_exec'
                 | |- ?A => idtac A
                 end.

(** Is asp SIG executable on the on target place in the P1s's
 * enviornement?
 *)

Example ex10: (executable (asp aHSH) P1 e_P1).
Proof. prove_exec'. Qed.

(** copy is not executable on the target in the appraiser's environment
 *)

Example ex11: (executable (asp CPY) P1 e_P2) -> False.
Proof.
  intros Hcontra; cbv in *; destruct Hcontra. inverts H. destruct H. inverts H. apply H.
Qed.

(** two signature operations are executable on the target
 *)

Example ex12: (executable (lseq (asp aHSH) (asp aVC)) P1 e_P1).
Proof. prove_exec'. Qed.

(** the relying party can ask the target to run aVC and signature
 * operations within system 1
 *) 

Example ex13: (executables 
                            (att P1
                                (lseq (asp aVC)
                                (asp aHSH)))
                P0 example_sys_1).
Proof.
  prove_exec'. cbv. propositional.
Qed.

Theorem string_dec: forall (s s':string), {s=s'}+{s<>s'}.
Proof.
  intros s s'.
  repeat decide equality.
Defined.

Theorem plc_dec: forall (p p':Plc),{p=p'}+{p<>p'}.
Proof.
  intros p p'.
  apply string_dec.
Defined.

Check ASP_dec.

(** A proof that [tar_Policy] is decidable.  If we can show all policies are
 * decidable, life is good.  This is a start.
 *)

Theorem tar_Policy_dec: forall (asp:ASP)(plc:Plc), {(tar_Policy asp plc)}+{~(tar_Policy asp plc)}.
Proof.
  intros asp.
  intros plc.
  destruct asp.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
  assert ({(ASPC s f a)=aHSH} + {(ASPC s f a)<>aHSH}).
  apply ASP_dec.
  assert ({(plc = "P2"%string)} + {(plc <> "P2"%string)}).
  apply plc_dec.
  destruct H; destruct H0. subst.
  left. rewrite e. apply p_aHSH.
  right. rewrite e. unfold not in *. intros Hneg. apply n. inversion Hneg. reflexivity.
  right. unfold not in *. intros Hneg. apply n. inversion Hneg. reflexivity.
  right. unfold not in *. intros Hneg. apply n. inversion Hneg. reflexivity.
  left. apply p_SIG.
  right. unfold not in *. intros Hneg. inverts Hneg.
Defined.

Theorem P0_Policy_dec: forall (asp:ASP)(plc:Plc),
    {(P0_Policy asp plc)}+{~(P0_Policy asp plc)}.
Proof.
  intros asp.
  intros plc.
  destruct asp.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
Defined.
  
Theorem P1_Policy_dec: forall (asp:ASP)(plc:Plc),
    {(P1_Policy asp plc)}+{~(P1_Policy asp plc)}.
  intros asp.
  intros plc.
  destruct asp.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
  assert ({(ASPC s f a)=aHSH} + {(ASPC s f a)<>aHSH}).
  apply ASP_dec.
  assert ({(ASPC s f a)=aVC} + {(ASPC s f a)<>aVC}).
  apply ASP_dec.
  assert ({(plc = "P0"%string)} + {(plc <> "P0"%string)}).
  apply plc_dec.
  destruct H; destruct H0; destruct H1; subst.
  rewrite e in e1. inversion e1.
  rewrite e in e1. inversion e1.
  rewrite e. auto.
  right. unfold not. intros Hneg. inverts Hneg. contradiction. contradiction.
  rewrite e. left. auto.
  right. unfold not. intros Hneg. inverts Hneg. contradiction. contradiction.
  right. unfold not. intros Hneg. inverts Hneg. contradiction. contradiction.
  right. unfold not. intros Hneg. inverts Hneg. contradiction. contradiction.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
Defined.
  
Theorem P2_Policy_dec: forall (asp:ASP)(plc:Plc),
    {(P2_Policy asp plc)}+{~(P2_Policy asp plc)}.
Proof.
  intros asp.
  intros plc.
  destruct asp.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
  assert ({(ASPC s f a)=aSFS} + {(ASPC s f a)<>aSFS}).
  apply ASP_dec.
  assert ({(plc = "P1"%string)} + {(plc <> "P1"%string)}).
  apply plc_dec.
  destruct H,H0.
  left. subst. rewrite e. auto.
  right. unfold not. intros Hneg. inverts Hneg. contradiction.
  right. unfold not. intros Hneg. inverts Hneg. contradiction.
  right. unfold not. intros Hneg. inverts Hneg. contradiction.
  right. unfold not. intros Hneg. inverts Hneg.
  right. unfold not. intros Hneg. inverts Hneg.
Defined.
  
Definition checkASPPolicy(p:Plc)(e:Environment)(a:ASP):Prop :=
match (e p) with (* Look for p in the environment *)
| None => False
| Some m => (Policy m a p) (* Policy from m allows p to run a *)
end.

Fixpoint checkTermPolicy(t:Term)(k:Plc)(e:Environment):Prop :=
  match t with
  | asp a  => checkASPPolicy k e a
  | att r t0 => checkTermPolicy t0 k e
  | lseq t1 t2 => checkTermPolicy t1 k e /\ checkTermPolicy t2 k e
  | bseq _ t1 t2 => checkTermPolicy t1 k e /\ checkTermPolicy t2 k e
  | bpar _ t1 t2 => checkTermPolicy t1 k e /\ checkTermPolicy t2 k e
  end.

Theorem checkTermPolicy_dec:forall t k e,
    (forall p0 a0, {(checkASPPolicy p0 e a0)} + {~(checkASPPolicy p0 e a0)}) ->
    {(checkTermPolicy t k e)}+{~(checkTermPolicy t k e)}.
Proof.
  intros t k e.
  intros H.
  induction t.
  simpl. apply H.
  simpl. assumption.
  simpl; destruct IHt1,IHt2.
  left. split; assumption.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  simpl; destruct IHt1,IHt2.
  left. split; assumption.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  simpl; destruct IHt1,IHt2.
  left. split; assumption.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
  right. unfold not. intros Hneg. destruct Hneg. contradiction.
Defined.

(** Soundness is executability and policy adherence *)

Definition sound (t:Term)(k:Plc)(e:Environment) :=
  (executable t k e) /\ (checkTermPolicy t k e).

(** Prove soundness is decidable with the assumption necessary for policy
 * adherence decidability.
 *)

Theorem sound_dec: forall t p e,
    (forall p0 a0, {(checkASPPolicy p0 e a0)} + {~(checkASPPolicy p0 e a0)})
    -> {sound t p e}+{~(sound t p e)}.
Proof.
  intros t p e.
  intros H.
  unfold sound.
  assert ({executable t p e}+{~(executable t p e)}). apply executable_dec.
  assert ({checkTermPolicy t p e}+{~(checkTermPolicy t p e)}). apply checkTermPolicy_dec. intros. apply H.
  destruct H0,H1.
  left. split; assumption.
  right. unfold not. intros. destruct H0. contradiction.
  right. unfold not. intros. destruct H0. contradiction.
  right. unfold not. intros. destruct H0. contradiction.
Defined.

Theorem sound_local_policies: (forall p0 a0, {(checkASPPolicy p0 e_P2 a0)} + {~(checkASPPolicy p0 e_P2 a0)}).
Proof.
  intros p a.
  assert ({(p="P0"%string)}+{(p<>"P0"%string)}). apply plc_dec.
  assert ({(p="P1"%string)}+{(p<>"P1"%string)}). apply plc_dec.
  assert ({(p="P2"%string)}+{(p<>"P2"%string)}). apply plc_dec.
  destruct H, H0, H1.
  rewrite e in e1. inversion e1.
  rewrite e in e1. inversion e1.
  rewrite e in e1. inversion e1.
  rewrite e.
  unfold checkASPPolicy.
  simpl. apply P0_Policy_dec.
  rewrite e in e1. inversion e1.
  rewrite e.
  unfold checkASPPolicy.
  simpl. apply P1_Policy_dec.
  rewrite e.
  unfold checkASPPolicy.
  simpl. apply P2_Policy_dec.
  right. unfold checkASPPolicy.
  assert (e_P2 p = e_P1 p).
  unfold e_P2.
  apply e_update_reduce. unfold not. intros Hneg. rewrite Hneg in *. contradiction.
  assert (e_P1 p = e_P0 p).
  unfold e_P2.
  apply e_update_reduce. unfold not. intros Hneg. rewrite Hneg in *. contradiction.
  assert (e_P0 p = e_empty p).
  unfold e_P2.
  apply e_update_reduce. unfold not. intros Hneg. rewrite Hneg in *. contradiction.
  unfold not. intros Hneg.
  rewrite <- H in *.
  rewrite <- H0 in *.
  rewrite H1 in *.
  simpl in Hneg.
  assumption.
Qed.

Theorem sound_system_dec: forall t p, {sound t p e_P2}+{~(sound t p e_P2)}.
Proof.
  intros t p.
  apply sound_dec.
  intros p0 a0.
  apply sound_local_policies.
Defined.

Compute sound_system_dec (asp aHSH) P1.
Compute sound_system_dec (asp aSFS) P2.

End Manifest.


(* END OF FILE *)
