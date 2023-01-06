Require Import Lists.List.
Import ListNotations.
Require Import String.

Module Copland.

Module Term.
  
Definition Plc: Set := string.
Definition N_ID: Set := nat.
Definition Event_ID: Set := nat.
Definition ASP_ID: Set := string.
Definition TARG_ID: Set := string.
Definition Arg: Set := string.

Notation plc_dec := string_dec.

(** The structure of evidence. *)

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Inductive FWD: Set :=
| COMP
| ENCR
| EXTD
| KILL
| KEEP.
Theorem FWD_dec : forall a1 a2 : FWD, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

Inductive SP: Set :=
| ALL
| NONE.
Theorem SP_dec : forall a1 a2 : SP, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.


Inductive ASP: Set :=
| NULL: ASP
| CPY: ASP
| ASPC: SP -> FWD -> ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP.
Theorem ASP_dec : forall a1 a2 : ASP, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

Definition Split: Set := (SP * SP).

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

Theorem Term_dec : forall a1 a2 : Term, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

End Term.

Module Evidence. 

Import Term. 

Inductive Evidence: Set :=
| mt: Evidence
| nn: N_ID -> Evidence
| uu: Plc -> FWD -> ASP_PARAMS -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence.
Theorem Evidence_dec : forall a1 a2 : Evidence, {a1=a2}+{~a1=a2}.
Proof. repeat decide equality. Defined.

(** Abstract definitions for signing and hashing parameters.  
May instantiate these during compilation in the future. *)
Definition sig_params : ASP_PARAMS.
Admitted.
Definition hsh_params : ASP_PARAMS.
Admitted.

Definition enc_params : Plc -> ASP_PARAMS.
Admitted.
Definition sp_ev (sp:SP) (e:Evidence) : Evidence :=
    match sp with
    | ALL => e
    | NONE => mt
    end.

(** Helper function for evidence type reference semantics *)
Definition eval_asp t p e :=
  match t with
  | NULL => mt
  | CPY => e 
  | ASPC sp fwd params =>
    match fwd with
    | KEEP => (sp_ev sp e)
    | KILL => mt
    | _ => uu p fwd params (sp_ev sp e)
    end
  | SIG => uu p EXTD sig_params e
  | HSH => uu p COMP hsh_params e
  (* | ENC q => uu p ENCR (enc_params q) e*)
  end.

Definition splitEv_T_l (sp:Split) (e:Evidence) : Evidence :=
match sp with
| (ALL,_) => e
|  _ => mt
end.

Definition splitEv_T_r (sp:Split) (e:Evidence) : Evidence :=
match sp with
| (_,ALL) => e
|  _ => mt
end.

(** Evidence Type denotational reference semantics.
    The evidence associated with a term, a place, and some initial evidence. *)

Fixpoint eval (t:Term) (p:Plc) (e:Evidence) : Evidence :=
  match t with
  | asp a => eval_asp a p e
  | att q t1 => eval t1 q e
  | lseq t1 t2 => eval t2 p (eval t1 p e)
  | bseq s t1 t2 => ss (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  | bpar s t1 t2 => ss (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  end.

End Evidence. 

End Copland.
