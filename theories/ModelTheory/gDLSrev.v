
Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.gDLS_defs.

Section BDP.

Definition extend_sigP: preds_signature -> preds_signature :=
    fun s => Build_preds_signature (fun P => match P with 
        | inl R => @ar_preds s R
        | inr tt => 1
        end).

Context {s_f: funcs_signature}.
Context {s_P:  preds_signature}.
Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller}.

Notation xform := (form s_f (extend_sigP s_P)).

Theorem BDP_of_DLS: forall M, gDLS_on s_f s_P M smaller -> exists N, smaller N (term + xform) /\ gBDP_on N M.
Proof.
    intros M [N [hsizeN [h hh]]].
    exists N. split.
    apply (@smaller_trans smaller smaller_lt N (term + form)%type).
    apply hsizeN.
    apply (@smaller_sum_incr _ smaller_lt).
    apply (@smaller_rfl _ smaller_lt).
    apply (@smaller_of_inj _ smaller_lt).
    exists (inl).


End BDP.