Require Import Lia.
Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.gDLS_defs.

Definition extend1_sigP: preds_signature -> preds_signature :=
		fun s => Build_preds_signature (fun P => match P with 
			| Some R => @ar_preds s R
			| None => 1
			end).

Definition extend2_sigP: preds_signature -> preds_signature :=
		fun s => Build_preds_signature (fun P => match P with 
			| Some R => @ar_preds s R
			| None => 2
			end).

Section BDP_and_BEP.

	Context {s_f: funcs_signature}.
	Context {s_P:  preds_signature}.
	Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller} {surj_of_smaller: SoS smaller}.
	Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

	Definition x1s_P := extend1_sigP s_P.

	Notation x1form := (form s_f x1s_P).

	Theorem BDP_of_DLS:
	forall M: Type, M -> 
	(forall xM: @model s_f x1s_P, gDLS_on s_f x1s_P xM smaller) ->
	gBDP_on (term + x1form) M.
	Proof.
			intros M m0 dls P.
			pose (xI := @B_I
				s_f
				x1s_P
				M
				(fun _ _ => m0)
				(fun Q v => match Q with
					| Some _ => True
					| None => match v with 
						| cons _ m 0 (nil _) => P m 
						| _ => False
						end
				end)).
			pose (xM := @Build_model s_f x1s_P M xI).
			destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
			destruct (surj_of_smaller hsizeN) as [g hg].
			exists (g >> h).
			intros Htf. 

			(* phi0 :=  `∀ p(x0)` *)
			pose (phi0 := quant s_f x1s_P _ _ All (@atom s_f x1s_P _ _ (None) (cons term $0 0 (nil term)))).
			assert (H3 := hh phi0 (fun _ => g (inl $0))); simpl in H3.
			rewrite <-H3.
			
			intros n'.
			assert (H5 := hh (@atom s_f x1s_P _ _ None (cons term $0 0 (nil term))) (fun _ => n')); simpl in H5.
			rewrite H5.
			destruct (hg n') as [x hx]. unfold ">>". rewrite <-hx.
			apply (Htf x).
	Qed.

	Theorem BEP_of_DLS:
	forall M: Type, M -> 
	(forall xM: @model s_f x1s_P, gDLS_on s_f x1s_P xM smaller) ->
	gBEP_on (term + x1form) M.
	Proof.
		intros M m0 dls P.
		pose (xI := @B_I
				s_f
				x1s_P
				M
				(fun _ _ => m0)
				(fun Q v => match Q with
					| Some _ => True
					| None => match v with 
						| cons _ m 0 (nil _) => P m 
						| _ => False
						end
				end)).
			pose (xM := @Build_model s_f x1s_P M xI).
			destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
			destruct (surj_of_smaller hsizeN) as [g hg].
			exists (g >> h).

			pose (phi0 := quant s_f x1s_P _ _ Ex (@atom s_f x1s_P _ _ (None) (cons term $0 0 (nil term)))).
			assert (H3 := hh phi0 (fun _ => g (inl $0))); simpl in H3.
			rewrite <-H3.
			
			intros [n hn].
			assert (H5 := hh (@atom s_f x1s_P _ _ None (cons term $0 0 (nil term))) (fun _ => n)); simpl in H5.
			destruct (hg n) as [x hx].
			exists x. unfold ">>". rewrite hx.
			rewrite <-H5. apply hn.
	Qed.

	Section BDP'.

		Definition gBDP'_on (B A: Type):=
		forall P, exists B', B' ≤ B /\ (exists f: B' -> A, (forall b', P (f b')) -> (forall a, P a)).

		Definition gBDP' B := forall A, gBDP'_on B A.

		Lemma gBDP'_mono :
		forall B B', B ≤ B' -> gBDP' B -> gBDP' B'.
		Proof.
			intros B B' hBB' bdp A P.
			destruct (bdp A P) as [B'' [hBB'' H]]. exists B''. split.
			+ transitivity B. apply hBB''. apply hBB'.
			+ apply H.
		Qed. 

		Theorem BDP'_of_DLS:
		forall M: Type, M -> 
		(forall xM: @model s_f x1s_P, gDLS_on s_f x1s_P xM smaller) ->
		gBDP'_on (term + x1form) M.
		Proof.
				intros M m0 dls P.
				pose (xI := @B_I
					s_f
					x1s_P
					M
					(fun _ _ => m0)
					(fun Q v => match Q with
						| Some _ => True
						| None => match v with 
							| cons _ m 0 (nil _) => P m 
							| _ => False
							end
					end)).
				pose (xM := @Build_model s_f x1s_P M xI).
				destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
				exists N. split.
				apply hsizeN.
				exists h.

				(* phi0 :=  `∀ P(x0)` *)
				pose (phi0 := quant s_f x1s_P _ _ All (atom s_f x1s_P _ _ (None) (cons term $0 0 (nil term)))).
				assert (Hphi0 := hh phi0 (fun _ => n0)); simpl in Hphi0.
				rewrite <-Hphi0.
				intros H n'.
				assert (Hs := hh (@atom s_f x1s_P _ _ None (cons term $0 0 (nil term))) (fun _ => n'));
				simpl in Hs.
				rewrite Hs. apply H.
		Qed.

	End BDP'.

	Section BEP'.

		Definition gBEP'_on (B A: Type):=
		forall P, exists B', B' ≤ B /\ (exists f: B' -> A, (exists x, P x) -> (exists b, P (f b))).

		Definition gBEP' B := forall A, gBEP'_on B A.

		Lemma gBEP'_mono :
		forall B B', B ≤ B' -> gBEP' B -> gBEP' B'.
		Proof.
			intros B B' hBB' bep A P.
			destruct (bep A P) as [B'' [hBB'' H]]. exists B''. split.
			+ transitivity B. apply hBB''. apply hBB'.
			+ apply H.
		Qed. 

		Theorem BEP'_of_DLS:
		forall M: Type, M -> 
		(forall xM: @model s_f x1s_P, gDLS_on s_f x1s_P xM smaller) ->
		gBEP'_on (term + x1form) M.
		Proof.
				intros M m0 dls P.
				pose (xI := @B_I
					s_f
					x1s_P
					M
					(fun _ _ => m0)
					(fun Q v => match Q with
						| Some _ => True
						| None => match v with 
							| cons _ m 0 (nil _) => P m 
							| _ => False
							end
					end)).
				pose (xM := @Build_model s_f x1s_P M xI).
				destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
				exists N. split.
				apply hsizeN.
				exists h.

				(* phi0 :=  `∀ P(x0)` *)
				pose (phi0 := quant s_f x1s_P _ _ Ex (@atom s_f x1s_P _ _ (None) (cons term $0 0 (nil term)))).
				assert (Hphi0 := hh phi0 (fun _ => n0)); simpl in Hphi0.
				rewrite <-Hphi0.
				intros [n Hn].
				assert (Hs := hh (@atom s_f x1s_P _ _ None (cons term $0 0 (nil term))) (fun _ => n));
				simpl in Hs.
				exists n.
				rewrite <-Hs. apply Hn.
		Qed.

	End BEP'.

End BDP_and_BEP.

Section DDC_and_BAC.

	Context {s_f: funcs_signature}.
	Context {s_P:  preds_signature}.
	Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller} {surj_of_smaller: @SoS smaller}.
	Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

	Definition x2s_P := extend2_sigP s_P.

	Notation x2form := (form s_f x2s_P).

	Lemma lt_dir: directedR lt.
	Proof. 
		intros n n'. exists (S (n + n')). lia.
	Qed.

	Lemma not_DDC_unit: ~ gDDC unit.
	Proof.
		intros H.
		destruct (H nat lt lt_dir) as [f H'].
		destruct (H' tt tt) as [[] [H'' _]]. lia.
	Qed.

	Lemma lt_tot: totalR lt.
	Proof.
		intros n. exists (S n). lia.
	Qed.

	Lemma not_BDC_unit:
	~ (
		forall X, forall R: X -> X -> Prop, totalR R ->
		exists f: unit -> X, totalR (fun x x' => R (f x) (f x'))
	).
	Proof.
		intros H.
		destruct (H nat lt lt_tot) as [f H'].
		destruct (H' tt) as [[] H'']. lia.
	Qed.

	Theorem DDC_of_DLS:
	forall M, M ->
	(forall xM: @model s_f x2s_P, gDLS_on s_f x2s_P xM smaller) ->
	gDDC_on (term + x2form) M.
	Proof.
		intros M m0 dls R hR.
		pose (xI := @B_I
				s_f
				x2s_P
				M
				(fun _ _ => m0)
				(fun Q v => match Q with
					| Some _ => True
					| None => match v with 
						| cons _ v1 _ (cons _ v2 _ (nil _)) => R v1 v2 
						| _ => False
						end
				end)).
		pose (xM := @Build_model s_f x2s_P M xI).
		destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
		destruct (surj_of_smaller hsizeN) as [g hg].
		exists (g >> h).

		pose (phi0 :=
			quant s_f x2s_P _ _ All
				(quant s_f x2s_P _ _ All
					(quant s_f x2s_P _ _ Ex
						(bin s_f x2s_P _ _ Conj
							(atom s_f x2s_P _ _ (None) (cons term $2 1 (cons term $0 0 (nil term))))
							(atom s_f x2s_P _ _ (None) (cons term $1 1 (cons term $0 0 (nil term))))
						)
					)
				)
			).
		

		assert (H1 := hh phi0 (fun _ => g (inl $0))). simpl in H1.
		intros x x'.
		unfold directedR in hR.
		rewrite <-H1 in hR.
		destruct (hR (g x) (g x')) as [n' hn'].
		destruct (hg n') as [y hy].
		exists y.
		unfold ">>".
		rewrite hy.
		simpl in hn'.
		assert (H2 :=
			hh
				(@atom s_f x2s_P _ _ None (cons term $1 1 (cons term $0 0 (nil term))))
				( n' .: (fun _ => (g x)))
			).
		assert (H2' :=
			hh
				(@atom s_f x2s_P _ _ None (cons term $2 1 (cons term $0 0 (nil term))))
				( n' .: (fun _ => (g x')))
			).
		simpl in H2, H2'. rewrite <-H2, <-H2'. apply hn'.
	Qed.

	Definition es_f: funcs_signature :=
			Build_funcs_signature (fun f: False => match f return nat with end).

	Context {kappa: Type}.
	Definition k1s_P: preds_signature := 
		Build_preds_signature (fun o: kappa => 1).

	Definition BAC_on K B (R: K -> B -> Prop) :=
	inhabited B -> (forall n, exists y, R n y) -> exists f : K -> B, forall n, exists w, R n (f w).

Theorem LS_implies_BAC (A: Type) (P: kappa -> A -> Prop): 
(forall M, gDLS_on es_f k1s_P M smaller) ->
@BAC_on kappa A P.
	Proof.
		intros dls [a0] total_R.
		pose (xI := @B_I
			es_f 
			k1s_P	
			A
			(fun _ _ => a0)
			(fun k v => P k (hd v))
		).
		pose (xM := @Build_model es_f k1s_P A xI).
		assert (forall k ρ, ρ ⊨ (∃ (atom es_f k1s_P _ _ k (cons _ ($0) _ (nil _))))).
		- cbn; intros; apply total_R.
		- destruct (dls xM) as [N [[n0] [hsizeN [h ele_el__h]]]].
			assert (forall (m: kappa) (ρ: env xM), ρ ⊨ (∃ atom es_f k1s_P _ _ m (cons term $0 0 (nil term)))).
			+ intro m. apply (H m).
			(* + exists (fun (n: kappa) => h (E_term n)).
				intro m; destruct (H0 m var) as [x Hx].
				exists (term_E x).
				specialize (ele_el__h (atom m (cons term ($0) 0 (nil term))) (fun _ => x)).
				cbn in ele_el__h.
				rewrite E_Κ.
				unfold ">>" in ele_el__h; rewrite <- ele_el__h.
				now cbn in Hx. *)
	Admitted.


	Definition gAC_on B X :=
    forall R: B -> X -> Prop, totalR R ->
		exists f: B -> X, forall b, R b (f b).

	Theorem AC_of_DLS:
	forall M, M ->
	(forall xM: @model es_f k1s_P, gDLS_on es_f k1s_P xM smaller) ->
	gAC_on (k1s_P) (M).
	Proof.
		intros M m0 dls R hR.
		pose (xI := @B_I
				es_f
				k1s_P
				M
				(fun _ _ => m0)
				(fun Q v => R Q (hd v))).
		pose (xM := @Build_model es_f k1s_P M xI).
		destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
		destruct (surj_of_smaller hsizeN) as [g hg].
		exists (fun Q => h (g (inr (atom es_f k1s_P _ _ Q (cons term $0 0 (nil term)))))).
		intros Q.
		unfold totalR in hR.
		assert (hQ := hR Q).
		pose (phiQ :=
			quant es_f k1s_P _ _ Ex
				(atom es_f k1s_P _ _ Q
					(cons term $0 0 (nil term))
				)
			).
		assert (HdlsQ := hh phiQ (fun _ => n0)). simpl in HdlsQ.
		rewrite <-HdlsQ in hQ.
	Admitted.

	Section DDC'.

		Definition gDDC'_on (B A: Type):=
		forall R, directedR R ->
		exists B', B' ≤ B /\ (exists f: B' -> A, directedR (fun b b' => R (f b) (f b'))).

		Definition gDDC' B := forall A, gDDC'_on B A.
	
		Theorem DDC'_of_DLS:
		forall M, M ->
		(forall xM: @model s_f x2s_P, gDLS_on s_f x2s_P xM smaller) ->
		gDDC'_on (term + x2form) M.
		Proof.
			intros M m0 dls R hR.
			pose (xI := @B_I
					s_f
					x2s_P
					M
					(fun _ _ => m0)
					(fun Q v => match Q with
						| Some _ => True
						| None => match v with 
							| cons _ v1 _ (cons _ v2 _ (nil _)) => R v1 v2 
							| _ => False
							end
					end)).
			pose (xM := @Build_model s_f x2s_P M xI).
			destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
			exists N. split. apply hsizeN.
			exists h.

			pose (phi0 :=
				quant s_f x2s_P _ _ All
					(quant s_f x2s_P _ _ All
						(quant s_f x2s_P _ _ Ex
							(bin s_f x2s_P _ _ Conj
								(atom s_f x2s_P _ _ (None) (cons term $2 1 (cons term $0 0 (nil term))))
								(atom s_f x2s_P _ _ (None) (cons term $1 1 (cons term $0 0 (nil term))))
							)
						)
					)
				).
			
			assert (Hphi0 := hh phi0 (fun _ => n0)). simpl in Hphi0.
			intros n n'.
			unfold directedR in hR.
			rewrite <-Hphi0 in hR.
			destruct (hR n n') as [y hy].
			exists y.
			unfold ">>".
			assert (Hs :=
				hh
					(@atom s_f x2s_P _ _ None (cons term $1 1 (cons term $0 0 (nil term))))
					( y .: (fun _ => n))
				).
			assert (Hs' :=
				hh
					(@atom s_f x2s_P _ _ None (cons term $2 1 (cons term $0 0 (nil term))))
					( y .: (fun _ => n'))
				).
			simpl in Hs, Hs'. rewrite <-Hs, <-Hs'. apply hy.
		Qed.

	End DDC'.

End DDC_and_BAC.

Section RDLS.

	Context {s_f: funcs_signature}.
	Context {s_P:  preds_signature}.
	Context {kappa: Type}.

	Notation x1form := (form s_f x1s_P).
	Notation x2form := (form s_f x2s_P).
	Definition k2s_P := @Build_preds_signature kappa (fun k => 2).
	Notation k2form := (form s_f k2s_P).
	
	Theorem BDP_of_RDLS: (forall M, @RDLS_on s_f x1s_P M) -> forall A, A -> gBDP_on x1form A.
	Proof.
		intros dls A a0 P.
		pose (mA := Build_model (@B_I s_f x1s_P _
			(fun _ _ => a0)
			(fun q v0 => match q, v0 with
				| Some _, _ => True
				| None, nil _ => False
				| None, cons _ a _ _ =>P a
				end)
			)).
		destruct (dls mA) as [IF [h Hh]].
		exists h.
		intros Hg.
		pose (phiQ := quant s_f x1s_P _ _ All (@atom s_f x1s_P _ _ (None) (cons term $0 _ (nil term)))).
		assert (H := Hh phiQ (fun _ => falsity)).  simpl in H. rewrite <-H.
		intros n0.
		pose (phin0 := (@atom s_f x1s_P _ _ (None) (cons term $0 _ (nil term)))).
		assert (Hn0 := Hh phin0 (fun _ => n0)).  simpl in Hn0. rewrite Hn0. apply Hg.
	Qed.
	
	Theorem BEP_of_RDLS: (forall M, @RDLS_on s_f x1s_P M) -> forall A, A -> gBEP_on x1form A.
	Proof.
		intros dls A a0 P.
		pose (mA := Build_model (@B_I s_f x1s_P _
			(fun _ _ => a0)
			(fun q v0 => match q, v0 with
				| Some _, _ => True
				| None, nil _ => False
				| None, cons _ a _ _ =>P a
				end)
			)).
		destruct (dls mA) as [IF [h Hh]].
		exists h.
		intros Hg.
		pose (phiQ := quant s_f x1s_P _ _ Ex (@atom s_f x1s_P _ _ (None) (cons term $0 _ (nil term)))).
		assert (HQ := Hh phiQ (fun _ => falsity)). simpl in HQ.
		rewrite <-HQ in Hg. destruct Hg as [n0 Hn0].
		pose (phi0 := @atom s_f x1s_P _ _ (None) (cons term $0 _ (nil term))).
		exists n0.
		assert (Hphin0 := Hh phi0 (fun _ => n0)).
		simpl in Hphin0. unfold ">>" in Hphin0.
		rewrite <-Hphin0. apply Hn0.
	Qed.

	Theorem DDC_of_RDLS: (forall M, @RDLS_on s_f x2s_P M) -> forall A, A -> gDDC_on x2form A.
	Proof.
		intros dls A a0 R HR.
		pose (mA := Build_model (@B_I s_f x2s_P _
			(fun _ _ => a0)
			(fun q v0 => match q, v0 with
				| Some _, _ => True
				| None, cons _ a1 _ (cons _ a2 _ (nil _)) => R a1 a2
				| None, _ => False
				end)
			)).
		destruct (dls mA) as [IF [h Hh]].
		exists h.
		pose (phiQ :=
				quant s_f x2s_P _ _ All
					(quant s_f x2s_P _ _ All
						(quant s_f x2s_P _ _ Ex
							(bin s_f x2s_P _ _ Conj
								(atom s_f x2s_P _ _ (None) (cons term $2 1 (cons term $0 0 (nil term))))
								(atom s_f x2s_P _ _ (None) (cons term $1 1 (cons term $0 0 (nil term))))
							)
						)
					)
				).
		assert (HQ := Hh phiQ (fun _ => falsity)); simpl in HQ.
		rewrite <-HQ in HR.
		intros x x'.
		destruct (HR x x') as [y Hy].
		exists y.
		unfold ">>".
		assert (Hs :=
			Hh
				(@atom s_f x2s_P _ _ None (cons term $1 1 (cons term $0 0 (nil term))))
				( y .: (fun _ => x))
			).
		assert (Hs' :=
			Hh
				(@atom s_f x2s_P _ _ None (cons term $2 1 (cons term $0 0 (nil term))))
				( y .: (fun _ => x'))
			).
		simpl in Hs, Hs'. rewrite <-Hs, <-Hs'. apply Hy.
	Qed.

End RDLS.


Notation "A ≤s B" := (exists f: B -> A, surjective f) (at level 90).

Lemma BDP_mono_s: forall B B', B ≤s B' -> (gBDP B -> gBDP B').
Proof.
	intros B B' [g hg] bdp A P.
	destruct (bdp A P) as [f hf].
	exists (g >> f).
	intros H a.
	apply hf. intros b.
	destruct (hg b) as [b' h'].
	rewrite <-h'. apply H.
Qed.
	
Lemma BEP_mono_s: forall B B', B ≤s B' -> (gBEP B -> gBEP B'). 
Proof.
	intros B B' [g hg] bep A P.
	destruct (bep A P) as [f hf].
	exists (g >> f).
	intros [a H].
	destruct (hf (ex_intro _ a H)) as [b hb].
	destruct (hg b) as [b' hb'].
	exists b'. unfold ">>". rewrite hb'. apply hb.
Qed.

Lemma DDC_mono_s: forall B B', B ≤s B' -> (gDDC B -> gDDC B').
Proof.
	intros B B' [g hg] ddc A R hdr.
	destruct (ddc A R hdr) as [f hf].
	exists (g >> f).
	intros b1' b2'.
	destruct (hf (g b1') (g b2')) as [b0 h0].
	destruct (hg b0) as [b0' e].
	exists b0'. unfold ">>". rewrite e. apply h0.
Qed.