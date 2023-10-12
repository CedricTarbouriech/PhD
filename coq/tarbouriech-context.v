Require Import Setoid.
Require Import Classical.

(***********
 *         *
 * Bennett *
 *         *
 ***********)
Parameter Entity: Set.
Parameter F : Entity -> Entity -> Prop.
Parameter Ps : Entity -> Entity -> Prop.
Definition P x y := exists s, F x s /\ Ps s y.
Definition PP x y := P x y /\ ~ P y x.
Definition O x y := exists z, P z x /\ P z y.
Definition Os x y := exists z, Ps z x /\ Ps z y.
Definition PPs x y := Ps x y /\ ~ F y x.

(* Only Slots are Filled *)
Axiom only_slots_are_filled : forall a s,
  F a s -> exists b, Ps s b.

(* Slots Cannot Fill *)
Axiom slots_cannot_fill : forall a s,
  F a s -> ~exists b, Ps a b.

(* Slots Don’t Have Slots *)
Axiom slots_dont_have_slots : forall x y,
  Ps x y -> ~exists z, Ps z x.

(* Filler Irreflexivity *)
Theorem BT1 : forall x,
  ~ F x x.
Proof.
  intros x h.
  apply only_slots_are_filled in h as h1.
  apply slots_cannot_fill in h as h2.
  contradiction.
Qed.

(* Filler Asymmetry *)
Theorem BT2 : forall x y,
  F x y -> ~ F y x.
Proof.
  intros x y H.
  apply only_slots_are_filled in H.
  intro h.
  apply slots_cannot_fill in h.
  contradiction.
Qed.

(* Filler Transitivity *)
Theorem BT3 : forall x y z,
  (F x y /\ F y z) -> F x z.
Proof.
  intros x y z [].
  apply only_slots_are_filled in H as [].
  apply slots_cannot_fill in H0 as [].
  exists x0.
  apply H.
Qed.

(* Slot Irreflexivity *)
Theorem BT4 : forall x,
  ~Ps x x.
Proof.
  intros x h.
  apply slots_dont_have_slots in h as h1.
  destruct h1.
  exists x.
  assumption.
Qed.

(* Slot Asymmetry *)
Theorem BT5 : forall x y,
  Ps x y -> ~ Ps y x.
Proof.
  intros x y H h.
  apply slots_dont_have_slots in h as [].
  exists x.
  assumption.
Qed.

(* Slot Transitivity *)
Theorem BT6 : forall x y z,
  (Ps x y /\ Ps y z) -> Ps x z.
Proof.
  intros x y z [].
  apply slots_dont_have_slots in H0 as [].
  exists x.
  assumption.
Qed.

(* Improper Parthood Slots *)
Axiom whole_improper_slots : forall x,
  (exists y, Ps y x) -> (exists z, Ps z x /\ F x z).

(* Slot Inheritance *)
Axiom slot_inheritance : forall x y z1 z2,
  (Ps z1 y /\ F x z1) /\ Ps z2 x -> Ps z2 y.

(* Mutual Occupancy is Identity *)
Axiom mutual_occupancy : forall x y z1 z2,
  (Ps z1 y /\ F x z1) /\ (Ps z2 x /\ F y z2) -> x = y.

(* Single Occupancy *)
Axiom single_occupancy : forall x y,
  Ps x y -> exists! z, F z x.

Ltac unify_filler F1 F2 :=
  let a := fresh "a" in
  let Pssa := fresh "Pssa" in
  let UniqueF := fresh "UniqueF" in
  let a' := fresh "a'" in
  pose proof (only_slots_are_filled _ _ F2) as (a & Pssa);
  pose proof (single_occupancy _ _ Pssa) as (a' & _ & UniqueF);
  apply UniqueF in F1 as eq1;
  apply UniqueF in F2 as eq2;
  symmetry in eq2;
  subst; clear a Pssa UniqueF F2.

(* Parthood Transitivity *)
Theorem parthood_transitivity : forall x y z,
  (P x y /\ P y z) -> P x z.
Proof.
  firstorder.
  unfold P.
  eauto 6 using slot_inheritance.
Qed.

(* Anti-Symmetry *)
Theorem BT8 : forall x y,
  (P x y /\ P y x) -> x = y.
Proof.
  unfold P.
  firstorder.
  apply mutual_occupancy with (z1 := x1) (z2 := x0).
  auto.
Qed.

(* Conditional Reflexivity *)
Theorem BT9 : forall x,
  (exists z, Ps z x) -> P x x.
Proof.
  intros x h.
  apply whole_improper_slots in h as [y ].
  unfold P.
  exists y.
  apply and_comm; assumption.
Qed.

(* Parts <-> Slots *)
Theorem BT11 : forall y,
  ((exists x, P x y) <-> (exists z, Ps z y)).
Proof.
  intro y.
  unfold P.
  split.
  - intros [x [s []]].
    exists s.
    assumption.
  - intros [z Pszy].
    apply single_occupancy in Pszy as H1.
    destruct H1 as [x []].
    exists x, z.
    split; assumption.
Qed.

(* Composites <-> Slot-Composites *)
Theorem BT12 : forall y,
  ((exists x, PP x y) <-> (exists z, PPs z y)).
Proof.
  unfold PP, PPs, P.
  intro b.
  split.
  (* left to right *)
  - intros [a [[c [Fac Pscb]] nPba]].
    exists c.
    split.
    -- apply Pscb.
    -- pose proof (single_occupancy _ _ Pscb) as [d [Fdc Uc]].
       intros Fbc.
       pose proof (Uc a Fac). subst.
       pose proof (Uc b Fbc). subst.
       apply nPba.
       exists c; split; assumption.
  (* right to left *)
  - intros [a [Psab nFba]].
    pose proof (single_occupancy _ _ Psab) as [c [Fca Uc]].
    exists c.
    split.
    + exists a; split; eauto.
    + intros [d [Fbd Psfc]].
    apply nFba.
    assert (b = c) as Heqbc.
    * eapply mutual_occupancy with (z1 := d) (z2 := a).
      repeat split; assumption.
    * rewrite Heqbc in *.
      apply Fca.
Qed.

(* Slot Strong Supplementation *)
Theorem BA8 : forall a b,
  (exists s, Ps s a) /\ (exists t, Ps t b) ->
    (~(exists u, Ps u a /\ F b u) ->
      (exists v, Ps v b /\ ~Ps v a)).
Proof.
  intros a b ((s & Pssa) & (t & Pstb)) nPba.
  pose proof (whole_improper_slots b (ex_intro _ t (Pstb))) as (u & Psub & Fbu).
  exists u; split; auto.
  intros Psua.
  destruct nPba.
  exists u; split; assumption.
Qed.

(* Slot Weak Supplementation *)
Theorem BT13 : forall x y,
  (PP x y -> (exists z, Ps z y /\ ~ Ps z x)).
Proof.
  intros a b [[c [Fac Pscb]] nPba].
  pose proof (whole_improper_slots b).
  destruct H.
  exists c.
  exact Pscb.
  exists x.
  split.
  apply H.
  intro h.
  apply nPba.
  destruct H.
  exists x.
  split; assumption.
Qed.

(* Slot Extensionality *)
(* This is not a theorem of the theory. *)
Theorem BT14 : forall x y,
  ((exists z, PP z x) \/ (exists z, PP z y)) ->
    ((x = y) <->
      (exists z, PPs z x <-> PPs z y)).
Abort.

(**********************
 *                    *
 * Tarbouriech et al. *
 *                    *
 **********************)

(*******************
 * Slot Definition *
 *******************)
Definition S s := exists a, Ps s a.

Axiom single_owner : forall a b s, Ps s a -> Ps s b -> a = b.

Ltac unify_owner Ps1 Ps2 :=
  pose proof (single_owner _ _ _ Ps2 Ps1);
  subst; clear Ps2.

Theorem anti_inheritance : forall a b s t,
  a <> b -> Ps s b -> F a s -> Ps t a -> ~Ps t b.
Proof.
  intros a b s t a_neq_b Pssb Fas Psta h.
  unify_owner Psta h.
  contradiction.
Qed.

Definition IPs s a := Ps s a /\ F a s.

Lemma either_proper_or_improper : forall s,
  S s -> exists a, PPs s a /\ ~ IPs s a \/ ~ PPs s a /\ IPs s a.
Proof.
  intros s (a & Pssa); exists a.
  destruct (classic (F a s)) as [Fas|NFas];
  [right|left]; split.
  - intros [_ NFxs]; contradiction.
  - split; assumption.
  - split; assumption.
  - intros [_ Fxs]; contradiction.
Qed.

Lemma proper_part_in_proper_slot : forall a b,
  PP b a <-> (exists s, PPs s a /\ F b s).
Proof.
  intros a b.
  split.
  - intros ((s & Fbs & Pssa) & nPab).
    exists s; repeat split; auto.
    intros Fas; destruct nPab.
    unify_filler Fas Fbs.
    apply BT9; exists s; assumption.
  - intros (s & [Pssa nFas] & Fbs).
    split.
    exists s; split; auto.
    intros Pab; destruct nFas.
    assert (a = b) as <-.
    apply BT8; split; auto.
    split with (x:=s); split; auto.
    assumption.
Qed.

Axiom filler_has_imp_slot : forall a s, F a s -> exists t, IPs t a.

Lemma general_conditional_refl : forall a s,
  Ps s a \/ F a s -> P a a.
Proof.
  intros a s Ps_or_F.
  apply BT9.
  destruct Ps_or_F as [Pssa|Fas].
  - exists s; assumption.
  - pose proof (filler_has_imp_slot a s Fas) as (t & Psta & _).
    exists t; assumption.
Qed.

(* Only One Improper Slot per Filler *)
Axiom unique_improper_slot : forall a s t,
  IPs s a -> IPs t a -> s = t.

Ltac unify_improper_slot IPs1 IPs2 :=
  pose proof (unique_improper_slot _ _ _ IPs2 IPs1);
  subst; clear IPs2.

Theorem mutual_occupancy_is_slot_identity : forall a b s t,
  Ps s b -> F a s -> Ps t a -> F b t -> s = t.
Proof.
  intros a b s t Pssb Fas Psta Fbt.
  pose proof (mutual_occupancy a b s t (conj (conj Pssb Fas) (conj Psta Fbt))) as <-.
  apply unique_improper_slot with (a:=a); split; assumption.
Qed.

(*********************
 * Contextualisation *
 *********************)

Parameter C : Entity -> Entity -> Entity -> Prop.

Axiom context_domains : forall u s t, C u s t -> S u /\ S s /\ S t.

Definition Cb s t := exists a, F a t /\ Ps s a.

Axiom context_existence : forall s t,
  Cb t s -> exists u, C u s t.

Axiom context_constraints : forall s t u,
  C u s t -> Cb t s.

Axiom context_unicity : forall s t u v,
  C u s t -> C v s t -> u = v.

Ltac unify_context C1 C2 :=
  pose proof (context_unicity _ _ _ _ C2 C1);
  subst; clear C2.

Theorem symmetric_context_are_slot_identity :
  forall s t u v, C u s t -> C v t s -> s = t.
Proof.
  intros s t u v Cust Cvts.
  pose proof (context_constraints s t u Cust) as (a & Fas & Psta).
  pose proof (context_constraints t s v Cvts) as (b & Fbt & Pssb).
  apply mutual_occupancy_is_slot_identity with (a:=a) (b:=b); assumption.
Qed.

Axiom context_left_inject : forall s t u v,
  C v s t -> C v s u -> t = u.

Axiom context_right_inject : forall s t u v a,
  C v t s -> C v u s -> IPs s a -> t = u.

Axiom context_asso : forall s t u v,
  (exists w, C v s w /\ C w t u) <-> (exists x, C v x u /\ C x s t).

Ltac context_asso s := apply context_asso; exists s; auto.

(* Improper-Improper Contextualisation *)
(* v = s o s *)
(* u = (s o s) o t *)
Theorem imp_imp_context : forall s,
  (exists a, IPs s a) <-> C s s s.
Proof.
  intros s; split.
  + intros (a & Pssa & Fas).
    pose proof (context_existence s s (ex_intro _ a (conj Fas Pssa))) as (v & Cvss).
    pose proof (context_domains v s s Cvss) as [(b & Psvb) _].
    pose proof (single_occupancy v b Psvb) as (c & Fcv & _).
    clear Psvb b.
    (* Proof of a = c *)
    pose proof (filler_has_imp_slot c v Fcv) as (t & Pstc & Fct).
    pose proof (context_existence v t (ex_intro _ _ (conj Fcv Pstc))) as (u & Cuvt).
    assert (exists d, C u s d /\ C d s t) as (d & Cust & Cdst).
    context_asso v.
    pose proof (context_constraints s t d Cdst) as (y & Fys & Psty).
    unify_filler Fas Fys.
    unify_owner Psty Pstc.
    pose proof (unique_improper_slot a s t (conj Pssa Fas) (conj Psty Fct)) as <-.
    (* Proof of a = b *)
    assert (exists v', C u s v' /\ C v' s s) as (v' & Cusv' & Cv'ss).
    context_asso v.
    unify_context Cvss Cv'ss.
    pose proof (symmetric_context_are_slot_identity s v u u Cusv' Cuvt) as <-.
    assumption.
  + intros Csss.
    pose proof (context_constraints _ _ _ Csss) as (a & Fas & Pssa).
    exists a; split; auto.
Qed.

(* Proper-Improper Composition *)
Theorem right_imp_composition : forall s t a,
  IPs s a -> F a t -> C t t s.
Proof.
  intros s t x (Pssx & Fxs) Fxt.
  assert (Csss: C s s s). apply imp_imp_context; exists x; split; auto.
  pose proof (context_existence t s (ex_intro _ _ (conj Fxt Pssx))) as (u & Cuts).
  assert (exists v, C u v s /\ C v t s) as (v & Cuvs & Cvts). context_asso s.
  unify_context Cuts Cvts.
  pose proof (context_constraints u s u Cuvs) as (y & Fyu & Pssy).
  unify_owner Pssx Pssy.
  pose proof (context_right_inject s t u u x Cuts Cuvs (conj Pssx Fxs)) as <-.
  assumption.
Qed.

(* Improper-Proper Composition *)
Theorem left_imp_composition : forall s t a,
  IPs s a -> Ps t a -> C t s t.
Proof.
  intros s t x (Pssx & Fxs) Pstx.
  assert (Csss : C s s s). apply imp_imp_context; exists x; split; auto.
  pose proof (context_existence s t (ex_intro _ _ (conj Fxs Pstx))) as (u & Cust).
  assert (exists v, C u s v /\ C v s t) as (v & Cusv & Cvst). context_asso s.
  pose proof (context_unicity s t u v Cust Cvst) as <-.
  pose proof (context_left_inject s t u u Cust Cusv) as <-.
  assumption.
Qed.

Lemma mutual_context_are_identity : forall s t u v,
  C s t u -> C t s v -> s = t.
Proof.
  intros s t u v Cstu Ctsv.
  assert (exists x, C s s x /\ C x v u) as (x & Cssx & Cxvu).
  context_asso t.
  assert (exists y, C t t y /\ C y u v) as (y & Cttx & Cyuv).
  context_asso s.
  pose proof (symmetric_context_are_slot_identity v u x y Cxvu Cyuv) as ->. 
  pose proof (context_constraints u u y Cyuv) as (z & Fzu & Psuz).
  assert (Cuuu: C u u u). apply imp_imp_context; exists z; split; auto.
  unify_context Cuuu Cyuv.
  unify_context Cxvu Cuuu.
  unify_context Ctsv Cssx.
  reflexivity.
Qed.

Definition SO s t := exists x, Ps s x /\ Ps t x.

Lemma SO_refl : forall s, S s -> SO s s.
Proof.
  intros s (x & Pssx).
  exists x; split; auto.
Qed.

Lemma SO_symm : forall s t, SO s t -> SO t s.
Proof.
  intros s t (x & Pssx & Pstx).
  exists x; split; auto.
Qed.

Lemma SO_trans : forall s t u, SO s t -> SO t u -> SO s u.
Proof.
  intros s t u (x & Pssx & Pstx) (y & Psty & Psuy).
  unify_owner Pstx Psty.
  exists x; split; auto.
Qed.
  
Theorem context_same_owner : forall u s t,
  C u s t -> SO u s.
Proof.
  intros u s t Cust.
  pose proof (context_domains u s t Cust) as ([x Psux] & _).
  exists x.
  split; trivial.
  pose proof (whole_improper_slots x) as (v & Psvx & Fxv).
  exists u; assumption.
  pose proof (left_imp_composition v u x (conj Psvx Fxv) Psux) as Cuvu.
  assert (exists z, C u z t /\ C z v s) as (z & _ & Czvs).
  context_asso u.
  pose proof (context_constraints v s z Czvs) as (x0 & Fx0v & Pssx0).
  unify_filler Fxv Fx0v.
  assumption.
Qed.

(* Same Filler *)
Theorem context_same_filler : forall u s t,
  C u s t -> exists a, F a u /\ F a t.
Proof.
  intros u s t Cust.
  pose proof (context_domains u s t Cust) as ([x Psux] & _ & [z Pstz]).
  pose proof (single_occupancy t z Pstz) as (a & Fat & _).
  clear z Pstz.
  exists a; split; trivial.
  pose proof (filler_has_imp_slot a t Fat) as (v & Psva & _).
  pose proof (context_existence t v (ex_intro _ _ (conj Fat Psva))) as (u' & Cu'tv).
  pose proof (context_constraints s t u Cust) as (z & Fzs & Pstz).
  pose proof (context_same_owner u' t v Cu'tv) as (z' & Psu'z' & Pstz').
  unify_owner Pstz Pstz'.
  rename Psu'z' into Psu'z.
  pose proof (context_existence s u' (ex_intro _ _ (conj Fzs Psu'z))) as (w & Cwsu').
  assert (exists w', C w w' v /\ C w' s t) as (w' & Cww'v & Cw'st).
  context_asso u'. 
  unify_context Cust Cw'st.
  pose proof (context_constraints u v w Cww'v) as (a' & Fa'u & Psva').
  unify_owner Psva Psva'.
  assumption.
Qed.

(* BT7 *)
Theorem parthood_transitivity_2 : forall a b c,
  P a b -> P b c -> P a c.
Proof.
  intros a b c (s & Fas & Pssb) (t & Fbt & Pstc).
  pose proof (context_existence t s (ex_intro _ _ (conj Fbt Pssb))) as (u & Cuts).
  exists u.
  pose proof (context_same_filler  _ _ _ Cuts) as (d & Fdu & Fds).
  unify_filler Fas Fds.
  pose proof (context_same_owner _ _ _ Cuts) as (d & Psud & Pstd).
  unify_owner Pstc Pstd.
  split; auto.
Qed.

Theorem right_imp_context_rev : forall s t,
  C t t s -> exists a, IPs s a /\ F a t.
Proof.
  intros s t Ctts.
  pose proof (context_constraints t s t Ctts) as (x & Fxt & Pssx).
  exists x; repeat split; trivial.
  pose proof (context_same_filler t t s Ctts) as (y & Fyt & Fys).
  pose proof (context_domains t t s Ctts) as ((z & Pstz) & _).
  unify_filler Fxt Fyt.
  assumption.
Qed.

Theorem imp_pro_compo_rev : forall s t,
  C t s t -> exists a, IPs s a /\ Ps t a.
Proof.
  intros s t Ctst.
  pose proof (context_constraints s t t Ctst) as (x & Fxs & Pstx).
  exists x; repeat split; trivial.
  pose proof (context_same_owner t s t Ctst) as (y & Psty & Pssy).
  unify_owner Pstx Psty.
  assumption.
Qed.

Theorem compo_stability : forall s t v s' t',
  C s' v s -> C t' v t -> (forall u, C s t u <-> C s' t' u).
Proof.
  intros s t v s' t' Cs'vs Ct'vt u.
  split.
  - intros Cstu.
    assert (exists u', C u' t' u) as (u' & Cu't'u).
    { pose proof (context_constraints _ _ _ Cstu) as (x & Fxt & Psux).
      apply context_existence; exists x; split; auto.
      pose proof (context_same_filler _ _ _ Ct'vt) as (y & Fyt' & Fyt).
      unify_filler Fxt Fyt; auto.
    }
    enough (s' = u') as <-; auto.
    assert (exists w, C u' v w /\ C w t u) as (w & Cu'vw & Cwtu).
    context_asso t'.
    unify_context Cstu Cwtu.
    unify_context Cs'vs Cu'vw.
    reflexivity.
  - intros Cs't'u.
    assert (exists w, C s' v w /\ C w t u) as (w & Cs'vw & Cwtu).
    context_asso t'.
    pose proof (context_left_inject _ _ _ _ Cs'vs Cs'vw) as <-.
    auto.
Qed.

(****************
 * Part of Slot *
 ****************)

Definition PoS s t := exists u, C s t u.

Lemma pos_domains : forall s t, PoS s t -> S s /\ S t.
Proof.
  intros s t [u Cstu].
  pose proof (context_domains s t u Cstu) as (Ss & St & _).
  split; assumption.
Qed.

(* Conditional PoS Reflexivity *)
Theorem conditional_pos_refl : forall s, S s -> PoS s s.
Proof.
  intros s (x & Pssx).
  unfold PoS.  
  pose proof (single_occupancy s x Pssx) as (z & Fzs & _).
  pose proof (general_conditional_refl z s) as [].
  right.
  assumption.
  exists x0.
  pose proof (right_imp_composition x0 s z).
  unfold IPs in H0.
  apply H0.
  destruct H.
  repeat split.
  all: assumption.
Qed.

(* PoS Anti-Symmetry *)
Theorem pos_antisym : forall s t,
  PoS s t -> PoS t s -> s = t.
Proof.
  intros s t [u Cstu] [v Ctsv].
  apply mutual_context_are_identity with (u:=u) (v:=v); assumption.
Qed.

(* PoS Transitivity *)
Theorem pos_trans : forall s t u,
  PoS s t -> PoS t u -> PoS s u.
Proof.
  intros s t u [v Cstv] [w Ctuw]; move w before v.
  assert (exists x, C s u x /\ C x w v) as (x & Csux & _).
  context_asso t.
  exists x; assumption.
Qed.

Theorem pos_same_owner : forall s t,
  PoS s t -> SO s t.
Proof.
  intros s t [u Cstu].
  apply context_same_owner with (u:=s) (s:=t) (t:=u).
  assumption.
Qed.

Theorem ips_eq : forall a s, IPs s a -> (forall t, Ps t a <-> PoS t s).
Proof.
  intros a s.
  intros IPssa t; split.
  intros Psta; exists t; apply left_imp_composition with (a:=a); assumption.
  intros PoSts; destruct IPssa as (Pssa & Fas).
  pose proof (pos_same_owner _ _ PoSts) as (b & H & H1);
  unify_owner Pssa H1; assumption.
Qed.

Theorem slots_constrain_fillers : forall a b,
  (exists s t, F b t /\ F a s /\ PoS t s) <-> P b a.
Proof.
  intros a b; split.
  + intros (s & t & Fbt & Fas & [u Ctsu]).
    pose proof (context_constraints s u t Ctsu) as (a' & Fa's & Psua).
    unify_filler Fas Fa's.
    pose proof (context_same_filler t s u Ctsu) as (b' & Fb't & Fb'u).
    unify_filler Fbt Fb't.
    exists u; split; auto.
  + intros (t & Fbt & Psta).
    pose proof (whole_improper_slots a) as (s & Pssa & Fas).
    { exists t; auto. }
    exists s, t; repeat split; auto.
    exists t.
    apply left_imp_composition with (a:=a); auto.
    split; auto.
Qed.

(* PoS is stable under composition. *)
Theorem pos_stability : forall s t u t' u',
  C t' s t -> C u' s u -> (PoS u t <-> PoS u' t').
Proof.
  intros s t u t' u' Ct'st Cu'su.
  pose proof (compo_stability _ _ _ _ _ Cu'su Ct'st).
  unfold PoS.
  setoid_rewrite H.
  reflexivity.
Qed.

(***************
 * Proper Part *
 ***************)
Definition PPoS s t := PoS s t /\ s <> t.

Theorem ppos_irrefl : forall s, ~ PPoS s s.
Proof.
  intros s [_ ].
  contradiction.
Qed.

Theorem ppos_asym : forall s t,
  PPoS s t -> ~ PPoS t s.
Proof.
  intros s t [] [].
  pose proof (pos_antisym s t H H1).
  contradiction.
Qed.

Theorem ppos_trans : forall s t u,
  PPoS s t -> PPoS t u -> PPoS s u.
Proof.
  intros s t u [] [].
  split.
  - apply pos_trans with (t:=t) ; assumption.
  - intro h.
    rewrite <- h in H1.
    pose proof (pos_antisym s t H H1).
    contradiction.
Qed.

Theorem ppos_same_owner: forall s t, PPoS s t -> SO s t.
Proof.
  intros s t [H _].
  apply pos_same_owner; auto.
Qed.

Theorem proper_slots_iff_parts_of_imp_slot :
  forall s a, IPs s a -> (forall t, PPs t a <-> PPoS t s).
Proof.
  intros s a IPssa t.
  pose proof (ips_eq a s IPssa).
  unfold PPs, PPoS.
  rewrite <- H.
  destruct IPssa as (Pssa & Fas).
  split.
  + intros (Psta & nFat); split; auto.
    intros ->; contradiction.
  + intros (Psta & t_neq_s); split; auto.
    intros Fat.
    assert (IPssa: IPs s a) by (split; auto).
    assert (IPsta: IPs t a) by (split; auto).
    unify_improper_slot IPssa IPsta.
    contradiction.
Qed.

Theorem slots_constrain_fillers_ppos : forall a b,
  (exists s t, F b t /\ F a s /\ PPoS t s) <-> PP b a.
Proof.
  intros a b; split.
  + intros (s & t & Fbt & Fas & (PoSts & t_neq_s)).
    assert (Pba: P b a) by (apply slots_constrain_fillers; exists s, t; auto).
    split; auto.
    intros Pab.
    pose proof (BT8 a b (conj Pab Pba)) as <-.
    destruct PoSts as (u & Ctsu).
    pose proof (context_constraints _ _ _ Ctsu) as (c & Fcs & Psua).
    unify_filler Fas Fcs.
    pose proof (context_same_filler _ _ _ Ctsu) as (c & Fct & Fau).
    unify_filler Fbt Fct.
    assert (IPsua: IPs u a) by (split; auto).
    pose proof (right_imp_composition u s a IPsua Fas) as Cssu.
    unify_context Ctsu Cssu.
    contradiction.
  + intros (Pba & nPab).
    apply slots_constrain_fillers in Pba as (s & t & Fbt & Fas & PoSts).
    exists s, t; repeat split; auto.
    intros ->.
    unify_filler Fas Fbt.
    destruct nPab.
    apply BT9.
    pose proof (filler_has_imp_slot _ _ Fas) as (t & Psta & _).
    exists t; auto.
Qed.

(* PPoS is stable under composition. *)
Theorem ppos_stability : forall s t u v w,
  C v s t -> C w s u -> (PPoS u t <-> PPoS w v).
Proof.
  intros s t u v w Cvst Cwsu.
  split.
  - intros [(u' & Cutu') u_neq_t].
    unfold PPoS.
    split.
    exists u'.
    assert (exists x, C w x u' /\ C x s t) as (x & Cwxu' & Cxst).
    context_asso u.
    pose proof (context_unicity s t v x Cvst Cxst) as <-.
    assumption.
    intro h.
    rewrite h in Cwsu.
    pose proof (context_left_inject s t u v Cvst Cwsu).
    intuition.
  - intros [].
    split.
    pose proof (pos_stability s t u v w Cvst Cwsu) as ut_eq_wv.
    + apply ut_eq_wv; assumption.
    + intros ->.
      apply H0.
      apply context_unicity with (s:=s) (t:=t); assumption.
Qed.

(********************
 * Overlap of Slots *
 ********************)

Definition OoS s t := exists u, PoS u s /\ PoS u t.

(* Conditional OoS Reflexivity *)
Theorem cond_oos_refl : forall s, S s -> OoS s s.
Proof.
  intros s Ss; exists s.
  pose proof (conditional_pos_refl s Ss).
  split; assumption.
Qed.

(* OoS Symmetry *)
Theorem oos_symmetry : forall s t,
  OoS s t -> OoS t s.
Proof.
  unfold OoS.
  intros.
  destruct H as [x H].
  exists x.
  apply and_comm.
  assumption.
Qed.

(* OoS Same Owner *)
Theorem oos_same_owner : forall s t,
  OoS s t -> SO s t.
Proof.
  intros s t [x [PoSxs PoSxt]].
  apply pos_same_owner in PoSxs as [sOwner []].
  apply pos_same_owner in PoSxt as [tOwner []].
  unify_owner H H1.
  exists sOwner; split; assumption.
Qed.

Lemma part_overlap_implies_whole_overlap: forall s t u,
  OoS u t -> PoS t s -> OoS u s.
Proof.
  intros s t u [v [PoSvu PoSvt]] PoSts.
  exists v; split; trivial.
  apply pos_trans with (t:=t); assumption.
Qed.

Theorem slots_overlap_with_imp_slot :
  forall s t a, IPs s a -> Ps t a -> OoS s t.
Proof.
  intros s t x IPssx Pstx.
  unfold OoS, PoS.
  exists t.
  split.
  - exists t.
    apply left_imp_composition with (a:=x) ; assumption.
  - pose proof (single_occupancy t x Pstx) as [y [Fyt _]].
    pose proof (filler_has_imp_slot y t Fyt) as [u IPsuy].
    exists u.
    apply right_imp_composition with (a:=y); assumption.
Qed.

Theorem pos_implies_overlap :
  forall s t, PoS s t -> OoS s t.
Proof.
  intros s t PoSst.
  exists s; split; trivial.
  pose proof (pos_same_owner s t PoSst) as (x & Pssx & _).
  apply conditional_pos_refl.
  exists x; assumption.
Qed.

(* Overlap is stable under composition. *)
(* OoS t u <-> OoS (s o t) (s o u) *)
Lemma oos_stability : forall s t u t' u',
  C t' s t -> C u' s u -> (OoS t u <-> OoS t' u').
Proof.
  intros s t u t' u' Ct'st Cu'su.
  split.
  (* Left-to-right *)
  - intros (v & PoSvt & PoSvu).
    unfold OoS.
    pose proof (context_constraints s t t' Ct'st) as (a & Fas & Psta).
    pose proof (pos_same_owner v t PoSvt) as (b & Psva & Pstb).
    unify_owner Psta Pstb.
    pose proof (context_existence s v (ex_intro _ _ (conj Fas Psva))) as (v' & Cv'sv).
    exists v'.
    split.
    pose proof (pos_stability s t v t' v' Ct'st Cv'sv) as [Hstab _].
    apply Hstab; assumption.
    pose proof (pos_stability s u v u' v' Cu'su Cv'sv) as [Hstab _].
    apply Hstab; assumption.
  - intros (v' & (vt & Cv't'vt) & (vu & Cv'u'vu)).
    assert (exists v, C v' s v /\ C v t vt) as (v1 & Cv'sv1 & Cv1tvt).
    context_asso t'.
    assert (exists v, C v' s v /\ C v u vu) as (v2 & Cv'sv2 & Cv2uvu).
    context_asso u'.
    pose proof (context_left_inject _ _ _ _ Cv'sv1 Cv'sv2) as <-. 
    clear Cv'sv2.
    exists v1.
    split; [exists vt|exists vu]; assumption.
Qed.

Theorem oos_constrains_o: forall a b s t,
  OoS s t -> F a s -> F b t -> O a b.
Proof.
  intros a b s t (u & PoSus & PoSut) Fas Fbt.
  pose proof (pos_domains _ _ PoSus) as ((d & Psud) & _).
  pose proof (single_occupancy _ _ Psud) as (c & Fcu & _).
  exists c; split; apply slots_constrain_fillers;
  [ exists s, u | exists t, u]; auto.
Qed.

(*******************
 * Supplementation *
 *******************)

Axiom slot_strong_supp : forall s t,
  S s -> S t -> (~ PoS t s -> exists u, PoS u t /\ ~ OoS u s).

Theorem slot_weak_supp : forall s t,
  PPoS s t -> exists u, PoS u t /\ ~ OoS u s.
Proof.
  intros s t [].
  pose proof (pos_domains _ _ H) as (Ss & St).
  apply slot_strong_supp; auto.
  intro h.
  pose proof (pos_antisym s t H h).
  contradiction.
Qed.

Theorem oos_extensionality:
  forall s t, S s -> S t -> (forall u, OoS s u <-> OoS t u) -> s = t.
Proof. 
  intros s t Ss St s_eq_t.
  apply NNPP.
  intro s_ne_t.
  assert (~ PoS t s) as NPoSts.
  { intros PoSts.
    destruct (slot_weak_supp t s) as (u & PoSus & NOoSut). split; congruence.
    apply NOoSut.
    apply oos_symmetry.
    rewrite <- s_eq_t.
    exists u. split; trivial.
    pose proof (pos_same_owner u s PoSus) as (x & Psux & Pssx).
    apply conditional_pos_refl.
    exists x; assumption. }
  pose proof (slot_strong_supp _ _ Ss St NPoSts) as (u & PoSut & NOoSus).
  apply NOoSus.
  apply oos_symmetry.
  rewrite s_eq_t.
  exists u. split; trivial.
  pose proof (pos_same_owner u t PoSut) as (x & Psux & Pstx).
  apply conditional_pos_refl.
  exists x; assumption.
Qed.

Theorem ppos_extensionality:
  forall s t, (exists u, PPoS u s \/ PPoS u t) -> (forall u, PPoS u s <-> PPoS u t) -> s = t.
Proof.
  intros s t (u & H) s_eq_t.
  assert (ppos_domains : forall s t, PPoS s t -> S s /\ S t) by (intros s' t' []; apply pos_domains; assumption).
  apply NNPP.
  intro s_ne_t.
  assert (~ PoS t s) as NPoSts.
  { intros PoSts.
    assert (PPoS t s) as PPoSts.
    split; congruence.
    apply s_eq_t in PPoSts as [_ t_neq_t].
    contradiction. }
  assert (Ss: S s) by (destruct H as [PPoSus|PPoSus]; [|apply s_eq_t in PPoSus];
    pose proof (ppos_domains _ _ PPoSus) as [_ Ss]; assumption).
  assert (St: S t)
    by (destruct H as [PPoSut|PPoSut]; [apply s_eq_t in PPoSut|];
    pose proof (ppos_domains _ _ PPoSut) as [_ St]; assumption).
  pose proof (slot_strong_supp _ _ Ss St NPoSts) as (v & PoSvt & NOoSvs).
  assert (t = v) as <-.
  { apply NNPP.
    intros t_neq_v.
    assert (PPoS v t) as PPoSvt.
    split; congruence.
    apply s_eq_t in PPoSvt as [PoSvs _].
    apply pos_implies_overlap in PoSvs.
    contradiction. }
  apply NOoSvs.
  exists u.
  destruct H as [H1|H1];
  apply s_eq_t in H1 as H2;
  destruct H1, H2;
  split; assumption.
Qed.

(****************
 * Sum of Slots *
 ****************)

Definition SoS u s t := PoS s u /\ PoS t u /\ forall v,
  (PoS v u -> (OoS s v \/ OoS t v)).

Definition SoS2 u s t := forall v, (OoS u v <-> (OoS s v \/ OoS t v)).

Lemma sum_domains: forall s t u, SoS s t u -> S s /\ S t /\ S u.
Proof.
  intros s t u (PoSts & PoSus & _).
  pose proof (pos_domains t s PoSts) as [].
  pose proof (pos_domains u s PoSus) as [].
  repeat split; assumption.
Qed.

Theorem SoS_equiv_SoS2: forall s t, SO s t -> (forall u, SoS u s t <-> SoS2 u s t).
Proof.
  assert (SoS2_imp_Pos: forall s t u, S s -> S u -> SoS2 u s t -> PoS s u).
  {
    intros s t u Ss Su H; apply NNPP; intros NPoSsu.
    pose proof (slot_strong_supp _ _ Su Ss NPoSsu) as (v & PoSvs & NOoSvu).
    apply pos_implies_overlap in PoSvs.
    destruct H with (v:=v).
    destruct H1.
    left; apply oos_symmetry; assumption.
    apply NOoSvu.
    exists x; apply and_comm; assumption.
  }
  intros s t SOst u.
  split.
  - intros (PoSsu & PoStu & H) v.
    split.
    + intros (w & PoSwu & PoSwv).
      pose proof (H w PoSwu) as [H1|H1];
      [left|right];
      apply part_overlap_implies_whole_overlap with (t:=w);
      assumption.
    + intros [|];
      apply oos_symmetry in H0;
      apply oos_symmetry;
      [apply part_overlap_implies_whole_overlap with (t:=s)|
       apply part_overlap_implies_whole_overlap with (t:=t)];
      assumption.
  - intros H.
    assert (S s /\ S t /\ S u) as (Ss & St & Su).
    { destruct SOst as (a & Pssa & Psta).
      repeat split.
      exists a; auto.
      exists a; auto.
      destruct H with (v:=s) as [_ H1].
      destruct H1 as (v & PoSvu & PoSvs). left; apply cond_oos_refl; exists a; auto.
      pose proof (pos_domains _ _ PoSvu) as (_ & Su); auto. }
    repeat split.
    + apply SoS2_imp_Pos with (t:=t); assumption.
    + apply SoS2_imp_Pos with (t:=s); auto.
      unfold SoS2 in *.
      setoid_rewrite (or_comm (OoS s _)) in H.
      assumption.
    + intros v PoSvu.
      apply H.
      apply oos_symmetry.
      apply pos_implies_overlap.
      assumption.
Qed.

(* Sum Existence *)
Axiom sum_existence : forall s t x,
  Ps s x /\ Ps t x -> exists u, SoS u s t.

(* Sum Same Owner *)
Theorem sum_same_owner : forall s t u,
  SoS u s t -> exists a, Ps u a /\ Ps s a /\ Ps t a.
Proof.
  intros s t u (PoSsu & PoStu & _).
  pose proof (pos_same_owner s u PoSsu) as [x []].
  pose proof (pos_same_owner t u PoStu) as [x0 []].
  unify_owner H0 H2.
  exists x.
  repeat split; assumption.
Qed.

(* Sum Unicity *)
Theorem sum_unicity : forall s t u v,
  (SoS u s t -> SoS v s t -> u = v).
Proof.
  intros s t u v SoSust SoSvst.
  apply oos_extensionality.
  - destruct SoSust as [H _].
    apply pos_domains in H as (_ & H).
    assumption.
  - destruct SoSvst as [[] _].
    apply context_domains in H as (_ & H & _).
    assumption.
  - pose proof (sum_domains _ _ _ SoSust) as (Su & Ss & St).
    pose proof (sum_domains _ _ _ SoSvst) as (Sv & _).
    pose proof (sum_same_owner _ _ _ SoSust) as (a & Psua & Pssa & Psta).
    apply SoS_equiv_SoS2 in SoSust, SoSvst; auto.
    intros w; split; intros OoSuw; 
    [apply SoSvst, SoSust | apply SoSust, SoSvst];
    assumption.
    all: exists a; split; auto.
Qed.

(* Sum Idempotence *)
Theorem sum_idempotence : forall s,
  S s -> SoS s s s.
Proof.
  intros s Ss.
  unfold SoS.
  repeat split; try (apply conditional_pos_refl; assumption).
  intros v PoSvs.
  apply pos_implies_overlap in PoSvs.
  apply oos_symmetry in PoSvs.
  left; assumption.
Qed.

(* Sum Commutativity *)
Theorem sum_commutativity : forall s t u,
  (SoS u s t <-> SoS u t s).
Proof.
  intros s t u.
  unfold SoS.
  setoid_rewrite (or_comm (OoS s _)).
  split; intros [H []]; repeat split; assumption.
Qed.

Lemma L47 : forall s t u, SO s t -> SoS u s t -> PoS s u.
Proof.
  intros s t u SOst (PoSsu & _).
  assumption.
Qed.

Theorem L48 : forall s t u v, SO t u -> PoS s t -> SoS v t u -> PoS s v.
Proof.
  intros s t u v _ PoSst (PoStv & PoSuv & _).
  apply pos_trans with (t:=t); assumption.
Qed.

Lemma L49 : forall s t u v,
  SO s t -> SoS v s t -> PoS v u -> PoS s u.
Proof.
  intros s t u v _ (PoSsv & _) PoSvu.
  apply pos_trans with (t:=v) ; assumption.
Qed.

(* PoS t s <-> s = s + t*)
Theorem subpotence :  forall s t, PoS s t <-> SoS t s t.
Proof.
  intros s t.
  split.
  - intros PoSst.
    pose proof (pos_same_owner s t PoSst) as (x & _ & Pstx).
    pose proof (conditional_pos_refl t) as PoStt.
    unfold SoS; repeat split; trivial.
    apply PoStt; exists x; assumption.
    intros v PoSvt.
    right.
    apply oos_symmetry.
    apply pos_implies_overlap.
    trivial.
  - intros (PoSst & _).
    trivial.
Qed.

Theorem overlap_sum_iff_operands: forall s t u,
  (exists a, F a s /\ Ps t a /\ Ps u a) ->
    forall tPu tPu' t' u', SoS tPu t u -> C tPu' s tPu -> C t' s t -> C u' s u ->
      (forall v, OoS v tPu' <-> OoS v t' \/ OoS v u').
Proof.
  intros s t u (a & Fas & Psta & Psua) tPu tPu' t' u'
    SoStPu C_tPu'_s_tPu Ct'st Cu'su v.
  split.
  - intros (w & PoSwv & [w1 C_w_tPu'_w1]).
    assert (exists w2, C w s w2 /\ C w2 tPu w1) as (w2 & Cwsw2 & Cw2_tPu_w1)
      by (context_asso tPu').
    assert (PoS w2 tPu) as PoS_w2_tPu by (exists w1; auto).
    destruct SoStPu as (PoSt_tPu & PoSu_tPu & H).
    apply H in PoS_w2_tPu as [OoStw2|OoSuw2].
    + pose proof (oos_stability _ _ _ _ _ Cwsw2 Ct'st) as oos_stab.
      apply oos_symmetry in OoStw2.
      apply oos_stab in OoStw2 as (w3 & PoSw3w & PoSw3t').
      pose proof (pos_trans _ _ _ PoSw3w PoSwv) as PoSw3v.
      left; exists w3; auto.
    + pose proof (oos_stability _ _ _ _ _ Cwsw2 Cu'su) as oos_stab.
      apply oos_symmetry in OoSuw2.
      apply oos_stab in OoSuw2 as (w3 & PoSw3w & PoSw3u').
      pose proof (pos_trans _ _ _ PoSw3w PoSwv) as PoSw3v.
      right; exists w3; auto.
  - intros [(w & PoSwv & PoSwt')|(w & PoSwv & PoSwu')].
    + exists w; split; auto.
      destruct PoSwt' as (w' & Cwt'w').
      assert (exists w2, C w s w2 /\ C w2 t w') as (w2 & Cwsw2 & Cw2tw')
        by (context_asso t').
      destruct SoStPu as (PoSt & _).
      destruct PoSt as (t2 & Ct_tPu_t2).
      assert (exists w3, C w2 tPu w3 /\ C w3 t2 w') as (w3 & Cw2_tPu_w3 & Cw3t2w')
        by (context_asso t).
      pose proof (context_asso s tPu w3 w) as [(x & Cwxw3 & CxstPu) _].
      exists w2; split; auto.
      unify_context C_tPu'_s_tPu CxstPu.
      exists w3; auto.
    + exists w; split; auto.
      destruct PoSwu' as (w' & Cwu'w').
      assert (exists w2, C w s w2 /\ C w2 u w') as (w2 & Cwsw2 & Cw2uw')
        by (context_asso u').
      destruct SoStPu as (_ & PoSu & _).
      destruct PoSu as (u2 & Cu_tPu_u2).
      assert (exists w3, C w2 tPu w3 /\ C w3 u2 w') as (w3 & Cw2_tPu_w3 & Cw3u2w')
        by (context_asso u).
      pose proof (context_asso s tPu w3 w) as [(x & Cwxw3 & CxstPu) _].
      exists w2; split; auto.
      unify_context C_tPu'_s_tPu CxstPu.
      exists w3; auto.
Qed.

Theorem left_distributivity: forall s t u tPu tPu'1 t' u' tPu'2,
  (exists a, F a s /\ Ps t a /\ Ps u a) ->
    SoS tPu t u -> C tPu'1 s tPu -> C t' s t -> C u' s u -> SoS tPu'2 t' u' ->
      tPu'1 = tPu'2.
Proof.
  intros s t u tPu tPu'1 t' u' tPu'2 H SoStu C_tPu'1 Ct'st Cu'su SoStPu'2.
  apply oos_extensionality.
  - pose proof (context_domains _ _ _ C_tPu'1) as (StPu'1 & _); auto.
  - pose proof (sum_domains _ _ _ SoStPu'2) as (StPu'2 & _); auto.
  - pose proof (overlap_sum_iff_operands s t u H
        tPu tPu'1 t' u' SoStu C_tPu'1 Ct'st Cu'su).
    apply SoS_equiv_SoS2 in SoStPu'2.
    unfold SoS2 in SoStPu'2.
    intros w.
    rewrite SoStPu'2.
    assert (oos_comm: forall s t, OoS s t <-> OoS t s)
      by (intros s0 t0; split; apply oos_symmetry).
    setoid_rewrite (oos_comm).
    apply H0.
    pose proof (sum_same_owner _ _ _ SoStPu'2) as (a & _ & Pst'a & Psu'a).
    exists a; auto.
Qed.

Lemma L53 : forall a s t u, F a s -> SoS u s t -> F a u -> s = u.
Proof.
  intros a s t u Fas ((s' & Csus') & PoStu & H) Fau.
  pose proof (context_same_filler _ _ _ Csus') as (a' & Fa's & Fas').
  unify_filler Fas Fa's.
  pose proof (context_constraints _ _ _ Csus') as (a' & Fa'u &  Pss'a).
  unify_filler Fau Fa'u.
  pose proof (right_imp_composition _ _ _ (conj Pss'a Fas') Fau) as Cuus'.
  unify_context Csus' Cuus'.
  reflexivity.
Qed.

Theorem right_distrib: forall s t u v w x y,
  SoS v s t -> C w v u -> C x s u -> C y t u -> s = t.
Proof.
  intros s t u v w x y ((s' & Csvs') & (t' & Ctvt') & _) Cwvu Cxsu Cytu.
  pose proof (context_constraints _ _ _ Cwvu) as (a & Fav & Psua).

  assert (s = v).
  { pose proof (context_same_filler _ _ _ Csvs') as (e & Fes & Fes').
    pose proof (context_constraints _ _ _ Cxsu) as (b & Fbs & Psub).
    unify_owner Psua Psub.
    unify_filler Fbs Fes.
    pose proof (context_constraints _ _ _ Csvs') as (f & Ffv & Pss'f).
    unify_filler Fav Ffv.
    pose proof (right_imp_composition s' v a (conj Pss'f Fes') Fav) as Cvvs'.
    pose proof (context_unicity _ _ _ _ Csvs' Cvvs') as s_eq_v.
    assumption. }
  
  assert (t = v).
  { pose proof (context_same_filler _ _ _ Ctvt') as (i & Fit & Fit').
    pose proof (context_constraints _ _ _ Cytu) as (c & Fcy & Psuc).
    unify_owner Psua Psuc.
    unify_filler Fcy Fit.
    pose proof (context_constraints _ _ _ Ctvt') as (g & Fgv & Pst'g).
    unify_filler Fav Fgv.
    pose proof (right_imp_composition _ _ _ (conj Pst'g Fit') Fav) as Cvvt'.
    pose proof (context_unicity _ _ _ _ Ctvt' Cvvt') as t_eq_v.
    assumption. }
  rewrite H, H0.
  reflexivity.
Qed.

Lemma left_distrib_ref: forall a b c s t u,
  C a s t -> C b s u -> SoS c a b -> (exists d, SoS d t u /\ C c s d).
Proof.
  intros a b c s t u Cast Cbsu SoScab.
  pose proof (context_constraints s t a Cast) as (x & Fxs & Pstx).
  pose proof (context_constraints s u b Cbsu) as (y & Fys & Psuy).
  unify_filler Fxs Fys.
  rename Psuy into Psux.
  pose proof (sum_existence t u x (conj Pstx Psux)) as (d & SoSdtu).
  exists d.
  split; trivial.
  pose proof (sum_same_owner t u d SoSdtu) as (y & Psdx & Psty & _).
  unify_owner Pstx Psty.
  pose proof (context_existence s d (ex_intro _ _ (conj Fxs Psdx))) as (e & Cesd).
  pose proof (left_distributivity s t u d e a b c (ex_intro _ _ (conj Fxs (conj Pstx Psux)) ) SoSdtu Cesd Cast Cbsu SoScab) as <-.
  assumption.
Qed.

Lemma pos_sum : forall s t u v,
  PoS s v -> PoS t v -> SoS u s t -> PoS u v.
Proof.
  intros s t u v [s' Csvs'] [t' Ctvt'] SoSust.
  pose proof (left_distrib_ref s t u v s' t' Csvs' Ctvt' SoSust) as (w & SoSws't' & Cuvw).
  exists w; assumption.
Qed.

Lemma L1 : forall s t u v,
  SoS u s t -> OoS v s -> OoS v u.
Proof.
  intros s t u v SoSust [x []].
  unfold OoS.
  exists x.
  split.
  assumption.
  destruct SoSust as [PoSsu [PoStu _]].
  apply pos_trans with (t:=s) ; assumption.
Qed.

(* OoS v (s + t) -> OoS s v \/ OoS t v *)
Lemma L3 : forall s t u v,
  SoS u s t -> OoS v u -> OoS s v \/ OoS t v.
Proof.
  intros s t u v [PoSsu [PoStu H_sum]] [x [PoSxv PoSxu]].
  pose proof (H_sum x PoSxu) as [OoSsx|OoStx];
  [left|right];
  apply part_overlap_implies_whole_overlap with (t:=x);
  assumption.
Qed.

(* Sum Associativity *)
Theorem sum_associativity : forall s t u a b c d,
  SoS a s t -> SoS b a u -> SoS d s c -> SoS c t u -> b = d.
Proof.
  intros s t u a b c d  SoSast SoSbau SoSdsc SoSctu.
  enough (SoS d a u).
  apply sum_unicity with (s:=a) (t:=u); assumption.
  repeat split.
  - apply pos_sum with (s:=s) (t:=t).
    destruct SoSdsc; assumption.
    destruct SoSdsc as (_ & PoScd & _), SoSctu as (PoStc & _).
    apply pos_trans with (t:=c); assumption.
    assumption.
  - destruct SoSdsc as (_ & PoScd & _), SoSctu as (_ & PoScu & _).
    apply pos_trans with (t:= c); assumption.
  - intros v PoSvd.
    destruct SoSdsc as (PoSsd & PoScd & H).
    apply H in PoSvd as [OoSsv|OoScv].
    + left.
      apply oos_symmetry.
      apply L1 with (s:=s) (t:=t); trivial.
      apply oos_symmetry; assumption.
    + apply oos_symmetry in OoScv.
      pose proof (L3 t u c v SoSctu OoScv) as [OoStv|OoSuv].
      * left.
        apply oos_symmetry.
        apply L1 with (s:=t) (t:=s).
        apply sum_commutativity; assumption.
        apply oos_symmetry; assumption.
      * right; assumption.
Qed.

Theorem sum_stability: forall u s t v, Cb u v -> Cb s v -> Cb t v -> 
  (forall u' s' t', C u' v u /\ C s' v s /\ C t' v t -> SoS u s t <-> SoS u' s' t').
Proof.
  intros u s t v (a & Fav & Psua) (b & Fbv & Pssa) (c & Fcv & Psta) u' s' t' (Cu'vu & Cs'vs & Ct'vt).
  unify_filler Fav Fbv.
  unify_filler Fav Fcv.
  pose proof (pos_stability _ _ _ _ _ Cu'vu Cs'vs) as PoSsu_stab.
  pose proof (pos_stability _ _ _ _ _ Cu'vu Ct'vt) as PoStu_stab.
  unfold SoS; rewrite PoSsu_stab, PoStu_stab; repeat apply and_iff_compat_l.
  split; intros H.
  - intros w' [x Cwu'x].
    assert (exists w, C w' v w /\ C w u x) as (w & Cw'vw & Cwux) by (context_asso u') .
    pose proof (oos_stability _ _ _ _ _ Cs'vs Cw'vw) as H1.
    pose proof (oos_stability _ _ _ _ _ Ct'vt Cw'vw) as H2.
    rewrite <- H1, <- H2.
    apply H; exists x; auto.
  - intros w PoSwu.
    pose proof (pos_same_owner _ _ PoSwu) as (b & Pswb & Psub).
    unify_owner Psua Psub.
    assert (exists w', C w' v w) as [w' Cw'vw].
    apply context_existence; exists a; split; auto.
    pose proof (oos_stability v _ _ _ _ Cs'vs Cw'vw) as H2.
    rewrite H2.
    pose proof (oos_stability v _ _ _ _ Ct'vt Cw'vw) as H3.
    rewrite H3.
    apply H.
    pose proof (pos_stability v _ _ _ _ Cu'vu Cw'vw) as H1.
    rewrite <- H1.
    auto.
Qed.

(**********
 * Fusion *
 **********)
Definition FoS z (phi: Entity -> Prop) :=
  (forall w, phi w -> PoS w z) /\ (forall v, PoS v z -> (exists w, phi w /\ OoS v w)).

Axiom FoS_existence:
  forall phi, (exists w, phi w /\ (forall v, phi v -> SO w v))
    -> (exists z, FoS z phi).

Theorem FoS_unicity: 
  forall (phi : Entity -> Prop) s t, (exists w, phi w) 
    -> FoS s phi -> FoS t phi -> s = t.
Proof.
  intros phi s t [w phiW] [H1 H2] [H3 H4].
  apply oos_extensionality.
  { apply H1, pos_domains in phiW as [_ Ss].
    assumption. }
  { apply H3, pos_domains in phiW as [_ St].
    assumption. }
  intros u; split.
  - intros (a & PoSas & PoSau).
    pose proof (H2 a PoSas) as (b & phiB & (c & PoSca & PoScb)).
    pose proof (H3 b phiB) as PoSbt.
    pose proof (pos_trans c a u PoSca PoSau) as PoScu.
    pose proof (pos_trans c b t PoScb PoSbt) as PoSct.
    exists c; split; assumption.
  - intros (a & PoSat & PoSau).
    pose proof (H4 a PoSat) as (b & phiB & (c & PoSca & PoScb)).
    pose proof (H1 b phiB) as PoSbs.
    pose proof (pos_trans c a u PoSca PoSau) as PoScu.
    pose proof (pos_trans c b s PoScb PoSbs) as PoScs.
    exists c; split; assumption.
Qed.

Ltac unify_fusion FoS1 Fos2 :=
  pose proof (FoS_unicity _ _ _ FoS1 Fos2);
  subst; clear Fos2.

Theorem conditioned_FoS_iff_SoS: forall s t u, FoS u (fun w => w = s \/ w = t) <-> SoS u s t.
Proof.
  intros s t u.
  split.
  + intros [H H0].
    repeat split; try apply H; auto.
    intros v PoSvu.
    pose proof (H0 v PoSvu) as (w & H1).
    destruct H1.
    apply oos_symmetry in H2.
    destruct H1 as [-> | ->]; auto.
  + intros (PoSsu & PoStu & H).
    split.
    intros w [-> | ->]; auto.
    intros v PoSvu.
    pose proof (H v PoSvu) as []; apply oos_symmetry in H0; [exists s | exists t ]; split; auto.
Qed.

Theorem slot_is_fusion_of_its_slots: forall s, FoS s (fun w => PoS w s).
Proof.
  intros s.
  split; auto.
  intros v PoSvs.
  exists v; split; auto.
  apply cond_oos_refl.
  pose proof (pos_same_owner _ _ PoSvs) as (a & Psva & _).
  exists a; auto.
Qed.

Theorem ips_is_fusion: forall a s, Ps s a -> (exists t, IPs t a /\ FoS t (fun w => Ps w a)).
Proof.
  intros a s Pssa.
  pose proof (whole_improper_slots a) as (t & IPsta).
  exists s; assumption.
  exists t; split; auto.
  pose proof (ips_eq a t IPsta).
  unfold FoS.
  setoid_rewrite H.
  apply slot_is_fusion_of_its_slots.
Qed.

Theorem fusion_stability : forall (phi : Entity -> Prop) s s' t,
  C s' t s -> (forall w, phi w -> exists w', C w' t w ) -> (FoS s phi <-> FoS s' (fun w' => exists w, C w' t w /\ phi w)).
Proof.
  intros phi s s' t Cs'ts H.
  split.
  - intros [H1 H2].
    split.
    + intros w (w' & Cwtw' & phi_w').
      pose proof (H1 _ phi_w') as PoSw's.
      pose proof (pos_stability _ _ _ _ _ Cs'ts Cwtw') as pos_stab.
      rewrite pos_stab in PoSw's; auto.
    + intros v (v' & Cvs'v').
      assert (exists v'', C v t v'' /\ C v'' s v') as (v'' & Cvtv'' & Cv''sv).
      context_asso s'.
      pose proof (H2 v'') as (w'' & phiw'' & OoSv''w'').
      exists v'; auto.
      pose proof (H1 w'' phiw'') as PoSw''s.
      pose proof (pos_same_owner w'' s PoSw''s) as (a & Psw''a & Pssa).
      pose proof (context_constraints _ _ _ Cs'ts) as (b & Fat & Pssb).
      unify_owner Pssa Pssb.
      pose proof (context_existence t w'' (ex_intro _ _ (conj Fat Psw''a))) as (w''' & Cw'''tw'').
      exists w'''; split.
      exists w''; auto.
      pose proof (oos_stability t v'' w'' v w''' Cvtv'' Cw'''tw'') as oos_stab.
      apply oos_stab; auto.
  - intros [H1 H2].
    split.
    + intros w phiW.
      pose proof (H w phiW) as (w' & Cw'tw).
      pose proof (pos_stability t s w s' w' Cs'ts Cw'tw) as pos_stab.
      apply pos_stab, H1.
      exists w; split; auto.
    + intros v' (v & Cv'sv).
      assert (exists v'', C v'' s' v) as (v'' & Cv''s'v).
      { pose proof (context_constraints _ _ _ Cv'sv) as (a & Fas & Psua).
        pose proof (context_same_filler _ _ _ Cs'ts) as (b & Fas' & Fbs).
        unify_filler Fas Fbs.
        apply context_existence; exists a; split; auto. }
      pose proof (H2 v'') as (w & (w' & Cwtw' & phiw') & OoSv''w).
      exists v; auto.
      exists w'; split; auto.
      assert (exists u, C v'' t u /\ C u s v) as (u & Cv''tu & Cusv).
      context_asso s'.
      unify_context Cv'sv Cusv.
      pose proof (oos_stability _ _ _ _ _ Cv''tu Cwtw') as oos_stab.
      apply oos_stab; auto.
Qed.
