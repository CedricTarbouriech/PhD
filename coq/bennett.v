Parameter Entity : Set.
Parameter F : Entity -> Entity -> Prop.
Parameter Ps : Entity -> Entity -> Prop.
Definition P x y := exists s, F x s /\ Ps s y.
Definition PP x y := P x y /\ ~ P y x.
Definition O x y := exists z, P z x /\ P z y.
Definition Os x y := exists z, Ps z x /\ Ps z y.
Definition PPs x y := Ps x y /\ ~ F y x.

(* Only Slots are Filled *)
Axiom A1 : forall x y, F x y -> exists z, Ps y z.

(* Slots Cannot Fill *)
Axiom A2 : forall x y, F x y -> ~exists z, Ps x z.

(* Slots Don’t Have Slots *)
Axiom A3 : forall x y, Ps x y -> ~exists z, Ps z x.

(* Filler Irreflexivity *)
Theorem T1 : forall x, ~ F x x.
Proof.
  intros x Fxx.
  apply A1 in Fxx as H1.
  apply A2 in Fxx as H2.
  contradiction.
Qed.

(* Filler Asymmetry *)
Theorem T2 : forall x y, F x y -> ~ F y x.
Proof.
  intros x y Fxy Fyx.
  apply A1 in Fxy.
  apply A2 in Fyx.
  contradiction.
Qed.

(* Filler Transitivity *)
Theorem T3 : forall x y z, F x y -> F y z -> F x z.
Proof.
  intros x y z Fxy Fyz.
  apply A1 in Fxy as (w & Psyw).
  apply A2 in Fyz as H.
  destruct H.
  exists w; auto.
Qed.

(* Slot Irreflexivity *)
Theorem T4 : forall x, ~Ps x x.
Proof.
  intros x Pxx.
  apply A3 in Pxx as H.
  destruct H.
  exists x; auto.
Qed.

(* Slot Asymmetry *)
Theorem T5 : forall x y, Ps x y -> ~ Ps y x.
Proof.
  intros x y Psxy Psyx.
  apply A3 in Psyx as [].
  exists x; auto.
Qed.

(* Slot Transitivity *)
Theorem T6 : forall x y z, Ps x y -> Ps y z -> Ps x z.
Proof.
  intros x y z Psxy Psyz.
  apply A3 in Psyz as [].
  exists x; apply Psxy.
Qed.

(* Improper Parthood Slots *)
Axiom A4 : forall x, (exists y, Ps y x) -> (exists z, Ps z x /\ F x z).

(* Slot Inheritance *)
Axiom A5 : forall x y z1 z2, Ps z1 y -> F x z1 -> Ps z2 x -> Ps z2 y.

(* Mutual Occupancy is Identity *)
Axiom A6 : forall x y z1 z2, Ps z1 y -> F x z1 -> Ps z2 x -> F y z2 -> x = y.

(* Single Occupancy *)
Axiom A7 : forall x y, Ps x y -> exists! z, F z x.

(* Parthood Transitivity *)
Theorem T7 : forall x y z, P x y -> P y z -> P x z.
Proof.
  intros x y z (s & Fxs & Pssy) (t & Fyt & Pstz).
  exists s; split; auto.
  apply A5 with (x:=y) (z1:=t); auto.
Qed.

(* Anti-Symmetry *)
Theorem T8 : forall x y, P x y -> P y x -> x = y.
Proof.
  intros x y (s & Fxs & Pssy) (t & Fyt & Pstx).
  apply A6 with (z1 := s) (z2 := t); auto.
Qed.

(* Conditional Reflexivity *)
Theorem T9 : forall x, (exists z, Ps z x) -> P x x.
Proof.
  intros x zPszx.
  apply A4 in zPszx as (s & Pssx & Fxs).
  exists s; split; auto.
Qed.

(* Parts <-> Slots *)
Theorem T11 : forall x, ((exists y, P y x) <-> (exists z, Ps z x)).
Proof.
  intros x; split.
  - intros (y & (s & Fys & Pssx)).
    exists s; auto.
  - intros (s & Pssx).
    pose proof (A7 _ _ Pssx) as (z & Fzs & _).
    exists z, s; split; auto.
Qed.

(* Composites <-> Slot-Composites *)
Theorem T12 : forall x, ((exists y, PP y x) <-> (exists z, PPs z x)).
Proof.
  intros x; split.
  - intros (y & (s & Fys & Pssx) & nPxy).
    exists s; split; auto.
    intros Fxs.
    destruct nPxy.
    pose proof (A7 _ _ Pssx) as (z & Fzs & UniqueFs).
    apply UniqueFs in Fxs as ->.
    apply UniqueFs in Fys as <-.
    exists s; auto.
  - intros (s & Pssx & nFxs).
    pose proof (A7 _ _ Pssx) as (y & Fys & _).
    exists y; split.
    exists s; auto.
    intros (t & Fxt & Psty).
    assert (x = y) as <- by (apply A6 with (z1:=t) (z2:=s); auto).
    contradiction.
Qed.

(* Slot Strong Supplementation *)
(* Not an axiom, but a theorem. See (Tarbouriech, 2023). *)
Theorem TA8 : forall x y,
  (exists z, Ps z x) /\ (exists z, Ps z y) ->
    ((~exists z, Ps z x /\ F y z) ->
      (exists z, Ps z y /\ ~Ps z x)).
Proof.
  intros x y (z1Psz1x & z2Psz2y) notPyx.
  apply A4 in z2Psz2y as (z3 & Psz3y & Fyz3).
  exists z3; split; trivial.
  intros Psz3x.
  destruct notPyx.
  exists z3; split; auto.
Qed.

(* Slot Weak Supplementation *)
Theorem T13 : forall x y, PP x y -> (exists z, Ps z y /\ ~ Ps z x).
Proof.
  intros x y ((s & Fxs & Pssy) & nPyx).
  pose proof (A4 y (ex_intro _ s Pssy)) as (t & Psty & Fyt).
  exists t; split; auto.
  intros Pstx.
  destruct nPyx.
  exists t; split; auto.
Qed.

(* Slot Extensionality *)
(* Not a theorem. See (Garbacz, 2016). *)
(* Theorem T14 : forall x y,
  ((exists z, PP z x) \/ (exists z, PP z y)) ->
    ((x = y) <->
      (forall z, PPs z x <-> PPs z y)).*)
