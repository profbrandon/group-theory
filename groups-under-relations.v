

(*==============================================================================*)
(* Utility                                                                      *)
(*==============================================================================*)

Definition app {A : Type} {B : A -> Type} (f : forall x : A, B x) (a : A) := f a.

Notation "f @ a" := (app f a) (at level 101, left associativity, only parsing).
Notation "f $ a" := (app f a) (at level 102, right associativity, only parsing).



Definition exT_implies_ex {A : Type} {P : A -> Prop}

  : {x : A & P x} -> exists x : A, P x

:=
  fun e =>
    match e with
    | existT _ x p => ex_intro _ x p
    end.



Definition fun_id {A : Type} : A -> A := fun a => a.



Fixpoint repeat {A : Type} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | 0    => fun_id
  | S n' => fun x => repeat f n' (f x)
  end.



Lemma repeat_on_right {A : Type} (f : A -> A) (n : nat)

  : forall (x : A), repeat f (S n) x = f (repeat f n x).

Proof.
  induction n.
  - simpl; unfold fun_id.
    reflexivity.
  - simpl.
    exact (fun x => IHn (f x)).
Qed.



Lemma repeat_on_left {A : Type} (f : A -> A) (n : nat)

  : forall (x : A), repeat f (S n) x = repeat f n (f x).

Proof.
  auto.
Qed.



Definition neg : bool -> bool :=
  fun b => 
    match b with
    | true  => false
    | false => true
    end.



Lemma nat_peq_is_decidable

  : forall (n m : nat), n <> m \/ n = m.

Proof.
  induction n.
  destruct m.
  - right; trivial.
  - left; discriminate.
  - destruct m.
    + left; discriminate.
    + destruct (IHn m).
      * left; exact (not_eq_S n m H).
      * right; exact (f_equal S H).
Qed.



Fixpoint nat_eq (n m : nat) : bool :=
  match n, m with
  | 0,   0     => true
  | 0,   S _   => false
  | S _, 0     => false
  | S n', S m' => nat_eq n' m'
  end.



Lemma nat_eq_refl (n : nat)

  : nat_eq n n = true.

Proof.
  induction n.
  - trivial.
  - simpl.
    exact IHn.
Qed.



Lemma nat_eq_reflect

  : forall (n m : nat), nat_eq n m = true <-> n = m.

Proof.
  intro n.
  induction n.
  intro m.
  - split.
    + destruct m; trivial.
      discriminate.
    + intro e; rewrite (eq_sym e).
      trivial.
  - intro m; split.
    + destruct m.
      * discriminate.
      * simpl; intro e.
        apply f_equal.
        destruct (IHn m) as (forward & _).
        exact (forward e).
    + destruct m.
      * discriminate.
      * simpl; intro e.
        injection e; intro e'.
        rewrite e'.
        exact (nat_eq_refl m).
Qed.



Lemma nat_eq_reflect_false

  : forall (n m : nat), nat_eq n m = false <-> n <> m.

Proof.
  intros n m.
  destruct (nat_eq_reflect n m) as (reflect_f & reflect_b).
  split.
  - unfold "<>".
    intros a b.
    rewrite a in reflect_b.
    discriminate (reflect_b b).
  - unfold "<>".
    intro z.
    induction (nat_eq n m).
    + exfalso; exact (z $ reflect_f $ eq_refl _).
    + reflexivity.
Qed.



Lemma none_less_than_zero

  : forall {n : nat}, ~(n < 0).

Proof.
  red in |-*; intros n e.
  unfold "<" in e.
  assert (exists k, 0 = S k).
  elim e.
  - exists n.
    reflexivity.
  - intros m l p.
    destruct p as (x & q).
    exists (S x).
    rewrite q; reflexivity.
  - destruct H.
    discriminate H.
Qed.



Lemma reduce_succ_lt

  : forall {n m : nat}, S n < S m -> n < m.

Proof.
  red in |-*; intros n m e.
  unfold "<" in e.
  inversion e.
  - exact (le_n (S n)).
  - set (le_S _ _ (le_n (S n))).
    elim H0.
    + exact l.
    + intros m' e1 e2.
      exact (le_S _ _ e2).
Qed.



Lemma apply_succ_lt

  : forall {n m : nat}, n < m -> S n < S m.

Proof.
  red in |-*; intros n m e.
  unfold "<" in e.
  inversion e.
  - exact (le_n (S (S n))).
  - elim H.
    + exact (le_S _ _ (le_n (S (S n)))).
    + intros m' e1 e2.
      exact (le_S _ _ e2).
Qed.



Lemma none_less_than_itself

  : forall {n : nat}, ~(n < n).

Proof.
  red in |-*; intros n e.
  induction n.
  - exact (none_less_than_zero e).
  - apply reduce_succ_lt in e.
    exact (IHn e).
Qed.



Lemma lt_trans

  : forall {n m k : nat}, n < m -> m < k -> n < k.

Proof.
  intros n m k e1 e2.
  elim e2.
  - exact (le_S _ _ e1).
  - intros m' e3 e4.
    exact (le_S _ _ e4).
Qed.



Lemma none_less_and_greater

  : forall {n m : nat}, (n < m) -> (m < n) -> False.

Proof.
  intros n m e e'.
  exact (none_less_than_itself (lt_trans e e')).
Qed.



Lemma split_le

  : forall {n m : nat}, n <= m -> (n < m \/ n = m).

Proof.
  intros.
  elim H.
  - right; reflexivity.
  - intros m' e' h.
    destruct h as [l | r].
    + left.
      apply apply_succ_lt in l.
      apply (fun z => lt_trans z l).
      exact (le_n (S n)).
    + left; rewrite r.
      exact (le_n (S m')).
Qed.



Lemma intro_lt

  : forall {n m : nat}, S n = m -> n < m.

Proof.
  intros n m e; unfold "<".
  rewrite e.
  exact (le_n _).
Qed.




(*==============================================================================*)
(* Equivalence Relation Definition                                              *)
(*==============================================================================*)

Class Equiv {A : Type} (R : A -> A -> Prop) :=
{
  refl  : forall (a : A), R a a;
  sym   : forall {x y : A}, R x y -> R y x;
  trans : forall {x y z : A}, R x y -> R y z -> R x z;

  rtrans := fun {x y z : A} (p : R y z) (q : R x y) => trans q p;

  lift_eq : forall {x y : A}, (x = y) -> R x y := fun x y => eq_ind x (fun z => R x z) (refl x) y;
}.





(*==============================================================================*)
(* Group Definition                                                             *)
(*==============================================================================*)

Class Group G (R : G -> G -> Prop) `{Equiv G R} :=
{
  (* elements/functions *)

  id   : G;
  mult : G -> G -> G;
  inv  : G -> G;


  (* derived notions *)

  eqv  : G -> G -> Prop := R;

  conj : G -> G -> G := fun g a => mult a (mult g (inv a));
  comm : G -> G -> G := fun a b => mult a (mult b (mult (inv a) (inv b)));

  actL : G -> G -> G := mult;
  actR : G -> G -> G := fun g a => mult a g;


  (* laws *)

  assoc : forall {a b c : G}, R (mult a (mult b c)) (mult (mult a b) c);
  
  left_id  : forall (g : G), R (mult id g) g;
  right_id : forall (g : G), R (mult g id) g;

  left_inv : forall (g : G), R (mult (inv g) g) id;


  (* coherence *)

  inv_well_def  : forall {g g' : G}, R g g' -> R (inv g) (inv g');
  mult_well_def : forall {a a' b b' : G}, R a a' -> R b b' -> R (mult a b) (mult a' b');
}.

Notation "x # y" := (mult x y) (at level 41, right associativity).
Notation "g *"   := (inv g) (at level 39).
Notation "x ~ y" := (eqv x y) (at level 71, no associativity).





(*==============================================================================*)
(* Basic Group Properties                                                       *)
(*==============================================================================*)

Lemma inv_id {G : Type} {R : G -> G -> Prop} `{Group G R}

  : id* ~ id.

Proof.
  apply (trans $ sym $ right_id $ id*).
  apply (trans $ left_inv id).
  exact (refl id).
Qed.



Lemma idempot_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : (g*)* ~ g.

Proof.
  apply (trans $ sym $ right_id $ (g*)*).
  apply (trans $ sym $ mult_well_def (refl $ (g*)*) @ left_inv g).
  apply (trans assoc).
  apply (trans $ mult_well_def (left_inv $ g*) @ refl g).
  exact (left_id g).
Qed.



Lemma right_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : g # g* ~ id.

Proof.
  apply (rtrans $ left_inv $ g*).
  apply mult_well_def.
  - exact (sym $ idempot_inv g).
  - exact (refl $ g*).
Qed.



Lemma left_cancel {G : Type} {R : G -> G -> Prop} `{Group G R} (g a b : G)

  : g # a ~ g # b -> a ~ b.

Proof.
  intro e.
  apply (trans $ sym $ left_id a).
  apply (rtrans $ left_id b).
  apply (trans $ mult_well_def @ sym (left_inv g) @ refl a).
  apply (rtrans $ mult_well_def @ left_inv g @ refl b).
  apply (trans $ sym assoc).
  apply (rtrans assoc).
  apply mult_well_def.
  - exact (refl @ g*).
  - exact e.
Qed.



Lemma right_cancel {G : Type} {R : G -> G -> Prop} `{Group G R} (g a b : G)

  : a # g ~ b # g -> a ~ b.

Proof.
  intro e.
  apply (trans $ sym $ right_id a).
  apply (rtrans $ right_id b).
  apply (trans $ sym $ mult_well_def @ refl a @ right_inv g).
  apply (rtrans $ mult_well_def @ refl b @ right_inv g).
  apply (trans assoc).
  apply (rtrans $ sym assoc).
  apply mult_well_def.
  - exact e.
  - exact (refl (g*)).
Qed.



Lemma left_mult {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G) {a b : G}

  : a ~ b -> g # a ~ g # b.

Proof.
  intro p.
  apply (left_cancel @ g*).
  apply (trans assoc).
  apply (trans $ mult_well_def @ left_inv g @ refl a).
  apply (trans $ left_id a).
  apply (rtrans $ sym assoc).
  apply (rtrans $ sym $ mult_well_def @ left_inv g @ refl b).
  apply (rtrans $ sym $ left_id b).
  exact p.
Qed.



Lemma right_mult {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G) {a b : G}

  : a ~ b -> a # g ~ b # g.

Proof.
  intro p.
  apply (right_cancel @ g*).
  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl a @ right_inv g).
  apply (trans $ right_id a).
  apply (rtrans assoc).
  apply (rtrans $ sym $ mult_well_def @ refl b @ right_inv g).
  apply (rtrans $ sym $ right_id b).
  exact p.
Qed.



Lemma shift_left {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g # a ~ b -> a ~ g* # b.

Proof.
  intro p.
  apply (left_cancel g).
  apply (rtrans $ sym assoc).
  apply (rtrans $ sym $ mult_well_def @ right_inv g @ refl b).
  apply (rtrans $ sym $ left_id b).
  exact p.
Qed.



Lemma shift_left_inv {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g* # a ~ b -> a ~ g # b.

Proof.
  intro p.
  apply (rtrans $ mult_well_def @ idempot_inv g @ refl b).
  apply shift_left.
  exact p.
Qed.



Lemma shift_right {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g ~ b -> a ~ b # g*.

Proof.
  intro p.
  apply (right_cancel g).
  apply (rtrans assoc).
  apply (rtrans $ sym $ mult_well_def @ refl b @ left_inv g).
  apply (rtrans $ sym $ right_id b).
  exact p.
Qed.



Lemma shift_right_inv {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g* ~ b -> a ~ b # g.

Proof.
  intro p.
  apply (rtrans $ mult_well_def @ refl b @ idempot_inv g).
  apply shift_right.
  exact p.
Qed.



Lemma simpl_left_inv_left {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g* # g # a ~ b -> a ~ b.

Proof.
  intro p.
  apply (left_cancel g).
  apply shift_left_inv.
  exact p.
Qed.



Lemma simpl_left_inv_right {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g* # g ~ b -> a ~ b.

Proof.
  intro p.
  apply (right_cancel @ g*).
  apply shift_right_inv.
  apply (trans $ mult_well_def @ refl _ @ idempot_inv g).
  apply (trans $ sym assoc).
  exact p.
Qed.



Lemma simpl_right_inv_left {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : g # g* # a ~ b -> a ~ b.

Proof.
  intro p.
  apply (left_cancel @ g*).
  apply shift_left.
  exact p.
Qed.



Lemma simpl_right_inv_right {G : Type} {R : G -> G -> Prop} `{Group G R} {g a b : G}

  : a # g # g* ~ b -> a ~ b.

Proof.
  intro p.
  apply (right_cancel g).
  apply shift_right_inv.
  apply (trans $ sym assoc).
  exact p.
Qed.



Lemma injective_inv {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall (a b : G), a* ~ b* -> a ~ b.

Proof.
  intros a b e.
  apply (trans $ sym $ idempot_inv a).
  apply (rtrans $ idempot_inv b).
  apply inv_well_def.
  exact e.
Qed.



Lemma inv_mult {G : Type} {R : G -> G -> Prop} `{Group G R} (g h : G)

  : (g # h)* ~ h* # g*.

Proof.
  apply (right_cancel @ g # h).
  apply (trans $ left_inv $ g # h).
  apply (rtrans assoc).
  apply shift_left.
  apply (trans $ right_id h).
  apply (trans $ sym $ left_id h).
  apply (rtrans $ sym $ assoc).
  apply mult_well_def.
  exact (sym $ left_inv g).
  exact (refl h).
Qed.



Lemma unique_left_id {G : Type} {R : G -> G -> Prop} `{Group G R} (e : G)

  : (forall (g : G), e # g ~ g) -> id ~ e.

Proof.
  intro l_id_cond.
  apply (trans $ sym $ l_id_cond id).
  exact (right_id e).
Qed.



Lemma unique_right_id {G : Type} {R : G -> G -> Prop} `{Group G R} (e : G)

  : (forall (g : G), e # g ~ g) -> id ~ e.

Proof.
  intro r_id_cond.
  apply (trans $ sym $ r_id_cond id).
  exact (right_id e).
Qed.



Lemma unique_left_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : forall (i : G), i # g ~ id -> i ~ g*.

Proof.
  intros i l_inv_cond.
  apply (right_cancel g).
  apply (rtrans $ sym $ left_inv g).
  exact l_inv_cond.
Qed.



Lemma unique_right_inv {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : forall (i : G), g # i ~ id -> i ~ g*.

Proof.
  intros i r_inv_cond.
  apply (left_cancel g).
  apply (rtrans $ sym $ right_inv g).
  exact r_inv_cond.
Qed.



Lemma conj_id {G : Type} {R : G -> G -> Prop} `{Group G R} (g : G)

  : conj g id ~ g.

Proof.
  unfold conj.
  apply (trans $ left_id _).
  apply sym.
  apply shift_right.
  exact (right_id g).
Qed.



Lemma double_conj {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall a b g : G, conj (conj g b) a ~ conj g (a # b).

Proof.
  intros.
  unfold conj.
  apply (trans assoc).
  apply (trans $ mult_well_def @ assoc @ refl _).
  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl _ @ sym assoc).
  apply (trans $ sym $ mult_well_def @ refl _ $ mult_well_def @ refl _ @ inv_mult a b).
  exact (refl _).
Qed.



Lemma conj_well_def {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall {g a g' a' : G}, g ~ g' -> a ~ a' -> conj g a ~ conj g' a'.

Proof.
  intros g a g' a' e1 e2.
  unfold conj.
  apply (mult_well_def e2).
  apply (fun e => mult_well_def e @ inv_well_def e2).
  exact e1.
Qed.



Lemma conj_inv {G : Type} {R : G -> G -> Prop} `{Group G R}

  : forall a b : G, conj (conj a b) (b*) ~ a.

Proof.
  intros.
  apply (trans $ double_conj (b*) b a).
  apply (trans $ conj_well_def @ refl a @ left_inv b).
  exact (conj_id a).
Qed.





(*==============================================================================*)
(* Subroups                                                                     *)
(*==============================================================================*)

Definition Sub (G : Type) (P : G -> Prop) := {x : G & P x}.



Class Subgroup (G : Type) (R : G -> G -> Prop) (P : G -> Prop) `{Group G R} :=
{
  contains_id : P id;

  closed_under_equiv : forall (a b : G), (a ~ b) -> P a -> P b;

  closed_under_mult : forall (a b : G), P a -> P b -> P (a # b);

  closed_under_inv : forall (a : G), P a -> P (a*);
}.



Definition subgroup_equiv {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Subgroup G R P}

  : Sub G P -> Sub G P -> Prop

:= 
  fun a b => 
    match a with
    | existT _ u _ => 
      match b with
      | existT _ v _ => R u v
      end
    end.



Lemma subgroup_equiv_refl {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (s : Sub G P), subgroup_equiv R P s s.

Proof.
  intro.
  destruct s.
  unfold subgroup_equiv.
  exact (refl x).
Qed.



Lemma subgroup_equiv_sym {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (s s' : Sub G P), subgroup_equiv R P s s' -> subgroup_equiv R P s' s.

Proof.
  intros s s' e.
  destruct s, s'.
  unfold subgroup_equiv in e.
  unfold subgroup_equiv.
  exact (sym e).
Qed.



Lemma subgroup_equiv_trans {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (s t u : Sub G P), subgroup_equiv R P s t -> subgroup_equiv R P t u -> subgroup_equiv R P s u.

Proof.
  intros s t u e1 e2.
  destruct s, t, u.
  unfold subgroup_equiv in e1, e2.
  unfold subgroup_equiv.
  exact (trans e1 e2).
Qed.



Instance subgroup_equiv_is_equiv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Equiv (subgroup_equiv R P)

:=
{
  refl  := subgroup_equiv_refl;
  sym   := subgroup_equiv_sym;
  trans := subgroup_equiv_trans;
}.



Definition subgroup_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P

:= existT _ @ id @ contains_id.



Definition subgroup_mult {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P -> Sub G P -> Sub G P

:= 
  fun a b => 
    match a with
    | existT _ u p =>
      match b with
      | existT _ v q =>
          existT _ 
            @ u # v 
            $ closed_under_mult u v p q
      end
    end.



Lemma subgroup_mult_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a a' b b' : Sub G P), let R' := subgroup_equiv R P in

      R' a a' -> R' b b' -> R' (subgroup_mult a b) (subgroup_mult a' b').

Proof.
  intros a a' b b' R' e1 e2.
  destruct a, a', b, b'.
  unfold subgroup_mult, R', subgroup_equiv.
  simpl.
  unfold R', subgroup_equiv in e1, e2.
  exact (mult_well_def e1 e2).
Qed.



Lemma subgroup_mult_assoc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a b c : Sub G P), 
      let m  := subgroup_mult  in
      let R' := subgroup_equiv R P in

      R' (m a (m b c)) (m (m a b) c).

Proof.
  intros a b c m R'.
  destruct a, b, c.
  unfold subgroup_mult, m, R', subgroup_equiv.
  simpl.
  exact assoc.
Qed.



Lemma subgroup_left_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), subgroup_equiv R P (subgroup_mult subgroup_id g) g.

Proof.
  intro.
  destruct g.
  unfold subgroup_equiv, subgroup_mult, subgroup_id.
  simpl.
  exact (left_id x).
Qed.



Lemma subgroup_right_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), subgroup_equiv R P (subgroup_mult g subgroup_id) g.

Proof.
  intro.
  destruct g.
  unfold subgroup_equiv, subgroup_mult, subgroup_id.
  simpl.
  exact (right_id x).
Qed.



Definition subgroup_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P -> Sub G P

:=
  fun a =>
    match a with
    | existT _ u p =>
        existT _
          @ u*
          @ closed_under_inv u p
    end.



Lemma subgroup_inv_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a a' : Sub G P), subgroup_equiv R P a a' -> subgroup_equiv R P (subgroup_inv a) (subgroup_inv a').

Proof.
  intros a a' e.
  destruct a, a'.
  unfold subgroup_equiv, subgroup_inv.
  simpl.
  unfold subgroup_equiv, subgroup_inv in e.
  exact (inv_well_def e).
Qed.



Lemma subgroup_left_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), subgroup_equiv R P (subgroup_mult (subgroup_inv g) g) subgroup_id.

Proof.
  intro.
  destruct g.
  unfold subgroup_equiv, subgroup_mult, subgroup_inv, subgroup_id.
  simpl.
  exact (left_inv x).
Qed.



Instance subgroup_is_group {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Subgroup G R P}

  : Group (Sub G P) (subgroup_equiv R P)

:=
{
  id   := subgroup_id;
  mult := subgroup_mult;
  inv  := subgroup_inv;

  assoc := subgroup_mult_assoc;

  left_id  := subgroup_left_id;
  right_id := subgroup_right_id;

  left_inv := subgroup_left_inv;

  mult_well_def := subgroup_mult_well_def;
  inv_well_def  := subgroup_inv_well_def;
}.



Definition inc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : Sub G P -> G

:= 
  fun p =>
    match p with
    | existT _ u _ => u
    end.

Notation "[ g ]" := (inc g).



Lemma subgroup_inc_preserves_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P),  [g*] ~ [g]*.

Proof.
  intro.
  destruct g.
  simpl.
  exact (refl _).
Qed.



Lemma subgroup_inc_preserves_mult {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (a b : Sub G P), [a # b] ~ [a] # [b].

Proof.
  intros.
  destruct a, b.
  simpl.
  exact (refl _).
Qed.



Lemma subgroup_closed_under_inv_inc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Subgroup G R P}

  : forall (g : Sub G P), P [g*] <-> P ([g]*).

Proof.
  intro g.
  destruct g.
  simpl.
  split.
  - trivial.
  - trivial.
Qed.



Class Normal (G : Type) (R : G -> G -> Prop) (P : G -> Prop) `{Subgroup G R P} :=
{
  closed_under_conj : forall (n : G), P n -> forall (g : G), P (conj n g);
}.





(*==============================================================================*)
(* Quotient Groups                                                              *)
(*==============================================================================*)

Definition normal_equiv {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Normal G R P}

  : G -> G -> Prop

:= 
  fun g g' => 
    exists (n n' : Sub G P), g # [n] ~ g' # [n'].



Lemma normal_equiv_refl {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (g : G), normal_equiv R P g g.

Proof.
  intro.
  exists id.
  exists id.
  exact (refl _).
Qed.



Lemma normal_equiv_sym {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a b : G), let N := normal_equiv R P in

      N a b -> N b a.

Proof.
  intros a b N.
  unfold normal_equiv in N.
  unfold N.
  simpl.
  intro e.
  destruct e, H3.
  exists x0, x.
  exact (sym H3).
Qed.



Lemma normal_equiv_trans {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a b c : G), let N := normal_equiv R P in 

      N a b -> N b c -> N a c.

Proof.
  intros a b c.
  simpl.
  intros e1 e2.
  destruct e1, e2.
  destruct H3, H4.
  unfold normal_equiv.
  exists (x # x1*).
  exists (x2 # x0*).
  destruct x, x0, x1, x2.
  simpl.
  simpl in H3, H4.
  apply (trans assoc).
  apply (rtrans $ sym $ assoc).
  apply (trans $ mult_well_def H3 $ refl $ x1*).
  apply (rtrans $ mult_well_def H4 $ refl $ x0*).
  apply (trans $ sym $ assoc).
  apply (rtrans assoc).
  apply mult_well_def.
  - exact (refl b).
  - exact (trans @ right_inv x1 @ sym (right_inv x0)).
Qed.



Instance normal_equiv_is_equiv {G : Type} (R : G -> G -> Prop) (P : G -> Prop) `{Normal G R P}

  : Equiv (normal_equiv R P)

:=
{
  refl  := normal_equiv_refl;
  sym   := normal_equiv_sym;
  trans := normal_equiv_trans;
}.



Lemma normal_equiv_assoc {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a b c : G), let N := normal_equiv R P in

      N (a # (b # c)) ((a # b) # c).

Proof.
  intros.
  unfold N, normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  exact assoc.
  exact (refl id).
Qed.



Lemma normal_equiv_left_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a : G), normal_equiv R P (id # a) a.

Proof.
  intro a.
  unfold normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  - exact (left_id a).
  - exact (refl id).
Qed.



Lemma normal_equiv_right_id {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a : G), normal_equiv R P (a # id) a.

Proof.
  intro a.
  unfold normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  - exact (right_id a).
  - exact (refl id).
Qed.



Lemma normal_equiv_left_inv {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a : G), normal_equiv R P (a* # a) id.

Proof.
  intro a.
  unfold normal_equiv.
  exists subgroup_id, subgroup_id.
  simpl.
  apply mult_well_def.
  - exact (left_inv a).
  - exact (refl id).
Qed.



Lemma normal_equiv_mult_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a a' b b' : G), let N := normal_equiv R P in

      N a a' -> N b b' -> N (a # b) (a' # b').

Proof.
  intros a a' b b'.
  simpl.
  intros e1 e2.
  destruct e1, e2, H3, H4.
  unfold normal_equiv.
  set (u  := [x0] # [x2]*).
  set (u' := conj ([x1] # [x]*) (b' *)).
  destruct x, x0, x1, x2.
  simpl in H3, H4, u, u'.
  set (q := closed_under_mult x0 (x2*) p0 (closed_under_inv x2 p2)).
  exists (existT _ u q).
  set (q' := closed_under_conj (x1 # x*) (closed_under_mult x1 (x*) p1 (closed_under_inv x p)) (b' *)).
  exists (existT _ u' q').
  simpl.
  unfold u, u', conj.

  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl a @ assoc).
  apply (trans $ mult_well_def @ refl a $ mult_well_def @ H4 @ refl (x2*)).
  apply (trans $ sym $ mult_well_def @ refl a @ assoc).
  apply (trans assoc).
  apply (trans $ mult_well_def @ refl _ @ right_inv x2).
  apply (trans $ right_id _).
  apply (rtrans $ sym $ assoc).
  apply (rtrans $ sym $ assoc).
  apply shift_right.
  apply (trans $ sym assoc).
  apply (trans $ mult_well_def @ refl a @ right_inv b').
  apply (trans $ right_id a).
  apply (rtrans $ sym assoc).
  apply shift_right.
  apply (trans H3).
  apply mult_well_def.
  - apply (rtrans assoc).
    apply (rtrans $ sym $ mult_well_def @ refl a' @ right_inv b').
    exact (sym $ right_id a').
  - exact (refl x1).
Qed.



Lemma normal_equiv_inv_well_def {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : forall (a a' : G), let N := normal_equiv R P in

      N a a' -> N (a*) (a'*).

Proof.
  intros a a'.
  simpl.
  intro e.
  destruct e, H3.
  unfold normal_equiv.
  set (u  := a # [x]* # a*).
  set (u' := a' # [x0]* # a'*).
  destruct x, x0.
  simpl in H3, u, u'.
  set (q  := closed_under_conj (x*) (closed_under_inv x p) a).
  set (q' := closed_under_conj (x0*) (closed_under_inv x0 p0) a').
  exists (existT _ u q).
  exists (existT _ u' q').
  unfold u, u', q, q'; simpl.
  apply (trans assoc).
  apply (rtrans $ sym assoc).
  apply mult_well_def.
  - exact (trans @ left_inv a @ (sym @ left_inv a')).
  - apply (trans $ sym $ inv_mult _ _).
    apply (rtrans $ inv_mult _ _).
    apply inv_well_def.
    exact H3.
Qed.



Definition Quotient (G : Type) (R : G -> G -> Prop) (P : G -> Prop) `{Normal G R P}

  := G.



Instance quotient_group {G : Type} {R : G -> G -> Prop} {P : G -> Prop} `{Normal G R P}

  : @Group (Quotient G R P) (normal_equiv R P) (normal_equiv_is_equiv R P)

:=
{
  id  := id;
  inv := inv;
  mult := mult;

  assoc := normal_equiv_assoc;

  left_id  := normal_equiv_left_id;
  right_id := normal_equiv_right_id;

  left_inv := normal_equiv_left_inv;

  inv_well_def := normal_equiv_inv_well_def;
  mult_well_def := normal_equiv_mult_well_def;
}.



(*==============================================================================*)
(* Group Homomorphisms                                                          *)
(*==============================================================================*)

Class GrpHom {G G' : Type} (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{Group G R, Group G' R'}
:=
{
  (* conditions *)

  hom_well_def : forall {a b : G}, a ~ b -> h a ~ h b;

  preserves_id : h id ~ id;

  break : forall {a b : G}, h (a # b) ~ h a # h b;
}.



Definition dom {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}
  := G.



Definition cod {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h} 
  := G'.



Lemma hom_preserves_inv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (x : G), h (x*) ~ (h x)*.

Proof.
  intro.
  apply (right_cancel @ h x).
  apply (rtrans $ sym $ left_inv _).
  apply (trans $ sym $ break).
  apply (rtrans $ preserves_id).
  apply hom_well_def.
  exact (left_inv x).
Qed.



Definition is_in_image {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : G' -> Prop

:= fun g' => exists g : G, h g ~ g'.



Definition image {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := Sub G' (is_in_image h).



Lemma image_contains_images {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall g : G, is_in_image h (h g).

Proof.
  intro g.
  exists g.
  exact (refl @ h g).
Qed.



Lemma image_contains_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : is_in_image h id.

Proof.
  unfold is_in_image.
  exists id.
  exact preserves_id.
Qed.



Lemma image_closed_under_equiv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a b : G'), a ~ b -> is_in_image h a -> is_in_image h b.

Proof.
  intros a b p.
  unfold is_in_image.
  intro i.
  destruct i.
  exists x.
  apply (rtrans p).
  exact H4.
Qed.



Lemma image_closed_under_mult {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a b : G'), is_in_image h a -> is_in_image h b -> is_in_image h (a # b).

Proof.
  intros a b.
  unfold is_in_image.
  intros ia ib.
  destruct ia, ib.
  exists (x # x0).
  apply (trans break).
  apply mult_well_def.
  - exact H4.
  - exact H5.
Qed.



Lemma image_closed_under_inv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a : G'), is_in_image h a -> is_in_image h (a*).

Proof.
  intro a.
  unfold is_in_image.
  intros i.
  destruct i.
  exists (x*).
  apply (trans $ hom_preserves_inv h x).
  apply inv_well_def.
  exact H4.
Qed.



Instance image_is_subgroup {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : Subgroup G' R' (is_in_image h)

:=
{
  contains_id        := image_contains_id h;

  closed_under_equiv := image_closed_under_equiv h;
  closed_under_mult  := image_closed_under_mult h;
  closed_under_inv   := image_closed_under_inv h;
}.



Definition restrict_cod {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : G -> image h

:= 
  fun g : G => 
    existT (fun x => is_in_image h x)
      @ h g 
      @ image_contains_images h g.



Lemma restrict_cod_preserves_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : subgroup_equiv R' (is_in_image h) (restrict_cod h id) subgroup_id.

Proof.
  unfold subgroup_equiv, is_in_image, restrict_cod, subgroup_id.
  simpl.
  exact preserves_id.
Qed.



Lemma restrict_cod_break {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let S  := subgroup_equiv R' (is_in_image h) in
    let h' := restrict_cod h in

    forall (x y : G), S (h' (x # y)) (subgroup_mult (h' x) (h' y)).

Proof.
  intros.
  unfold S, h', subgroup_equiv, is_in_image, restrict_cod, subgroup_mult; simpl.
  exact break.
Qed.



Lemma restrict_cod_well_def {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let S  := subgroup_equiv R' (is_in_image h) in
    let h' := restrict_cod h in

    forall (x y : G), x ~ y -> S (h' x) (h' y).

Proof.
  intros S h' x y p.
  unfold S, h', subgroup_equiv, is_in_image, restrict_cod, subgroup_mult; simpl.
  exact (hom_well_def p).
Qed.



Instance restrict_cod_is_hom {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : @GrpHom G (image h) R (subgroup_equiv R' (is_in_image h)) (restrict_cod h) 
      H 
      H0 
      subgroup_equiv_is_equiv 
      (subgroup_is_group R' (is_in_image h))

:= 
{
  hom_well_def := @restrict_cod_well_def G G' R R' h H H0 H1 H2 H3;
  preserves_id  := @restrict_cod_preserves_id G G' R R' h H H0 H1 H2 H3;
  break        := @restrict_cod_break G G' R R' h H H0 H1 H2 H3;
}.



Definition is_in_kernel {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : G -> Prop

:= fun g => h g ~ id.



Definition kernel {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := Sub G (is_in_kernel h).



Lemma kernel_contains_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : is_in_kernel h id.

Proof.
  unfold is_in_kernel.
  exact preserves_id.
Qed.



Lemma kernel_closed_under_equiv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall {a b : G}, a ~ b -> is_in_kernel h a -> is_in_kernel h b.

Proof.
  intros a b p.
  unfold is_in_kernel.
  intro e.
  apply sym.
  apply (trans $ sym e).
  apply hom_well_def.
  exact p.
Qed.



Lemma kernel_closed_under_mult {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall {a b : G}, is_in_kernel h a -> is_in_kernel h b -> is_in_kernel h (a # b).

Proof.
  intros a b.
  unfold is_in_kernel.
  intros e1 e2.
  apply (rtrans $ left_id id).
  apply (rtrans $ mult_well_def e1 e2).
  exact break.
Qed.



Lemma kernel_closed_under_inv {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall {a : G}, is_in_kernel h a -> is_in_kernel h (a*).

Proof.
  intro a.
  unfold is_in_kernel.
  intro e.
  apply (trans $ hom_preserves_inv h a).
  apply (rtrans inv_id).
  apply inv_well_def.
  exact e.
Qed.



Instance kernel_is_subgroup {G G' : Type} (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{GrpHom G G' R R' h}

  : Subgroup G R (is_in_kernel h)

:=
{
  contains_id := kernel_contains_id h;

  closed_under_equiv := @kernel_closed_under_equiv G G' R R' h H H0 H1 H2 H3;
  closed_under_mult  := @kernel_closed_under_mult G G' R R' h H H0 H1 H2 H3;
  closed_under_inv   := @kernel_closed_under_inv G G' R R' h H H0 H1 H2 H3;
}.



Lemma kernel_closed_under_conj {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : forall (a : G), is_in_kernel h a -> forall (g : G), is_in_kernel h (conj a g).

Proof.
  unfold is_in_kernel.
  intros a p g.
  unfold conj.
  apply (trans break).
  apply (trans $ mult_well_def @ refl (h g) @ break).
  apply (trans $ mult_well_def @ refl (h g) $ mult_well_def @ p @ refl _).
  apply (trans $ mult_well_def @ refl (h g) $ left_id _).
  apply (trans $ mult_well_def @ refl (h g) @ hom_preserves_inv h g).
  exact (right_inv _).
Qed.



Instance kernel_is_normal {G G' : Type} (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{GrpHom G G' R R' h}

  : Normal G R (is_in_kernel h)

:=
{
  closed_under_conj := kernel_closed_under_conj h;
}.



Definition hom_equiv {G G' : Type} (R : G -> G -> Prop) {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := normal_equiv R (is_in_kernel h).



Instance hom_equiv_is_equiv {G G' : Type} (R : G -> G -> Prop) {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : Equiv (hom_equiv R h)

:= normal_equiv_is_equiv R (is_in_kernel h).



Definition HomQuotient {G G' : Type} (R : G -> G -> Prop) {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  := @Quotient G R (is_in_kernel h) 
        H 
        H0 
        (kernel_is_subgroup R R' h) 
        (kernel_is_normal R R' h).





(*==============================================================================*)
(* First Isomorphism Theorem                                                    *)
(*==============================================================================*)

Class GrpAut (G G' : Type) (R : G -> G -> Prop) (R' : G' -> G' -> Prop) (h : G -> G') `{GrpHom G G' R R' h} :=
{
  injective : forall {x y : G}, h x ~ h y -> x ~ y;

  surjective : forall z : G', exists x : G, h x ~ z;
}.



Lemma group_aut_kernel_is_unitary {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpAut G G' R R' h}

  : forall x : G, is_in_kernel h x -> x ~ id.

Proof.
  unfold is_in_kernel.
  intros x p.
  apply injective.
  apply (rtrans $ sym $ preserves_id).
  exact p.
Qed.



Definition isomorphic (G : Type) (R : G -> G -> Prop) (G' : Type) (R' : G' -> G' -> Prop) `{Group G R, Group G' R'}

  := {h : G -> G' & {e : GrpHom R R' h & GrpAut G G' R R' h}}.



Lemma quotient_to_image_well_def {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    forall (x y : G), K x y -> S (h' x) (h' y).

Proof.
  intros h' K S x y p.
  unfold S, subgroup_equiv.
  simpl.
  apply (right_cancel id).
  unfold K, hom_equiv, normal_equiv, is_in_kernel, Sub in p.
  destruct p, x0, H4, x1.
  simpl in H4.
  apply (trans $ sym $ mult_well_def @ refl (h x) @ e).
  apply (rtrans $ mult_well_def @ refl (h y) @ e0).
  apply (trans $ sym break).
  apply (rtrans break).
  exact (hom_well_def H4).
Qed.



Lemma quotient_to_image_preserves_id {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let S := subgroup_equiv R' (is_in_image h) in

    S (h' id) subgroup_id.

Proof.
  intros h' S.
  unfold S, subgroup_equiv, subgroup_id, restrict_cod; simpl.
  exact preserves_id.
Qed.



Lemma quotient_to_image_break {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let S  := subgroup_equiv R' (is_in_image h) in
    let m  := subgroup_mult in

    forall (x y : G), S (h' (x # y)) (m (h' x) (h' y)).

Proof.
  intros h' S m x y.
  unfold S, h', m, subgroup_equiv, subgroup_mult, restrict_cod; simpl.
  exact break.
Qed.



Instance quotient_to_image_is_hom {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : GrpHom (hom_equiv R h) (subgroup_equiv R' (is_in_image h)) (restrict_cod h)

:=
{
  hom_well_def := @quotient_to_image_well_def G G' R R' h H H0 H1 H2 H3;
  preserves_id := @quotient_to_image_preserves_id G G' R R' h H H0 H1 H2 H3;
  break        := @quotient_to_image_break G G' R R' h H H0 H1 H2 H3;
}.



Lemma quotient_to_image_injective {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    forall (x y : G), S (h' x) (h' y) -> K x y.

Proof.
  intros h' K p x y.
  unfold h', K, hom_equiv, subgroup_equiv; simpl.
  intro q.
  unfold normal_equiv, is_in_kernel, Sub.
  assert (is_in_kernel h (x* # y)).
  - unfold is_in_kernel.
    apply (trans break).
    apply (trans $ mult_well_def @ hom_preserves_inv h x @ refl (h y)).
    apply (trans $ mult_well_def @ (inv_well_def q) @ refl (h y)).
    exact (left_inv _).
  - exists (existT _ (x* # y) H4).
    exists (existT _ id (kernel_contains_id h)).
    simpl.
    apply (rtrans $ sym $ right_id y).
    apply (trans assoc).
    apply (trans $ mult_well_def @ right_inv x @ refl y).
    exact (left_id y).
Qed.



Lemma quotient_to_image_surjective {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    forall (z : image h), exists x : G, S (h' x) z.

Proof.
  intros h' K S z.
  destruct z, i; simpl.
  exists x0.
  exact e.
Qed.



Instance quotient_to_image_is_aut {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : GrpAut G (image h) (hom_equiv R h) (subgroup_equiv R' (is_in_image h)) 
      (restrict_cod h)

:=
{
  injective  := quotient_to_image_injective h;
  surjective := quotient_to_image_surjective h;
}.



Theorem first_iso_theorem {G G' : Type} {R : G -> G -> Prop} {R' : G' -> G' -> Prop} (h : G -> G') `{GrpHom G G' R R' h}

  : let h' := restrict_cod h in
    let K  := hom_equiv R h  in
    let S  := subgroup_equiv R' (is_in_image h) in

    isomorphic 
      (HomQuotient R h) K 
      (image h) S.

Proof.
  intros h' K S.
  unfold isomorphic.
  unfold HomQuotient.
  unfold Quotient.
  exists h'.
  exists (quotient_to_image_is_hom h).
  exact (quotient_to_image_is_aut h).
Qed.





(*==============================================================================*)
(* Generators for Free Groups                                                   *)
(*==============================================================================*)

Inductive Generators (n : nat) : Type :=
  | gen       : forall k : nat, k < n -> Generators n
  | inv_gen   : forall k : nat, k < n -> Generators n.



Definition gen_label {n : nat}

  : Generators n -> nat

:=
  fun g =>
    match g with
    | gen     _ k _ => k
    | inv_gen _ k _ => k
    end.



Notation "# g" := (gen_label g) (at level 26, no associativity).



Lemma no_zero_generators :

  Generators 0 -> False.

Proof.
  intro g; destruct g.
  - exact (none_less_than_zero l).
  - exact (none_less_than_zero l).
Qed.



Definition gen_equiv_0

  : Generators 0 -> Generators 0 -> Prop

:= fun _ _ => True.



Definition gen_equiv (n : nat)

  : Generators n -> Generators n -> Prop

:=
  match n with
  | 0   => gen_equiv_0
  | S n =>

    fun g g' =>
      match g, g' with
      | gen     _ x _, gen     _ y _ => x = y
      | gen     _ _ _, inv_gen _ _ _ => False
      | inv_gen _ x _, inv_gen _ y _ => x = y
      | inv_gen _ _ _, gen     _ _ _ => False
      end
  end.



Lemma gen_equiv_production {n : nat}

  : forall (k k' : nat) (l : k < n) (l' : k' < n),

      k = k' -> (gen_equiv n (gen n k l) (gen n k' l')) /\ (gen_equiv n (inv_gen n k l) (inv_gen n k' l')).

Proof.
  intros k k' l l' e.
  induction e.
  induction n.
  - simpl; unfold gen_equiv_0; auto.
  - simpl; auto.
Qed.



Lemma gen_equiv_reduction {n : nat}

  : forall (g h : Generators n), gen_equiv n g h -> #g = #h.

Proof.
  induction n.
  - intros g h.
    exfalso; exact (no_zero_generators g).
  - intros g h.
    destruct g, h.
    + simpl; trivial.
    + simpl; intro H; exfalso; exact H.
    + simpl; intro H; exfalso; exact H.
    + simpl; trivial.
Qed.



Lemma gen_equiv_fails_on_inv {n : nat}

  : forall (k k' : nat) (l : k < n) (l' : k' < n),

      ~(gen_equiv n (gen n k l) (inv_gen n k' l')).

Proof.
  induction n.
  - intros k k' l l' eqv.
    exact (none_less_than_zero l).
  - intros k k' l l' eqv.
    simpl in eqv; exact eqv.
Qed.



Lemma gen_equiv_refl (n : nat) (x : Generators n)

  : gen_equiv n x x.

Proof.
  induction n.
  - simpl; unfold gen_equiv_0; trivial.
  - induction x.
    * simpl; trivial.
    * simpl; trivial.
Qed.



Lemma gen_equiv_sym (n : nat) (x y : Generators n)

  : gen_equiv n x y -> gen_equiv n y x.

Proof.
  induction n.
  - simpl; unfold gen_equiv_0; trivial.
  - induction x, y; simpl in *.
    auto. auto. auto. auto.
Qed.



Lemma gen_equiv_trans (n : nat) (x y z : Generators n)

  : gen_equiv n x y -> gen_equiv n y z -> gen_equiv n x z.

Proof.
  induction n.
  - simpl; unfold gen_equiv_0; trivial.
  - induction x, y, z; simpl in *.
    * intros p q; exact (eq_trans p q).
    * trivial.
    * intros; exfalso; exact H.
    * trivial.
    * trivial.
    * intros; exfalso; exact H.
    * trivial.
    * intros p q; exact (eq_trans p q).
Qed.



Instance gen_equiv_is_equiv (n : nat)

  : Equiv (gen_equiv n)

:=
{
  refl  := gen_equiv_refl n;
  sym   := gen_equiv_sym n;
  trans := gen_equiv_trans n;
}.



Definition is_inverse_gen {n : nat}

  : Generators n -> Generators n -> Prop

:=
  fun a b =>
    match a, b with
    | gen     _ k _, inv_gen _ k' _ => k = k'
    | inv_gen _ k _, gen     _ k' _ => k = k'
    | _,             _              => False
    end.



Lemma is_inverse_gen_swap {n : nat}

  : forall {g h : Generators n}, is_inverse_gen g h -> is_inverse_gen h g.

Proof.
  intros g h inv.
  destruct g, h.
  - simpl in *. exact inv.
  - simpl in *. symmetry; exact inv.
  - simpl in *. symmetry; exact inv.
  - simpl in *. exact inv.
Qed.



Lemma is_inverse_gen_is_decidable {n : nat}

  : forall (g h : Generators n), ~(is_inverse_gen g h) \/ (is_inverse_gen g h).

Proof.
  induction g. destruct h.
  - simpl. auto.
  - simpl. exact (nat_peq_is_decidable k k0).
  - destruct h.
    + simpl. exact (nat_peq_is_decidable k k0).
    + simpl. auto.
Qed.



Definition inverse {n : nat}

  : Generators n -> Generators n

:=
  fun a =>
    match a with
    | gen     _ k e => inv_gen n k e
    | inv_gen _ k e => gen n k e
    end.



Lemma inverse_is_inverse_gen {n : nat}

  : forall (g : Generators n), is_inverse_gen g (inverse g).

Proof.
  induction g.
  - simpl; reflexivity.
  - simpl; reflexivity.
Qed.



Lemma unique_inverse_gen {n : nat}

  : forall {g h g' : Generators n}, 

    is_inverse_gen g h -> is_inverse_gen g' h -> gen_equiv n g g'.

Proof.
  intros g h g' inv1 inv2.
  destruct g, h.
  - simpl in inv1. exfalso; exact inv1.
  - simpl in inv1.
    induction inv1.
    destruct g'.
    + simpl in inv2.
      induction inv2.
      set (prod := gen_equiv_production k0 k0 l l1 eq_refl).
      exact (proj1 prod).
    + simpl in inv2. exfalso; exact inv2.
  - simpl in inv1.
    induction inv1.
    destruct g'.
    + simpl in inv2. exfalso; exact inv2.
    + simpl in inv2.
      induction inv2.
      set (prod := gen_equiv_production k0 k0 l l1 eq_refl).
      exact (proj2 prod).
  - simpl in inv1. exfalso; exact inv1.
Qed.



Lemma inverse_gen_respects_gen_equiv {n : nat}

  : forall {g g' h : Generators n}, 

      gen_equiv n g g' -> is_inverse_gen g h -> is_inverse_gen g' h.

Proof.
  intros g g' h eqv inv.
  destruct g, g', h.
  - simpl in *. exact inv.
  - simpl in *.
    apply gen_equiv_reduction in eqv; simpl in eqv.
    transitivity k. symmetry; exact eqv. exact inv.
  - simpl in *. exfalso; exact inv.
  - simpl in *. exact (gen_equiv_fails_on_inv _ _ _ _ eqv).
  - simpl in *. exact (gen_equiv_fails_on_inv _ _ _ _ (sym eqv)).
  - simpl in *. exfalso; exact inv.
  - simpl in *.
    apply gen_equiv_reduction in eqv; simpl in eqv.
    transitivity k.
    symmetry; exact eqv. exact inv.
  - simpl in *. exact inv.
Qed.





(*==============================================================================*)
(* Free Groups                                                                  *)
(*==============================================================================*)

Inductive FreeGroup (n : nat) :=
  | free_id  : FreeGroup n
  | free_con : Generators n -> FreeGroup n -> FreeGroup n.

Definition fid {n : nat} := free_id n.

Definition fcon {n : nat} := free_con n.



Definition invert {n : nat}

  : FreeGroup n -> FreeGroup n

:=
  fun zs =>
    let invert' : FreeGroup n -> (FreeGroup n -> FreeGroup n) :=
      fix invert'' g :=
        match g with
        | free_id  _      => fun_id
        | free_con _ x xs => fun z => invert'' xs @ (fcon (inverse x) z)
        end
    in invert' zs fid.



Definition singleton {n : nat}

  : Generators n -> FreeGroup n

:=
  fun g => fcon g fid.



Definition word_length {n : nat}

  : FreeGroup n -> nat

:=
  fix len g :=
    match g with
    | free_id _ => 0
    | free_con _ _ xs => S (len xs)
    end.



Corollary singleton_has_length_1 {n : nat}

  : forall (g : Generators n), word_length (singleton g) = 1.

Proof.
  intro g; simpl.
  reflexivity.
Qed.



Lemma word_length_s {n : nat}

  : forall (g : Generators n) (w : FreeGroup n), word_length (fcon g w) = S (word_length w).

Proof.
  auto.
Qed.





(*==============================================================================*)
(* Word Equivalence                                                             *)
(*==============================================================================*)

Definition strong_free_equiv {n : nat}

  : FreeGroup n -> FreeGroup n -> Prop

:=
  fix eq g h :=
    match g, h with
    | free_id  _     , free_id  _      => True
    | free_id  _     , _               => False
    | free_con _ _ _ , free_id  _      => False
    | free_con _ x xs, free_con _ y ys => (gen_equiv n x y) /\ eq xs ys
    end.



Lemma strong_free_equiv_refl {n : nat}

  : forall (g : FreeGroup n), strong_free_equiv g g.

Proof.
  induction g.
  - simpl; trivial.
  - simpl; split.
    + exact (gen_equiv_refl n g).
    + exact IHg.
Qed.



Lemma strong_free_equiv_sym {n : nat}

  : forall {g h : FreeGroup n}, 
      let E := strong_free_equiv in 

        E g h -> E h g.

Proof.
  induction g.
  - intros h E eqv; destruct h.
    + exact (strong_free_equiv_refl _).
    + simpl in eqv. exfalso; exact eqv.
  - intros h E eqv; destruct h.
    + simpl in eqv. exfalso; exact eqv.
    + simpl in eqv; simpl.
      split; destruct eqv.
      * exact (gen_equiv_sym n g g1 H).
      * exact (IHg h H0).
Qed.



Lemma strong_free_equiv_trans {n : nat}

  : forall {g h k : FreeGroup n},
      let E := strong_free_equiv in

        E g h -> E h k -> E g k.

Proof.
  induction g.
  - intros h k E eqv1 eqv2.
    destruct h.
    + exact eqv2.
    + simpl in eqv1.
      exfalso; exact eqv1.
  - intros h k E eqv1 eqv2.
    destruct h.
    + simpl in eqv1.
      exfalso; exact eqv1.
    + destruct k.
      * simpl in eqv2.
        exfalso; exact eqv2.
      * simpl in *.
        destruct eqv1, eqv2.
        split.
        exact (gen_equiv_trans n _ _ _ H H1).
        exact (IHg h k H0 H2).
Qed.



Instance strong_free_equiv_is_equiv {n : nat}

  : Equiv (@strong_free_equiv n)

:=
{
  refl  := @strong_free_equiv_refl n;
  sym   := @strong_free_equiv_sym n;
  trans := @strong_free_equiv_trans n;
}.



Lemma free_con_respects_strong_free_equiv {n : nat}

  : forall (x y : Generators n) {g h : FreeGroup n},
      let E := strong_free_equiv in

        gen_equiv n x y ->

          (E g h <-> E (fcon x g) (fcon y h)).

Proof.
  intros x y g h E ge.
  split.
  - intro eqv; simpl.
    split. exact ge. exact eqv.
  - intro eqv.
    simpl in eqv; destruct eqv as (_ & eqv').
    exact eqv'.
Qed.





(* free group normalized words *)

Definition normalized {n : nat}

  : FreeGroup n -> Prop

:=
  fix normal xs :=
    match xs with
    | free_id  _                           => True
    | free_con _ g (free_id _)             => True
    | free_con _ g (free_con _ h zs as ys) => ~(is_inverse_gen g h) /\ normal ys
    end.



Corollary fid_is_normal {n : nat}

  : normalized (free_id n).

Proof.
  simpl; trivial.
Qed.



Lemma children_are_normal {n : nat} {xs : FreeGroup n} {g : Generators n}

  : normalized (fcon g xs) -> normalized xs.

Proof.
  intro norm.
  induction xs.
  - trivial.
  - induction xs.
    + simpl; trivial.
    + simpl in norm.
      destruct norm.
      destruct H0.
      unfold normalized.
      split.
      * exact H0.
      * fold (normalized xs).
        exact H1.
Qed.



Lemma singleton_is_normalized {n : nat} (g : Generators n)

  : normalized (singleton g).

Proof.
  unfold singleton.
  simpl.
  trivial.
Qed.



Lemma extend_normalized {n : nat} {xs : FreeGroup n}

  : forall {g h : Generators n}, 

      ~(is_inverse_gen g h) -> normalized (fcon h xs) -> normalized (fcon g (fcon h xs)).

Proof.
  intro g.
  induction g.
  - intros h e norm.
    unfold normalized in *; simpl in *.
    split.
    + exact e.
    + exact norm.
  - intros h e norm.
    unfold normalized in *; simpl in *.
    split.
    + exact e.
    + exact norm.
Qed.



Lemma normalized_respects_strong_free_equiv {n : nat}

  : forall {g h : FreeGroup n},
      let E := strong_free_equiv in

        E g h -> normalized g -> normalized h.

Proof.
  induction g.
  - intros h E eqv norm.
    destruct h.
    + exact norm.
    + simpl in eqv.
      exfalso; exact eqv.
  - intros h E eqv norm.
    destruct h.
    + simpl in eqv.
      exfalso; exact eqv.
    + simpl in eqv.
      destruct eqv as (ge & eqv).
      set (IHg' := IHg h eqv (children_are_normal norm)).
      destruct h.
      * exact (singleton_is_normalized g1).
      * set (inv_dec := is_inverse_gen_is_decidable g1 g2).
        destruct inv_dec as [ninv | inv].
        -- exact (extend_normalized ninv IHg').
        -- set (inv' := inverse_gen_respects_gen_equiv (sym ge) inv).
          destruct g0.
          ++ simpl in eqv.
            exfalso; exact eqv.
          ++ simpl in eqv.
            destruct eqv as (ge' & eqv).
            set (inv'' := inverse_gen_respects_gen_equiv (sym ge') (is_inverse_gen_swap inv')).
            destruct norm as (ninv & norm').
            exfalso; exact (ninv (is_inverse_gen_swap inv'')).
Qed.




(* free group word reduction *)

Definition reduce1 {n : nat}

  : FreeGroup n -> FreeGroup n

:=
  fix red xs :=
    match xs with
    | free_id  _                           => xs
    | free_con _ g (free_id _)             => xs
    | free_con _ g (free_con _ h zs as ys) =>

      match g, h with
      | gen     _ k _, inv_gen _ k' _ => if nat_eq k k' then zs else fcon g (red ys)
      | inv_gen _ k _, gen     _ k' _ => if nat_eq k k' then zs else fcon g (red ys)
      | _            , _              => fcon g (red ys)
      end
    end.



Definition reduce {n : nat} (m : nat)

  : FreeGroup n -> FreeGroup n

:= repeat reduce1 m.



Lemma simpl_reduce1_on_inv {n : nat} {xs : FreeGroup n}

  : forall {g h : Generators n},

      is_inverse_gen g h -> 

        (reduce1 (fcon g (fcon h xs)) = xs).

Proof.
  induction g.
  - intros h inv.
    destruct h.
    + exfalso; simpl in inv; exact inv.
    + simpl in inv.
      induction inv.
      simpl.
      set (k_refl := nat_eq_refl k).
      symmetry in k_refl.
      induction k_refl.
      reflexivity.
  - intros h inv.
    destruct h.
    + simpl in inv.
      induction inv.
      simpl.
      set (k_refl := nat_eq_refl k).
      symmetry in k_refl.
      induction k_refl.
      reflexivity.
    + exfalso; simpl in inv; exact inv.
Qed.



Lemma pass_reduce1 {n : nat} (xs : FreeGroup n)

  : forall {g h : Generators n}, 

      ~(is_inverse_gen g h) -> (reduce1 (fcon g (fcon h xs)) = fcon g (reduce1 (fcon h xs))).

Proof.
  induction g.
  - intros h neq.
    destruct h.
    + simpl; reflexivity.
    + simpl in neq.
      set (ref_fls := nat_eq_reflect_false k k0).
      destruct ref_fls.
      set (e := H0 neq).
      symmetry in e.
      simpl.
      induction e.
      reflexivity.
  - intros h neq.
    destruct h.
    + simpl in neq.
      set (ref_fls := nat_eq_reflect_false k k0).
      destruct ref_fls.
      set (e := H0 neq).
      symmetry in e.
      simpl.
      induction e.
      reflexivity.
    + simpl; reflexivity.
Qed.



Corollary pass_reduce1_2 {n : nat} {xs : FreeGroup n}

  : forall {g h k : Generators n},

      ~(is_inverse_gen g h) ->
      ~(is_inverse_gen h k) ->

        reduce1 (fcon g (fcon h (fcon k xs))) = fcon g (fcon h (reduce1 (fcon k xs))).

Proof.
  intros g h k inv1 inv2.
  rewrite (pass_reduce1 _ inv1).
  rewrite (pass_reduce1 _ inv2).
  reflexivity.
Qed.



Lemma reduce1_on_length {n : nat}

  : forall (g : FreeGroup n), 

      (word_length g = word_length (reduce1 g)) \/ (word_length g = S (S (word_length (reduce1 g)))).

Proof.
  induction g.
  - simpl. left; trivial.
  - destruct g0.
    + simpl. left; trivial.
    + set (inv_dec := is_inverse_gen_is_decidable g g0).
      destruct inv_dec as [ninv | inv].
      * repeat fold (@fcon n) in *. 
        rewrite (pass_reduce1 g1 ninv).
        destruct IHg as [l | r].
        -- repeat rewrite (word_length_s g _).
          rewrite <- l.
          left; reflexivity.
        -- repeat rewrite (word_length_s g _).
          rewrite <- r.
          right; reflexivity.
      * repeat fold (@fcon n) in *.
        rewrite (simpl_reduce1_on_inv inv).
        right.
        repeat rewrite (word_length_s _ _).
        reflexivity.
Qed.



Lemma reduce1_normal_is_id {n : nat}

  : forall {xs : FreeGroup n}, normalized xs -> (reduce1 xs = xs).

Proof.
  intros xs nxs.
  induction xs.
  - reflexivity.
  - assert (nxs'  := children_are_normal nxs).
    assert (redxs := IHxs nxs').
    induction xs.
    + simpl; reflexivity.
    + unfold normalized in nxs; destruct nxs.
      fold (normalized xs) in H0.
      set (e := pass_reduce1 xs H).
      apply eq_sym in e.
      unfold fcon in e.
      induction e.
      apply f_equal.
      exact redxs.
Qed.



Lemma length_fixpoint_is_normal {n : nat}

  : forall (w : FreeGroup n), (word_length w = word_length (reduce1 w)) -> normalized w.

Proof.
  intros w e.
  induction w.
  - simpl; trivial.
  - destruct w.
    + exact (singleton_is_normalized g).
    + repeat rewrite (word_length_s _ _) in e.
      set (inv_dec := is_inverse_gen_is_decidable g g0).
      destruct inv_dec as [ninv | inv].
      * repeat fold (@fcon n) in *. rewrite (pass_reduce1 w ninv) in e.
        rewrite (word_length_s _ _) in e.
        apply (extend_normalized ninv).
        apply IHw.
        inversion e.
        exact H0.
      * exfalso.
        rewrite (simpl_reduce1_on_inv inv) in e.
        induction (word_length w).
        discriminate e.
        inversion e.
        exact (IHn0 H0).
Qed.



Lemma extend_normalized_weak {n : nat} {xs : FreeGroup n}

  : forall (g : Generators n), 

      normalized xs -> normalized (reduce1 (fcon g xs)).

Proof.
  induction xs.
  - intros g i.
    simpl; trivial.
  - intros g0 norm.
    set (cnorm := children_are_normal norm).
    set (inv_dec := is_inverse_gen_is_decidable g0 g).
    destruct inv_dec as [ninv | inv].
    + fold (@fcon n) in *; rewrite (pass_reduce1 xs ninv).
      rewrite (reduce1_normal_is_id norm).
      exact (extend_normalized ninv norm).
    + rewrite (simpl_reduce1_on_inv inv).
      exact cnorm.
Qed.



Lemma reduce_normal_is_id {n : nat}

  : forall {xs : FreeGroup n} (m : nat), normalized xs -> (reduce m xs = xs).

Proof.
  intros xs m nxs.
  induction m.
  - simpl.
    trivial.
  - unfold reduce; rewrite repeat_on_left.
    fold (@reduce n m).
    rewrite (reduce1_normal_is_id nxs).
    exact IHm.
Qed.



Lemma reduce1_well_def {n : nat}

  : forall {g h : FreeGroup n},
      let E := strong_free_equiv in

        E g h -> E (reduce1 g) (reduce1 h).

Proof.
  induction g.
  - intros h E eqv.
    destruct h.
    + simpl; trivial.
    + unfold reduce1 at 1.
      set (xs := reduce1 (free_con n g h)).
      destruct xs.
      * exact (refl _).
      * simpl; simpl in eqv.
        exact eqv.
  - intros h E eqv.
    destruct h.
    + simpl in eqv.
      exfalso; exact eqv.
    + simpl in eqv; destruct eqv as (ge & eqv).
      set (IHg' := IHg h eqv).
      destruct g0, h.
      * simpl.
        split.
        exact ge.
        trivial.
      * fold (@fid n); fold (@fcon n); fold (singleton g).
        rewrite (reduce1_normal_is_id (singleton_is_normalized g)).
        unfold reduce1 in IHg at 1.
        set (inv_dec := is_inverse_gen_is_decidable g1 g0).
        destruct inv_dec as [ninv | inv].
        -- fold (@fcon n); rewrite (pass_reduce1 h  ninv).
          unfold singleton.
          set (resp := proj1 (@free_con_respects_strong_free_equiv n g g1 fid (reduce1 (fcon g0 h)) ge)).
          apply resp.
          exact IHg'.
        -- simpl in eqv.
          exfalso; exact eqv.
      * simpl in eqv.
        exfalso; exact eqv.
      * simpl in eqv.
        destruct eqv as (ge' & eqv).
        set (inv_dec := is_inverse_gen_is_decidable g g0).
        destruct inv_dec as [ninv | inv].
        -- fold (@fcon n); fold (@fcon n); rewrite (pass_reduce1 g2 ninv).
          assert (~is_inverse_gen g1 g3).
          intro hyp_inv.
          apply (inverse_gen_respects_gen_equiv (sym ge)) in hyp_inv.
          apply is_inverse_gen_swap in hyp_inv.
          apply (inverse_gen_respects_gen_equiv (sym ge')) in hyp_inv.
          apply is_inverse_gen_swap in hyp_inv.
          exact (ninv hyp_inv).
          rewrite (pass_reduce1 h H).
          apply (proj1 (free_con_respects_strong_free_equiv g g1 ge)).
          exact IHg'.
        -- rewrite (simpl_reduce1_on_inv inv).
          assert (is_inverse_gen g1 g3).
          apply (inverse_gen_respects_gen_equiv ge).
          apply is_inverse_gen_swap.
          apply (inverse_gen_respects_gen_equiv ge').
          apply is_inverse_gen_swap.
          exact inv.
          rewrite (simpl_reduce1_on_inv H).
          exact eqv.
Qed.



Lemma reduce_well_def {n : nat} (m : nat)

  : forall {g h : FreeGroup n},
      let E := strong_free_equiv in

        E g h -> E (reduce m g) (reduce m h).

Proof.
  induction m.
  - intros g h E eqv.
    unfold reduce, repeat, fun_id.
    exact eqv.
  - intros g h E eqv.
    unfold reduce.
    rewrite repeat_on_left.
    rewrite repeat_on_left.
    fold (@reduce n m).
    set (eqv' := reduce1_well_def eqv).
    exact (IHm _ _ eqv').
Qed.



Lemma pass_reduce {n : nat} 

  : forall (m : nat) (xs : FreeGroup n) {g h : Generators n},
      let E := strong_free_equiv in

          E (reduce (S m) (fcon g (fcon h xs))) (reduce1 (fcon g (reduce m (fcon h xs)))).

Proof.
  induction m.
  - intros xs g h E.
    unfold reduce, repeat, fun_id.
    exact (refl _).
  - intros xs g h E.
    unfold reduce at 1.
    rewrite repeat_on_right.
    fold (@reduce n (S m)).
    set (IHm' := IHm xs g h).
    apply (trans (reduce1_well_def IHm')).
    unfold reduce at 2.
    rewrite repeat_on_right.
    fold (@reduce n m).
    set (ys := reduce m (fcon h xs)).
    destruct ys.
    + simpl.
      split.
      exact (refl _).
      trivial.
    + fold (fcon g0 ys).
      set (inv_dec := is_inverse_gen_is_decidable g g0).
      destruct inv_dec as [ninv1 | inv1].
      * rewrite (pass_reduce1 ys ninv1).
        exact (refl _).
      * rewrite (simpl_reduce1_on_inv inv1).
        destruct ys.
        -- fold (@fid n); fold (@singleton n g0).
          rewrite (reduce1_normal_is_id (singleton_is_normalized g0)).
          unfold singleton. rewrite (simpl_reduce1_on_inv inv1).
          exact (refl _).
        -- destruct (is_inverse_gen_is_decidable g0 g1) as [ninv2 | inv2].
          ++ fold (fcon g1 ys).
            rewrite (pass_reduce1 ys ninv2).
            rewrite (simpl_reduce1_on_inv inv1).
            exact (refl _).
          ++ rewrite (simpl_reduce1_on_inv inv2).
            apply reduce1_well_def.
            simpl.
            split.
            exact (unique_inverse_gen (is_inverse_gen_swap inv2) inv1).
            exact (refl _).
Qed.



Lemma children_are_really_normal {n : nat}

  : forall (m : nat) (g : Generators n) (xs : FreeGroup n),

      normalized (reduce m (fcon g xs)) -> normalized (reduce m xs).

Proof.
  induction m.
  - intros g xs norm.
    unfold reduce, repeat, fun_id in *.
    exact (children_are_normal norm).
  - intros g xs norm.
    unfold reduce in norm.
    rewrite repeat_on_left in norm.
    destruct xs.
    + rewrite (reduce_normal_is_id (S m) fid_is_normal).
      exact fid_is_normal.
    + set (inv_dec := is_inverse_gen_is_decidable g g0).
      destruct inv_dec as [ninv | inv].
      * rewrite (pass_reduce1 _ ninv) in norm.
        fold (@reduce n m) in norm.
        set (IHm' := IHm g (reduce1 (fcon g0 xs)) norm).
        unfold reduce in IHm'.
        rewrite <- repeat_on_left in IHm'.
        fold (@reduce n) in IHm'.
        exact IHm'.
      * rewrite (simpl_reduce1_on_inv inv) in norm.
        fold (@reduce n m) in norm.
        set (ext := extend_normalized_weak g0 norm).
        destruct xs.
        -- set (norm_sng := singleton_is_normalized g0).
          fold (@fcon n); fold (@fid n); fold (singleton g0).
          rewrite (reduce_normal_is_id (S m) norm_sng).
          exact norm_sng.
        -- repeat fold (@fcon n) in *.
          set (pass := @pass_reduce n m xs g0 g1).
          exact (normalized_respects_strong_free_equiv (sym pass) ext).
Qed.



Lemma normalizable {n : nat} (g : FreeGroup n)

  : {m : nat & normalized (reduce m g)}.

Proof.
  induction g.
  - exists 0.
    simpl.
    trivial.
  - destruct IHg as (m & norm).
    exists (S m).
    destruct g0.
    + set (norm_sng := singleton_is_normalized g).
      fold (@fid n); fold (@fcon n); fold (singleton g).
      rewrite (reduce_normal_is_id (S m) norm_sng).
      exact norm_sng.
    + set (inv_dec := is_inverse_gen_is_decidable g g0).
      destruct inv_dec as [ninv | inv].
      * apply (normalized_respects_strong_free_equiv (sym $ pass_reduce m g1)).
        fold (@fcon n) in *.
        set (ys := reduce m (fcon g0 g1)).
        fold ys in norm.
        destruct ys.
        -- set (norm_sng := singleton_is_normalized g).
          fold (@fid n); fold (singleton g).
          rewrite (reduce1_normal_is_id norm_sng).
          exact norm_sng.
        -- set (inv_dec := is_inverse_gen_is_decidable g g2).
          destruct inv_dec as [ninv2 | inv2].
          ++ fold (fcon g2 ys); rewrite (pass_reduce1 ys ninv2).
            unfold fcon at 2; rewrite (reduce1_normal_is_id norm).
            exact (extend_normalized ninv2 norm).
          ++ rewrite (simpl_reduce1_on_inv inv2).
            exact (children_are_normal norm).
      * unfold reduce.
        rewrite repeat_on_left.
        rewrite (simpl_reduce1_on_inv inv).
        fold (@reduce n m).
        destruct g1.
        -- assert (normalized (free_id n)).
          simpl; trivial.
          rewrite (reduce_normal_is_id m H).
          exact H.
        -- exact (children_are_really_normal m g0 _ norm).
Qed.



Lemma word_length_reduce1 {n : nat}

  : forall (g : Generators n) (w : FreeGroup n),

      word_length (reduce1 (fcon g w)) <= S (word_length w).

Proof.
  intros g w.
  destruct (reduce1_on_length (fcon g w)) as [l | r].
  - rewrite <- l.
    rewrite word_length_s.
    exact (le_n _).
  - rewrite word_length_s in r.
    set (e := le_n (word_length (reduce1 (fcon g w)))).
    set (e' := le_S _ _ (le_S _ _ e)).
    rewrite <- r in e'.
    exact e'.
Qed.



Lemma normalizable_via_length {n : nat} (g : FreeGroup n)

  : normalized (reduce (word_length g) g).

Proof.
  destruct (reduce1_on_length g) as [l | r].
  - set (ng := length_fixpoint_is_normal g l).
    set (e  := reduce_normal_is_id (word_length g) ng).
    rewrite e; exact ng.
  - assert (word_length g > word_length (reduce1 g)).
    rewrite r; unfold ">"; unfold "<".
    exact (le_S _ _ (le_n (S (word_length (reduce1 g))))).
    clear r.
    induction g.
    + simpl; trivial.
    + rewrite word_length_s in H.
      destruct (reduce1_on_length (free_con n g g0)) as [l | r].
      * rewrite <- l in H.
        rewrite word_length_s in H.
        exfalso; exact (none_less_than_itself H).
      * clear H.
        rewrite word_length_s in *.
        destruct g0.
        -- simpl in *.
          trivial.
        -- set (inv_dec := is_inverse_gen_is_decidable g g0).
          destruct inv_dec as [ninv | inv].
          ++ rewrite (pass_reduce1 _ ninv) in r.
            apply (normalized_respects_strong_free_equiv $ sym $ pass_reduce _ _).
            repeat rewrite word_length_s in *.
            set (le_n (S (S (word_length g1)))).
            pattern (S (S (word_length g1))) at 1 in l.
            rewrite r in l.
            apply le_S in l.
            fold (lt (S (S (word_length (reduce1 (fcon g0 g1))))) (S (S (S (word_length g1))))) in l.
            repeat apply reduce_succ_lt in l.
            unfold ">" in IHg; fold (@fcon n) in IHg.
            set (IHg l).
            apply (extend_normalized_weak g) in n0.
            exact n0.
          ++ repeat fold (@fcon n) in *.
            unfold reduce; rewrite repeat_on_left; fold (@reduce n (word_length (fcon g0 g1))).
            rewrite (simpl_reduce1_on_inv inv) in *.
            repeat rewrite word_length_s in *.
            clear r.
            set (word_length_reduce1 g0 g1).
            apply split_le in l.
            destruct l as [l | r].
            ** set (IHg' := IHg l).
              exact (children_are_really_normal _ _ _ IHg').
            ** destruct (reduce1_on_length (fcon g0 g1)) as [l' | r'].
              set (norm := length_fixpoint_is_normal _ l').
              set (norm' := children_are_normal norm).
              rewrite (reduce_normal_is_id _ norm'); exact norm'.
              rewrite word_length_s in r'.
              rewrite r in r'.
              inversion r'.
              exfalso.
              set (intro_lt (eq_sym H0)).
              set (intro_lt (eq_refl (S (word_length g1)))).
              set (lt_trans l0 l).
              exact (none_less_than_itself l1).
Qed.



(*
Definition normalizable_compute {n : nat} (g : FreeGroup n)

  : {m : nat & normalized (reduce m g)}

:=
  let base :=
        existT 
          (fun m => normalized (reduce m fid))
          0 
          I
  in

  let step := 
        fun (g : Generators n) (xs : FreeGroup n) (hyp : {m : nat & normalized (reduce m xs)}) =>
          let m    := projT1 hyp in
          let norm := projT2 hyp in

            existT 
              (fun k => normalized (reduce k (fcon g xs)))
              (S m)
              @(match xs with
                | free_id  _       => 
                    fun (eq_xs : xs = free_id n) =>
                      let norm_sng := singleton_is_normalized g in
                      let red      := reduce_normal_is_id (S m) norm_sng in

                        eq_ind
                          (free_id n)
                          (fun xs' => normalized (reduce (S m) (fcon g xs')))
                          (eq_ind _ _ norm_sng _ (eq_sym red))
                          (xs)
                          (eq_sym eq_xs)

                | free_con _ g' ys => 
                    fun (eq_xs : xs = free_con n g' ys) =>
                      let inv_dec := is_inverse_gen_is_decidable g g' in
                      let norm'   := eq_ind _ (fun xs' => normalized (reduce m xs')) norm _ eq_xs in

                        eq_ind 
                          (free_con n g' ys)
                          (fun xs' => normalized (reduce (S m) (fcon g xs')))

                          (match inv_dec with
                            | or_introl ninv =>
                                let zs := reduce m (fcon g' ys) in

                                  normalized_respects_strong_free_equiv (sym $ pass_reduce m ys) $
                                    (match zs with
                                    | free_id _ => 
                                        fun (eq_zs : reduce m (fcon g' ys) = free_id n) =>
                                          let norm_sng := singleton_is_normalized g in
                                          let red      := reduce1_normal_is_id norm_sng in

                                            eq_ind 
                                              fid 
                                              (fun zs' => normalized (reduce1 (fcon g zs'))) 
                                              (eq_ind _ _ norm_sng _ (eq_sym red))
                                              (reduce m (fcon g' ys)) 
                                              (eq_sym eq_zs)

                                    | free_con _ h hs => 
                                        fun (eq_zs : reduce m (fcon g' ys) = free_con n h hs) => 
                                          let norm''   := eq_ind _ (fun zs' => normalized zs') norm' _ eq_zs in
                                          let inv_dec' := is_inverse_gen_is_decidable g h in
                                            match inv_dec' with
                                            | or_introl ninv' =>
                                                  eq_ind 
                                                    (free_con n h hs)
                                                    (fun zs' => normalized (reduce1 (fcon g zs')))
                                                    (let pass := pass_reduce1 hs ninv' in
                                                     let red  := reduce1_normal_is_id norm'' in 
                                                        eq_ind 
                                                          _
                                                          (fun ps => normalized ps)
                                                          (eq_ind 
                                                            _
                                                            (fun qs => normalized (fcon g qs))
                                                            (extend_normalized ninv' norm'')
                                                            _
                                                            (eq_sym red))
                                                          _
                                                          (eq_sym pass))
                                                    zs
                                                    (eq_sym eq_zs)


                                            | or_intror inv'  => _
                                            end
                                    end) eq_refl

                            | or_intror inv  => _
                            end)

                            xs
                            (eq_sym eq_xs)
                end) eq_refl

  in
    FreeGroup_rect n (fun h => {m : nat & normalized (reduce m h)}) base step g.
*)



Definition normalize {n : nat}

  : FreeGroup n -> FreeGroup n

:=
  fun g => reduce (word_length g) g.



Corollary normal_is_normalized {n : nat}

  : forall (g : FreeGroup n), normalized (normalize g).

Proof.
  intro g; unfold normalize.
  exact (normalizable_via_length _).
Qed.



Corollary normalize_normal_is_id {n : nat}

  : forall (g : FreeGroup n), normalized g -> normalize g = g.

Proof.
  intros g norm.
  unfold normalize; simpl.
  exact (reduce_normal_is_id _ norm).
Qed.


Definition free_equiv {n : nat}

  : FreeGroup n -> FreeGroup n -> Prop

:= 
  fun g g' =>
    strong_free_equiv (normalize g) (normalize g').



Lemma free_equiv_refl {n : nat}

  : forall (g : FreeGroup n), free_equiv g g.

Proof.
  intro g.
  unfold free_equiv.
  exact (refl _).
Qed.



Lemma free_equiv_sym {n : nat}

  : forall (g h : FreeGroup n), free_equiv g h -> free_equiv h g.

Proof.
  intros g h eqv.
  unfold free_equiv in *.
  exact (sym eqv).
Qed.



Lemma free_equiv_trans {n : nat}

  : forall (g h k : FreeGroup n), free_equiv g h -> free_equiv h k -> free_equiv g k.

Proof.
  intros g h k e1 e2.
  unfold free_equiv in *.
  exact (trans e1 e2).
Qed.



Instance free_equiv_is_equiv {n : nat}

  : Equiv (@free_equiv n)

:=
{
  refl := @free_equiv_refl n;
  sym  := @free_equiv_sym n;
  trans := @free_equiv_trans n;
}.



Lemma free_con_well_def_on_free_equiv {n : nat}

  : forall {g g' : Generators n} {w w' : FreeGroup n},
      let G := gen_equiv n in
      let F := free_equiv in

        G g g' -> F w w' -> F (fcon g w) (fcon g' w').

Proof.
  intros g g'.
  induction w.
  - destruct w'.
    + intros G F ge fe.
      unfold F, free_equiv.
      fold (@fid n); fold (@singleton n g); fold (@singleton n g').
      repeat rewrite (normalize_normal_is_id _ (singleton_is_normalized _)).
      simpl. split. exact ge. trivial.
    + intros G F ge fe.
      unfold F, free_equiv; unfold F, free_equiv in fe.
      rewrite (normalize_normal_is_id _ fid_is_normal) in fe.
      fold (@fid n); fold (@singleton n g).
      rewrite (normalize_normal_is_id _ (singleton_is_normalized _)).
      unfold normalize.
      rewrite word_length_s.
      fold (@fcon n) in *.
      apply (rtrans $ sym (@pass_reduce n (word_length (fcon g0 w')) w' g' g0)).
      fold (normalize (fcon g0 w')).
      set (nw := normalize (fcon g0 w')).
      fold nw in fe.
      destruct nw.
      * simpl. split. exact ge. trivial.
      * simpl in fe. exfalso; exact fe.
  - destruct w'.
    + intros G F ge fe.
      unfold F, free_equiv; unfold F, free_equiv in fe.
      fold (@fcon n) in *; fold (@fid n) in *; fold (@singleton n g').
      rewrite (normalize_normal_is_id _ (singleton_is_normalized g')).
      rewrite (normalize_normal_is_id _ fid_is_normal) in fe.
      unfold normalize.
      rewrite word_length_s.
      apply (trans (@pass_reduce n (word_length (fcon g0 w)) w g g0)).
      fold (normalize (fcon g0 w)).
      set (nw := normalize (fcon g0 w)).
      fold nw in fe.
      destruct nw.
      * simpl. split. exact ge. trivial.
      * simpl in fe. exfalso; exact fe.
    + intros G F ge fe.
      unfold F, free_equiv, normalize.
      rewrite word_length_s.
      fold (@fcon n). 
      apply (trans (@pass_reduce n (word_length (fcon g0 w)) w g g0)).
      fold (normalize (fcon g0 w)).
      rewrite word_length_s.
      apply (rtrans $ sym $ @pass_reduce n (word_length (fcon g1 w')) w' g' g1).
      fold (normalize (fcon g1 w')).
      unfold F, free_equiv in fe.
      destruct (@free_con_respects_strong_free_equiv n g g' (normalize (fcon g0 w)) (normalize (fcon g1 w')) ge) as (f & _).
      exact (reduce1_well_def $ f fe).
Qed.



Definition free_mult {n : nat}

  : FreeGroup n -> FreeGroup n -> FreeGroup n

:=
  fix con xs ys :=
    match xs with
    | free_id     _      => ys
    | free_con _ g zs => fcon g (con zs ys)
    end.



Lemma free_mult_left_id {n : nat}

  : forall (g : FreeGroup n), free_equiv (free_mult fid g) g.

Proof.
  intro g; simpl. exact (free_equiv_refl g).
Qed.



Lemma free_mult_right_id {n : nat}

  : forall (g : FreeGroup n), free_equiv (free_mult g fid) g.

Proof.
  intro g; simpl.
  induction g.
  - simpl; exact (free_equiv_refl fid).
  - simpl.
    unfold app.
    exact (free_con_well_def_on_free_equiv (refl g) IHg).
Qed.

About pass_reduce.

Lemma normalize_sub {n : nat}

  : forall {g h : FreeGroup n},

      free_equiv (free_mult g h) (free_mult (normalize g) (normalize h)).

Proof.
  induction g.
  - intro h.
    simpl.
    unfold free_equiv.
    rewrite (normalize_normal_is_id _ (normal_is_normalized h)).
    exact (refl _).
  - intro h.
    set (IHg' := IHg h).
    set (free_con_well_def_on_free_equiv (refl g) IHg').
    unfold free_mult at 1.
    fold (free_mult g0 h).
    apply (trans f).
    unfold free_equiv.
    unfold normalize at 1.
    rewrite word_length_s.
    set (m := word_length (free_mult (normalize g0) (normalize h))).
    set (w := free_mult (normalize g0) (normalize h)).
    set (pass := pass_reduce m w).



Lemma free_mult_eq_id {n : nat}

  : forall {g h : FreeGroup n},

      free_equiv fid g -> free_equiv fid h -> free_equiv fid (free_mult g h).

Proof.
  destruct g, h.
  - simpl; trivial.
  - simpl; trivial.
  - intros e1 e2.
    apply (rtrans $ sym $ free_mult_right_id _).
    exact e1.
  - intros e1 e2.
    unfold free_equiv in *.
    repeat rewrite (normalize_normal_is_id _ fid_is_normal) in *.
    fold (@fid n); fold (@fcon n). 



Lemma free_mult_well_def {n : nat}

  : forall {g g' h h' : FreeGroup n},

      free_equiv g g' -> free_equiv h h' -> free_equiv (free_mult g h) (free_mult g' h').

Proof.
  induction g.
  - destruct g'.
    + simpl. trivial.
    + induction h.
      * destruct h'.
        -- simpl; unfold app.
          intros e1 e2.
          set (free_mult_right_id g').
          apply (rtrans $ sym $ free_con_well_def_on_free_equiv (refl g) f).
          exact e1.
        -- intros e1 e2.
          simpl; unfold app.
          set (g0h' := fcon g0 h').
          fold (@fcon n) in *; fold g0h'; fold g0h' in e2.
          destruct g0h'.
          ++ set (free_mult_right_id g').
            apply (rtrans $ sym $ free_con_well_def_on_free_equiv (refl g) f).
            apply (rtrans e1).
            exact e2.
          ++ assert (free_mult (fcon g g') (fcon g1 g0h') = fcon g (free_mult g' (fcon g1 g0h'))).
            simpl; unfold app.
            reflexivity.
            apply (rtrans $ lift_eq H).
            













