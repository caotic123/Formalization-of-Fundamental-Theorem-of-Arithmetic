From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Logic.JMeq.
Require Import Coq.Init.Specif.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Logic.FinFun.
Require Import FunInd.
Require Import Coq.Arith.Div2.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.Streams.
Require Import Coq.Lists.Streams.

Notation "x ** y" := (prod x y)  (at level 90, left associativity) : type_scope.
Notation "H ´ 1" := (fst H) (at level 10, left associativity).
Notation "H ´ 2" := (snd H) (at level 10, left associativity).
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Init.Nat.
Require Import Psatz.

Definition divisible (x : nat) (a : nat) := {b : nat | a * b = x}.
Definition indivisible (x : nat) (a : nat) := divisible x a -> False.

Definition prime (x : nat) := {y & y <> x ** y <> 1 ** divisible x y} -> False.
Definition composite (x : nat) := prime x -> False.

Axiom div_2 : forall (x : nat), {y & y.1 >= 2 /\ y.2 >= 2 /\ y.1 * y.2 = x}.

Inductive Totally {A : Type} :=
  |Total : A -> Totally
  |Partial : Totally.

Fixpoint div' x y z c {struct z} :=
  match z with
    | 0 => Partial
    | S y' => if (x =? c*y) then Total c else (div' x y y' (S c))
  end.

Fixpoint div2' x y z {struct z} :=
  match z with
    | 0 => Partial
    | S y' => if (x =? y'*y) then Total y' else (div2' x y y')
  end.

Definition div (x y : nat) := div' x y x 1.
Definition div2 (x y : nat) := div2' x y (S x).

Export ListNotations.

Fixpoint get_factors x z :=
     match z with
       |0 => []
       |S n => match (div2 x (S n)) with
                 | Total _ => cons (S n) (get_factors x n) 
                 | Partial => get_factors x n
               end
    end.

Definition prime_dec (x : nat) : bool := length (get_factors x x) =? 2.

Theorem sum_less : forall y z x, S y + S z = x -> S y <= x /\ S z <= x.
 intros;lia.
Qed.

Definition strong_relation : forall x, {h | x <= h}.
intros.
by exists x.
Defined.

Theorem div_less : forall x y z, S y * S z = x -> S y <= x /\ S z <= x.
 intro.
 destruct(strong_relation x).
 move => H'.
 destruct H'.
 induction x0.
 intros.
 destruct x.
 inversion H.
 inversion l.
 intros.
 lia.
 intros.
   have : forall y z, S y <= S y * S z.
   intros.
   induction y.
   simpl.
   destruct z0.
   auto.
   auto with arith.
   lia.
 move => H1.
 subst.
 constructor.
 apply : H1.
 rewrite PeanoNat.Nat.mul_comm.
 apply : H1.
 Qed.

Definition _1_prime_not_prime : ~ (prime 1 \/ ~ prime 1).
Admitted.

Definition _2prime : prime 2.
  move => H.
  destruct H.
  destruct p.
  destruct p.
  destruct x.
  destruct d.
  inversion e.
  destruct d.
  destruct x.
  intuition.
  destruct x.
  intuition.
  destruct x0.
  rewrite PeanoNat.Nat.mul_0_r in e.
  inversion e.
  destruct (div_less e).
  inversion H.
  inversion H2.
  inversion H4.
Qed.

Definition isPartial {A} (x : @Totally A) := 
 match x with
   |Total _ => False
   |Partial => True
  end.

Definition isTotal {A} (x : @Totally A) := 
 match x with
   |Total _ => True
   |Partial => False
  end.

Definition proj_total {A} {x : @Totally A} : isTotal x -> A :=
  match x as c return isTotal c -> A with
    |Total y => fun _ => y
    |Partial => fun (v : False) => match v with end
  end.

Theorem ind_by_2 (P : nat -> Prop) (H : P 2) (H1 : forall x, P (S (S (S x)))) : forall x, x >= 2 -> P x.
  move => x I.
  elim/@ind_0_1_SS : x I.
  move => H'; inversion H'.
  move => H'; inversion H'; inversion H2.
  intros.
  destruct n.
  exact H.
  apply : H1.
Defined.

Theorem dif_eq : forall x y, x <> y -> x =? y = false.
  intros.
  elim/@nat_double_ind : x/y H.
  intros.
  destruct n.
  intuition.
  trivial.
  intros.
  trivial.
  intros.
    have : forall n m, S n <> S m -> n <> m.
    intros.
    lia.
  move => H2.
  exact (H (H2 _ _ H0)).
Qed. 

Theorem reflexivity_div : forall x, x > 0 -> isTotal (div x x).
  case.
  intros.
  inversion H.
  intros.
  unfold div.
  unfold div'.
  rewrite Nat.mul_1_l.
  by rewrite Nat.eqb_refl.
Qed.


Theorem mult_discrimate : forall x y c, y > S x -> ~ c * y = S x.
  intros.
  move => H'.
  destruct c.
  inversion H'.
  destruct y.
  by rewrite Nat.mul_comm in H'.
  destruct (div_less H').
  lia.
Qed.

Theorem discr0 : forall x y, 0 = x * y -> x = 0 \/ y = 0.
  intros.
  destruct x.
  by left.
  right.
  by destruct y.
Qed.

Theorem discrS : forall x y z, S z = x * y -> x > 0 /\ y > 0.
  intros.
  destruct x.
  inversion H.
  destruct y.
  rewrite Nat.mul_comm in H.
  inversion H.
  auto with arith.
Qed.

Theorem eq_rel : forall x y, x =? y = true -> x = y.
  intros.
  elim/@nat_double_ind : x/y H.
  intros; by destruct n.
  intros; inversion H.
  intros; auto.
Qed.

Theorem eq_rel_false : forall x y, x =? y = false -> x <> y.
  intros.
  elim/@nat_double_ind : x/y H.
  intros; by destruct n.
  intros; auto.
  intros; auto.
Qed.

Theorem false_eq_rel : forall x y, x <> y -> x =? y = false.
  intros.
  elim/@nat_double_ind : x/y H.
  intros; by destruct n.
  intros; auto.
  intros; auto.
Qed.

Theorem refl_nat_dec : forall x, x =? x.
  intros.
  by induction x.
Qed.

Theorem symm_nat_dec : forall x y b, x =? y = b -> y =? x = b.
  intros.
  destruct b.
  rewrite (eq_rel H).
  by apply : refl_nat_dec.
  pose (eq_rel_false H).
  remember (y =? x).
  destruct b.
  pose (eq_rel (eq_sym Heqb)).
  intuition.
  trivial.
Qed.

Theorem le_dec : forall x y, x <=? y = true -> x <= y.
  intros.
  elim/@nat_double_ind : x/y H.
  intros.
  auto with arith.
  intros.
  inversion H.
  intros.
  apply : le_n_S.
  by apply : H.
Qed.

Theorem dec_le : forall x y, x <= y -> x <=? y = true.
  intros.
  elim/@nat_double_ind : x/y H.
  intros.
  auto with arith.
  intros.
  inversion H.
  intros.
  apply le_S_n in H0.
  by apply : H.
Qed.

Theorem le_dec_false : forall x y, x <=? y = false -> y <= x.
  intros.
  elim/@nat_double_ind : x/y H.
  intros.
  destruct n.
  auto with arith.
  inversion H.
  intros.
  auto with arith.
  intros.
  apply : le_n_S.
  by apply : H.
Qed.

Theorem partially_between_le : forall x y z, y > S x -> isPartial (div2' (S x) y z).
  intros.
  generalize dependent y.
  generalize dependent z.
  induction z.
  intros.
  by simpl.
  intros.
  unfold div2'.
  pose (@mult_discrimate _ _ z H).
    have : S x <> z * y.
    auto.
  move => e.
  rewrite (dif_eq e).
  by apply : IHz.
Qed.

Require Import Coq.Logic.FinFun.

Theorem injection_plus : forall z, Injective (fun x => z+x).
  unfold Injective.
  elim.
  easy.
  intros.
  apply : H.
  simpl in H0.
  by inversion H0.
Qed.

Theorem ant_mul : forall z x y, x * S z = y * S z -> z * x = z * y.
  intros.
  elim/@nat_double_ind : x/y H.
  intros.
  destruct n.
  trivial.
  inversion H.
  intros.
  inversion H.
  intros.
  lia.
Qed.

Theorem injective_mult : forall z, Injective (fun x => (S z)*x).
  intros.
  unfold Injective.
  intros.
  replace (S z * x) with (x * S z).
  replace (S z * y) with (y * S z).  
  elim/@nat_double_ind : x/y H.
  intros.
  destruct n.
  trivial.
  rewrite Nat.mul_comm in H.
  inversion H.
  intros.
  symmetry in H; rewrite Nat.mul_comm in H.
  inversion H.
  intros.
  lia.
  auto with arith.
  auto with arith.
Qed. 

Ltac Symmetry_Op H := rewrite Nat.mul_comm in H; symmetry in H; rewrite Nat.mul_comm in H; symmetry in H. 


Theorem induction_div_to_definition : forall x y z, isTotal (div2' (S x) y z) -> divisible (S x) y.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction z.
  intros.
  inversion H.
  intros.
  unfold div2' in H.
  destruct (Nat.eq_dec (S x) (z * y)).
  exists z.   
  by rewrite Nat.mul_comm in e.
  rewrite (dif_eq n) in H.
  apply : IHz.
  exact H.
Qed.


Theorem divisor_le : forall x y z (H : isTotal (div2' (S x) y z)),
   proj_total H < z.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction z.
  intros.
  inversion H.
  intros.
  remember ( (div2' (S x) y (S z))).
  destruct t.
  unfold div2' in Heqt.
  destruct (S x =? z * y).
  move : H.
  rewrite Heqt.
  auto with arith.
  move : H.
  rewrite Heqt.
  move => H.
  pose (IHz _ _ H).
  auto with arith.
  inversion H.
Qed.


Theorem divisor_le' : forall x y z (H : isTotal (div2' x (S y) z)),
  x < (S y)*z.
  intros.
  generalize dependent x.
  generalize dependent y.
  induction z.
  intros.
  inversion H.
  intros.
  unfold div2' in H.
  remember (x =? z * S y).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)).
  lia.  
  pose (IHz _ _ H).
  lia.
Qed.
  
Theorem divisor_uniquess_ind : forall x y z (H : isTotal (div2' (S x) y z)),
    div2' (S x) y z = div2' (S x) y (S z).

  intros.
  generalize dependent x.
  generalize dependent y.
  induction z.
  intros.
  inversion H.
  intros.
  unfold div2'.
  destruct z.
  simpl.
  inversion H.
  destruct y.
  simpl.
  rewrite Nat.mul_comm.
  by simpl.
  simpl.
  remember (x =? y + z * S y).
  remember (x =? y + S (y + z * S y)).
  destruct b.
  destruct b0.
  pose (eq_rel (eq_sym Heqb)).
  pose (eq_rel (eq_sym Heqb0)).
  move : e.
  rewrite e0.
  move => H'.
  lia.
  trivial.
  destruct b0.
  pose (divisor_le' H).
  pose (eq_rel (eq_sym Heqb0)).
  move : l.
  rewrite e.
  move => H'.
  simpl in H'.
  lia.
  trivial.
Qed.

Theorem divisor_uniquess : forall x y z z' (H : isTotal (div2' (S x) y z)), z <= z' ->
    div2' (S x) y z = div2' (S x) y z'.
  intros.
    have : forall x z y n, isTotal(div2' (S x) y z) -> isTotal(div2' (S x) y (z + n)).
    intros.
    assert(forall y z x, isTotal(div2' (S x) y z) -> isTotal(div2' (S x) y (S z))).
    intros.
    induction z1.
    inversion H2.
    unfold div2'.
    destruct (S x1 =? S z1 * y1).
    constructor.
    apply : H2.
    induction n.
    by rewrite <- plus_n_O.
    rewrite <- Plus.plus_Snm_nSm.
    apply : H2.
    apply : IHn.
  move => H2.
    have : z' = z + (z' - z).
    lia.
  move => H'.
  rewrite H'.
  clear H'.
  generalize dependent (z' - z).
  clear H0.
  generalize dependent H.
  induction n.
  by rewrite <- plus_n_O.
  rewrite IHn.
  rewrite <- Plus.plus_Snm_nSm.
  apply : divisor_uniquess_ind.
  apply : H2.
  exact H.
Qed.
  
Theorem definition_div_to_induction' : forall x y (H : divisible (S x) y), isTotal (div2' (S x) y (S (proj1_sig H))).
  intros.
  destruct H. 
  generalize dependent x.
  generalize dependent y.
  induction x0.
  intros; simpl.
  rewrite Nat.mul_comm in e.
  inversion e.
  intros.
  simpl.
  rewrite Nat.mul_comm in e.
  simpl in e.
  rewrite e.
  by rewrite refl_nat_dec.
Qed.

Theorem definition_div_to_induction : forall x y, divisible (S x) y -> isTotal (div2 (S x) y).
  intros.
  pose (definition_div_to_induction' H).
    have : S (sval H) <= S (S x).
    destruct H.
    simpl.
    destruct x0.
    auto with arith.
    destruct y.
    inversion e.
    destruct (div_less e).
    auto with arith.
  move => H'.
  unfold div2.
  by rewrite <- (divisor_uniquess i H').
Qed.

Theorem definition_div_to_false_ind : forall x y, isPartial (div2 (S x) y) -> indivisible (S x) y.
  intros.
  move => HI.
    have : forall x y, isPartial (div2 (S x) y) -> ~ isTotal(div2 (S x) y).
    move => H'. 
    intros.
    destruct (div2 (S H') y0).
    inversion H0.
    move => H2.
    inversion H2. 
  move => H'.
  destruct (H' x y H).
  clear H'.
  by apply : definition_div_to_induction.
Qed.

Theorem definition_div_to_false_ind' : forall x y, indivisible (S x) y -> isPartial (div2 (S x) y).
  intros.
    have : forall x y, ~ isTotal(div2 (S x) y) -> isPartial (div2 (S x) y).
    move => H'. 
    intros.
    destruct (div2 (S H') y0).
    by contradiction H0.
    easy. 
  move => H'.
  apply : H'.
  move => H'.
  by pose(induction_div_to_definition H').
Qed.

Theorem Decibility_division : forall x y, divisible (S x) y + {indivisible (S x) y}.
  intros.
  set (div2 (S x) y).
  remember (div2 (S x) y).
  destruct t0.
  left.
  apply : (@induction_div_to_definition _ _ (S (S x))).
  unfold div2 in Heqt0.
  by destruct (div2' (S x) y (S (S x))).
  right.
  apply : definition_div_to_false_ind.
  by destruct (div2 (S x) y).
Qed.

Theorem list_factors_inhabited : forall x z h, In h (get_factors x z) -> divisible x h.
  intros.
  destruct x.
  by exists 0.
  apply : (@induction_div_to_definition _ _ (S (S x))).
  induction z.
  inversion H.
  simpl in H.
  set (div2 (S x) (S z)).
  remember (div2 (S x) (S z)).
  destruct t0.
  simpl in H.
  destruct H.
  assert(isTotal (div2 (S x) (S z))).
  by rewrite <- Heqt0.
  rewrite <- H.
  by [].
  by apply : IHz.
  by apply : IHz.
Qed.

Theorem le_factors_inhabited : forall x z h, h <= z -> divisible (S x) h -> In h (get_factors (S x) z) .
  intros.
  generalize dependent x.
  generalize dependent h. 
  induction z.
  intros.
  destruct h.
  destruct H0.
  inversion e.
  inversion H.
  intros.
  simpl.
  remember (div2 (S x) (S z)).
  destruct t.
  simpl.
  inversion H.
  by left.
  subst.
  right.
  by apply : IHz.
  assert(isPartial (div2 (S x) (S z))).
  destruct (div2 (S x) (S z)).
  inversion Heqt.
  easy.
  pose (definition_div_to_false_ind H1).
  inversion H.
  subst.
  easy.
  by apply : IHz.
 Qed.

Theorem all_factors_inhabits : forall x h, divisible (S x) h -> In h (get_factors (S x) (S x)).
  intros.
  destruct H.
  destruct h.
  inversion e.
  destruct x0.
  rewrite Nat.mul_comm in e.
  inversion e.
  apply : le_factors_inhabited.
  by destruct (div_less e).
  by exists (S x0). 
Qed.

Theorem all_indivisibles_not_inhabits : forall x h, ~ In h (get_factors (S x) (S x)) -> indivisible (S x) h.
  intros.
  move => H'.
  by pose (all_factors_inhabits H').
Qed.

Theorem le_factors_inhabited' : forall x z h, In h (get_factors (S x) z) -> divisible (S x) h.
  intros.
  apply : (@induction_div_to_definition _ _ (S (S x))).
  induction z.
  inversion H.
  simpl in H.
  remember (div2 (S x) (S z)).
  destruct t.
  unfold div2 in Heqt.
  destruct H.
  rewrite <- H.
  by rewrite <- Heqt.
  by apply : IHz.
  by apply : IHz.
Qed.

Theorem itself_1_factor : forall x, In (S x) (get_factors (S x) (S x)) /\ In 1 (get_factors (S x) (S x)).
  intros.
  assert(divisible (S x) 1).
  exists (S x).
  auto with arith.
  assert(divisible (S x) (S x)).
  exists 1.
  auto with arith.
  constructor.
  by apply : all_factors_inhabits.
  by apply : all_factors_inhabits.
Qed.

Theorem _2_minimuim_factors : forall x, 2 <= length (get_factors (S (S x)) (S (S x))).
  intros.
  pose (itself_1_factor (S x)).
  destruct a.
  destruct ((get_factors (S (S x)) (S (S x)))).
  inversion H.
  destruct l.
  inversion H.
  inversion H0.
  lia.
  easy.
  easy.
  simpl; auto with arith.
Qed.

Fixpoint nth_list {A} (xs : list A) n : n < length xs -> A. 
refine (match n as c return (c < length xs -> A) with
           |0 => _
           |S n => _
        end).
move => H.
destruct xs.
assert(~ 0 < 0).
auto with arith.
destruct(H0 H).
exact a.
move => H.
exact (nth_list A xs n (Nat.lt_succ_l _ _ H)).
Defined.

Theorem nth_list_uniquess_index : forall {A} (xs : list A) n (H : n < length xs) (H1 : n < length xs), 
   nth_list H = nth_list H1.
  intros.
  generalize dependent xs.
  induction n.
  intros.
  destruct xs.
  inversion H.
  trivial.
  intros.
  destruct xs.
  inversion H.
  simpl.
  apply : IHn.
Qed.

Theorem uniquess_2factors : 
  forall x, length (get_factors (S (S x)) (S (S x))) = 2 -> forall y, 
     divisible (S (S x)) y -> y = 1 \/ y = (S (S x)).

  (* this proof was made in a brutal manual way, for sure there is a more fancy way to prove
       just generalizing the proof, but idk the generalized proof might be necessary for our work *)

  
  intros.
  pose(@all_indivisibles_not_inhabits (S x)).
  destruct (itself_1_factor (S x)).
  pose(le_factors_inhabited' H1).
  pose(le_factors_inhabited' H2).
  move : i d d0.
  destruct (get_factors (S (S x)) (S (S x))).
  inversion H.
    have : forall (y : nat) k h, y <> k /\ y <> h -> ~ In y [k; h].
    intros.
    move => H4.
    destruct H3.
    destruct H4.
    subst.
    intuition.
    destruct H5.
    destruct H4.
    auto.
    inversion H4.
  move => brute_theorem.
  destruct l.
  inversion H.
  intros.
  destruct l.
  assert([n;n0] = [1; S (S x)] \/ [n; n0] = [S (S x); 1]).
  destruct H1.
  destruct H2.
  subst.
  inversion H2.
  destruct H2.
  subst.
  by right.
  destruct H2.
  destruct H2.
  destruct H1.
  subst.
  by left.
  destruct H1.
  destruct H1.
  destruct H2.
  subst.
  inversion H2.
  destruct H2.
  destruct H1.
  destruct H3.
  injection H3.
  intros; subst.
  destruct (Nat.eq_dec 1 y).
  by left.
  destruct (Nat.eq_dec y (S (S x))).
  by right.
  destruct (((i _ (brute_theorem _ _ _ (conj (Nat.Private_Tac.neq_sym n) n0)))) H0).
  injection H3.
  intros; subst.
  destruct (Nat.eq_dec 1 y).
  by left.
  destruct (Nat.eq_dec y (S (S x))).
  by right.
  destruct ((i _ (brute_theorem _ _ _ (conj n0 (Nat.Private_Tac.neq_sym n)))) H0).
  inversion H.
Qed.
  
Theorem prime_correspondence : forall x, prime_dec (S (S x)) = true -> prime (S (S x)).
  intros.
  unfold prime_dec in H.
  move => H'.
  destruct H'.
  destruct p.
  destruct p.
  destruct (uniquess_2factors (eq_rel H) d).
  intuition.
  intuition.
Qed.

Fixpoint prop_list {A} 
   (P : A -> A -> Prop) (v : list A) {struct v} : Prop.
intros.
destruct v.
exact True.
refine (_ (prop_list _ P v)).
destruct v.
exact (fun H => P a a).
refine (fun H => P a a0 /\ H).
Defined.

Fixpoint strong_prop_list {A} 
   (P : A -> A -> Prop) (v : list A) {struct v} : Prop.
intros.
destruct v.
exact True.
refine (_ (strong_prop_list _ P v)).
destruct v.
exact (fun H => True).
refine (fun H => P a a0 /\ H).
Defined.

Definition descending := fun v => prop_list (fun x y => y <= x) v.
Definition strong_descending := fun v => strong_prop_list (fun x y => y < x) v.

Theorem le_factors : forall z h x, In h (get_factors x z) -> h <= z.
  elim.
  intros.
  inversion H.
  intros.
  pose(H h x).
  unfold get_factors in H0.
  remember (div2 x (S n)).
  destruct t.
  destruct H0.
  by subst.
  pose (l H0).
  auto with arith.
  pose (l H0).
  auto with arith.
Qed.
    
Theorem factors_descending : forall x z, descending (get_factors x z).
  intros.
  induction z.
  intros.
  easy.
  intros.
  destruct z.
  simpl.
  by destruct (div2 x 1).
  simpl in *.
  move : IHz.
  remember (div2 x (S (S z))).
  remember (div2 x (S z)).
  intros.
  destruct t.
  destruct t0.
  constructor.
  auto with arith.
  exact IHz.
  unfold descending.
  simpl.
  remember (get_factors x z ).
  destruct l.
  auto with arith.
  constructor.
  assert(In n0 (get_factors x z)).
  destruct (get_factors x z).
  inversion Heql.
  simpl.
  left.
  inversion Heql.
  auto.  
  pose (le_factors H).
  auto with arith.
  exact IHz.
  assumption.
Qed.

Theorem factors_descending' : forall x z, strong_descending (get_factors x z).
  intros.
  induction z.
  intros.
  easy.
  intros.
  destruct z.
  simpl.
  by destruct (div2 x 1).
  simpl in *.
  move : IHz.
  remember (div2 x (S (S z))).
  remember (div2 x (S z)).
  intros.
  destruct t.
  destruct t0.
  constructor.
  auto with arith.
  exact IHz.
  unfold descending.
  simpl.
  remember (get_factors x z ).
  destruct l.
  auto with arith.
  constructor.
  assert(In n0 (get_factors x z)).
  destruct (get_factors x z).
  inversion Heql.
  simpl.
  left.
  inversion Heql.
  auto.  
  pose (le_factors H).
  auto with arith.
  exact IHz.
  assumption.
Qed.

Theorem strong_distinction_succ : forall x y z, strong_descending x -> S y < length x ->
  nth (S y) x z < nth y x z.
  intros.
  unfold strong_descending in H.
  generalize dependent x.
  generalize dependent z.
  induction y.
  intros.
  destruct x.
  inversion H0.
  destruct x.
  inversion H0.
  inversion H2.
  simpl in *.
  lia.
  intros.
  destruct x.
  inversion H0.
  simpl.
  assert (strong_prop_list (fun x : nat => lt^~ x) x).  
  destruct x.
  by constructor.
  by destruct H.
  simpl in H0.
  apply : (IHy z x H1 (le_S_n _ _ H0)).
Qed.
 
Theorem strong_distinction : forall a b z x, strong_descending x -> a < b -> b < length x ->
  nth b x z < nth a x z.
  elim.
  intros.
  generalize dependent x.
  induction b.
  inversion H0.
  intros.
  destruct b.
  by apply : strong_distinction_succ.
  assert(S b < length x) by lia.
  pose (IHb (Nat.lt_0_succ _) x H H2).
  rewrite <- l.
  by apply : strong_distinction_succ.
  intros.
  destruct b.
  inversion H1.
  assert(n < b) by lia.
  assert(b < length x) by lia.
  destruct x.
  inversion H2.
  simpl.
  assert(strong_descending x).
  destruct x.
  trivial.
  destruct H0.
  done.
  simpl in H4.
  destruct b.
  inversion H1.
  inversion H7.
  simpl in H2.
  assert(S b < length x) by lia.
  exact (H (S b) z x H5 H3 H6).
Qed.

Theorem nth_In : forall {A} (xs : list A) n z, n < length xs -> In (nth n xs z) xs.
  move => T; elim.
  intros.
  inversion H.
  intros.
  simpl in H0.
  destruct n.
  by left.
  right.
  apply : H.
  auto with arith.
Qed.

Theorem In_nth : forall {A} (xs : list A) n h, In n xs -> exists z, z < length xs /\ nth z xs h = n.
  move => T; elim.
  intros.
  inversion H.
  intros.
  destruct H0.
  subst.
  exists 0.
  constructor.
  simpl; auto with arith.
  auto.
  destruct (H n h H0).
  exists (S x).
  destruct H1.
  constructor.
  simpl; auto with arith.
  by simpl.
Qed.

Definition max (ls : list nat) : nat := 
  (fold_left (fun x y => if x <=? y then y else x) ls 0).

Definition min (ls : list nat) : nat :=
   (fold_left (fun x y => if x <=? y then x else y) ls (hd 0 ls)).
  
Theorem last_cons : forall {A} (xs : list A) y x, xs <> [] -> last xs y = last (x :: xs) y.
  move => A; elim.
  intuition.
  move => a l H y x H'.
  destruct l.
  auto.
  assert (a0 :: l <> []) by congruence.
  exact (H y x H0).
Qed.

Theorem left_le_max : 
  forall l a, a <= fold_left (fun x y0 : nat => if x <=? y0 then y0 else x) l a.
  elim.
  auto with arith.
  intros.
  simpl.
  remember (a0 <=? a).
  destruct b.
  pose (le_dec (eq_sym Heqb)).
  rewrite -> l0.
  apply : H.
  apply : H.
Qed.

Theorem left_le_min : 
  forall l a, fold_left (fun x y0 : nat => if x <=? y0 then x else y0) l a <= a.
  elim.
  auto with arith.
  intros.
  simpl.
  remember (a0 <=? a).
  destruct b.
  apply : H.
  pose (le_dec_false (eq_sym Heqb)).
  rewrite <- l0.
  apply : H.
Qed.

Theorem max_le_reduce : forall xs a b, a <= b -> 
  fold_left (fun x y0 : nat => if x <=? y0 then y0 else x) xs a <=
     fold_left (fun x y0 : nat => if x <=? y0 then y0 else x) xs b.
  elim.
  intros.
  auto with arith.
  intros.
  simpl.
  remember (b <=? a).
  destruct b0.
  pose (le_dec (eq_sym Heqb0)).
  assert(a0 <= a).
  by rewrite -> H0.
  by rewrite (dec_le H1).
  remember (a0 <=? a). 
  destruct b0.
  apply : H.
  exact (le_dec_false (eq_sym Heqb0)).
  pose (le_dec_false (eq_sym Heqb0)).
  pose (le_dec_false (eq_sym Heqb1)).
  by apply : H.
Qed.

Theorem min_le_reduce : forall xs a b, a <= b -> 
  fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs a <=
     fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs b.


  elim.
  intros.
  simpl.
  auto with arith.
  intros;simpl in *.
  remember (b <=? a).
  destruct b0.
  pose (le_dec (eq_sym Heqb0)).
  assert(a0 <= a).
  by rewrite -> H0.
  rewrite (dec_le H1).
  by apply : H.
  remember (a0 <=? a). 
  destruct b0.
  apply : H.
  pose (le_dec_false (eq_sym Heqb0)).
  pose (le_dec (eq_sym Heqb1)).
  lia.
  auto with arith.
Qed.

Theorem max_prop : forall xs y, In y xs -> y <= max xs.
  elim.
  intros.
  inversion H.
  intros.
  destruct H0. 
  rewrite <-H0.
  simpl.
  apply : left_le_max.
  pose (H _ H0).
  unfold max.
  simpl.
  pose (left_le_max l a).
  rewrite -> l0.
  clear l0 H H0.
  unfold max.
  generalize dependent a.
  induction l.
  auto with arith.
  simpl.
  move => a0.
  remember (a0 <=? a).
  destruct b.
  simpl.
  auto with arith.
  apply : max_le_reduce.
  by apply : (le_dec_false (eq_sym Heqb)).
Qed.


Theorem le_min_fold_skip : forall xs a b, In a xs -> a <= b ->
   fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs a
   =  fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs b.
   elim.
   intuition.
   intros.
   destruct H0.
   subst.
   simpl.
   rewrite Nat.leb_refl.
   remember (b <=? a0).
   destruct b0.
   pose (le_dec (eq_sym Heqb0)).
   auto with arith.
   auto.
   simpl.
   remember (b <=? a).
   destruct b0.
   pose (le_dec (eq_sym Heqb0)).
   assert(a0 <= a) by lia.
   rewrite (dec_le H2).
   by apply : H.
   pose(le_dec_false (eq_sym Heqb0)).
   remember (a0 <=? a).
   destruct b0.
   apply : H.
   assumption.
   by apply : le_dec.
   auto.
Qed.
 
Theorem ignore_default_value_by_copy : forall xs a b, In a xs -> In b xs ->
   fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs a
   =  fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs b.
  elim.
  intros.
  inversion H.
  intros.
  destruct H1.
  destruct H0.
  subst; simpl.
  by rewrite Nat.leb_refl.
  subst; simpl.
  rewrite Nat.leb_refl.
  remember (a0 <=? b).
  destruct b0.
  apply : le_min_fold_skip.
  assumption.
  by apply : le_dec.
  auto.
  destruct H0.
  rewrite <- H0.
  simpl.
  rewrite Nat.leb_refl.
  symmetry.
  remember (b <=? a).
  destruct b0.
  apply : le_min_fold_skip.
  assumption.
  by apply : le_dec.
  auto.
  simpl.
  remember (a0 <=? a).
  destruct b0.
  pose (le_dec (eq_sym Heqb0)).
  remember (b <=? a).
  destruct b0.
  pose (le_dec (eq_sym Heqb1)).
  by apply : H.
  by apply : le_min_fold_skip.
  remember (b <=? a).
  destruct b0.
  symmetry.
  apply : le_min_fold_skip.
  auto.
  by apply : le_dec.
  auto.
Qed.


Theorem min_inc : forall xs a b, 
  fold_left (fun x y0 : nat => if x <=? y0 then x else y0) (b :: xs) a <=
      fold_left (fun x y0 : nat => if x <=? y0 then x else y0) xs b.
 elim.
 intros.
 simpl.
 remember (a <=? b).
 destruct b0.
 exact (le_dec (eq_sym Heqb0)).
 auto.
 intros.
 pose (H a0 b).
 simpl;simpl in l0.
 move : l0.
 remember (a0 <=? b).
 destruct b0.
 pose(le_dec (eq_sym Heqb0)).
 intros.
 remember (b <=? a).
 destruct b0.
 pose (le_dec (eq_sym Heqb1)).
 assert(a0 <= a) by lia.
 by rewrite (dec_le H0).
 pose (le_dec_false (eq_sym Heqb1)).
 remember (a0 <=? a).
 destruct b0.
 apply : min_le_reduce.
 by apply : le_dec.
 auto.
 auto.
Qed.

Theorem min_itself : forall {A} xs b (f : A -> A -> A), (forall a b, f a b = a \/ f a b = b) ->
 In (fold_left f xs b) (b :: xs).
  move => A.
  elim.
  intros.
  by left.
  intros.
  simpl.
  destruct (H a _ H0).
  destruct (H b _ H0).
  destruct (H0 b a).
  rewrite -> H3.
  by left.
  rewrite <- H3 in H1 at 2.
  by right;left.
  destruct (H0 b a).
  right;right.
  rewrite -> H3.
  exact H2.
  right;left.
  rewrite H3.
  exact H1.
  destruct (H b _ H0).
  destruct (H0 b a).
  left.
  by rewrite H3.
  right;right.
  by rewrite H3.
  destruct (H0 b a).
  rewrite -> H3; intuition.
  rewrite -> H3; intuition.
Qed.

Theorem min_In : forall xs, xs <> [] -> In (min xs) xs.
  intros.
  unfold min.
  destruct xs.
  intuition.
  simpl.
  rewrite (dec_le (le_n n)).
  apply min_itself.
  intros.
  destruct (a <=? b).
  by left.
  by right.
Qed.

Theorem min_forall : forall xs y, In y xs -> min xs <= y.
  intros.  
  generalize dependent y.
  induction xs.
  intros.
  inversion H.
  intros.
  destruct H.
  rewrite <- H.
  unfold min.
  simpl.
  rewrite Nat.leb_refl.
  apply : left_le_min.
  destruct xs.
  inversion H.
  rewrite <- (IHxs _ H).
  unfold min.
  simpl.
  rewrite Nat.leb_refl.
  rewrite Nat.leb_refl.
  exact (min_inc xs a n).
Qed.
 
Theorem manual_min_1_0 : forall xs, ~ In 0 xs -> In 1 xs -> 
     min xs = 1.
  (* This proof is very manual, however it fits perfectly identifying one as minimum
       in a non-nullable list with a indentity *)
  intros.
  pose (min_forall H0).
  unfold min.
  destruct xs.
  inversion H0.
  simpl.
  move : l.
  unfold min.
  simpl.
  rewrite Nat.leb_refl.
  move => H'.
  inversion H'.
  auto.
  subst.
  inversion H2.
  contradiction H.
  rewrite <- H3.
  apply : (min_itself xs n).
  intros.
  destruct (a <=? b).
  intuition.
  intuition.
Qed.

Theorem desc_cons : forall xs a, descending (a :: xs) -> forall y, In y (a :: xs) -> y <= a.
  elim.
  intros.
  destruct H0.
  subst; auto with arith.
  inversion H0.
  intros.
  destruct H1.
  subst.
  by destruct H0.
  destruct H0.
  pose (H _ H2 _ H1).
  by rewrite <- H0.   
Qed.

Theorem descending_0 : 
  forall xs k, descending xs -> In k xs -> (forall y, In y xs -> y <= k) -> nth 0 xs k = k.
    elim.
    intros.
    trivial.
    intros.
    destruct H1.
    subst.
    auto.
    simpl.
    assert (descending l).
    destruct l.
    inversion H1.
    by destruct H0.
    assert (forall y : nat, In y l -> y <= k).
    intros.
    apply : H2.
    by right.
    pose (H _ H3 H1 H4).
    assert (In a (a :: l)).
    by left.
    pose (H2 _ H5).
    destruct l.
    inversion H1.
    destruct H0.
    simpl in e.
    inversion l0.
    trivial.
    lia.
Qed.

Theorem descending_min_pred :
   forall xs b, descending xs -> xs <> [] -> min xs = last xs b.
  intros.
  induction xs.
  intuition.
  unfold min.
  simpl.
  rewrite (dec_le (le_n a)).
  destruct xs.
  auto with arith.
  assert(min (n :: xs) = last (n :: xs) b).
  apply : IHxs.
  by destruct H.
  by [].
  unfold min in H1.
  simpl;simpl in H1.
  rewrite (dec_le (le_n n)) in H1.
  remember (a <=? n).
  destruct b0.
  destruct H.
  simpl in H1.
  rewrite <- H1.
  pose (le_dec (eq_sym Heqb0)).
  inversion H.
  by subst.
  lia.
  by rewrite <- H1.
Qed.

Theorem descending_max_0 : forall xs b, descending xs -> xs <> [] -> max xs = nth 0 xs b.
   intros.
   destruct xs.
   intuition.
   assert (In (max (n :: xs)) (n :: xs)).   
   unfold max.
   apply : min_itself.
   intros.
   destruct (a <=? b0).
   intuition.
   intuition.
   assert (forall y : nat, In y (n :: xs) -> y <= max (n :: xs)).
   intros.
   by apply : max_prop.
   by rewrite <- (@descending_0 _ (max (n :: xs)) H H1 H2).
Qed.
   
Theorem disibility_eqless_itself : forall x k, In k (get_factors (S x) (S x)) -> k <= S x.
  intros.
  by apply : (@le_factors (S x) _ (S x)).
Qed.

Theorem max_div_is_itself : forall x, max (get_factors (S x) (S x)) = S x.
  intros.
  destruct (itself_1_factor x).
  rewrite (@descending_max_0 _ (S x)).
  apply : factors_descending.
  destruct ((get_factors (S x) (S x))).
  inversion H.
  congruence.
  rewrite descending_0.
  apply : factors_descending.
  assumption.
  apply : disibility_eqless_itself.
  auto.
Qed.

Theorem min_factors : forall x, @min (get_factors (S x) (S x)) = 1.
  intros.
  assert(In 1 (get_factors (S x) (S x))).
  by destruct (itself_1_factor x).
  assert (forall z x, ~ In 0 (get_factors x (S z))).
  clear H.
  elim.
  intros.
  simpl.
  destruct (div2 x0 1).
  move => H.
  inversion H.
  inversion H0.
  inversion H0.
  move => H.
  inversion H.
  intros.
  move => H'.
  simpl in H'.
  destruct (div2 x0 (S (S n))).
  destruct H'.
  inversion H0.
  destruct (H x0 H0).
  destruct (H x0 H').
  by apply : manual_min_1_0.
Qed.


Definition leb_last : forall x, pred (S x) < (S x).
  elim.
  auto with arith.
  intros.
  apply : le_n.
Defined.

Theorem _1_is_first_factor : forall x,
   last (get_factors (S x) (S x)) 1 = 1.
  intros.
  pose(factors_descending (S x) (S x)).
  rewrite <- (min_factors x).
  move : d.
  generalize dependent (get_factors (S x) (S x)).
  clear x.
  intros.
  induction l. 
  trivial.
  intros.
  destruct l.
  unfold min; simpl.
  by rewrite Nat.leb_refl.
  destruct d.
  pose (IHl H0).
  move : e.
  unfold min; simpl.
  do 2! rewrite Nat.leb_refl.
  remember (a <=? n).
  destruct b.
  pose (le_dec (eq_sym Heqb)).
  inversion H.
  subst.
  auto.
  lia.
  auto.
Qed.

(*
Theorem _itself_is_first_factor : forall x,
   hd (S x) (get_factors (S x) (S x)) = S x.
  intros.
  pose(factors_descending (S x) (S x)).
  rewrite <- (min_factors x).
  move : d.
  generalize dependent (get_factors (S x) (S x)).
  clear x.
  intros.
  induction l. 
  trivial.
  intros.
  destruct l.
  unfold min; simpl.
  by rewrite Nat.leb_refl.
  destruct d.
  pose (IHl H0).
  move : e.
  unfold min; simpl.
  do 2! rewrite Nat.leb_refl.
  remember (a <=? n).
  destruct b.
  pose (le_dec (eq_sym Heqb)).
  inversion H.
  subst.
  auto.
  lia.
  auto.
Qed.
*)

Theorem last_is_nth : forall {A} (x : list A) y, nth (pred (length x)) x y = last x y.
  intros. 
  induction x.
  trivial.
  destruct x.
  by simpl.
  simpl in *.
  exact IHx.
Qed.

Theorem factor_composite : forall x,
   length (get_factors (S (S x)) (S (S x))) > 2 -> {y & (divisible (S (S x)) y ** y <> 1 /\ y <> S (S x))}.
  intros.
  pose (_2_minimuim_factors x).
  
  destruct (lt_eq_lt_dec 2 (length (get_factors (S (S x)) (S (S x))))).
  destruct s.
  exists (nth 1 (get_factors (S (S x)) (S (S x))) 1).
  constructor.
  apply : (@le_factors_inhabited' _ (S (S x)) _ _).  
  clear l l0.
  destruct ((get_factors (S (S x)) (S (S x)))).
  inversion H.
  destruct l.
  inversion H.
  inversion H1.
  intuition.
  constructor.
  pose (_1_is_first_factor (S x)).
  rewrite <- last_is_nth in e.
  assert (1 < pred (length (get_factors (S (S x)) (S (S x))))) by lia.
  assert (pred (length (get_factors (S (S x)) (S (S x)))) <
   length (get_factors (S (S x)) (S (S x)))) by lia.
  pose (strong_distinction 1 (factors_descending' (S (S x)) (S (S x))) H0 H1).
  move => H'.
  rewrite -> H' in l1.
  rewrite <- l1 in H0.
  lia.
  pose (max_div_is_itself (S x)).
  move => H'.
  rewrite <- e in H' at 3.
  rewrite (@descending_max_0 _ 1) in H'.
  apply : factors_descending.
  move : H l l0 e.
  destruct (get_factors (S (S x)) (S (S x))).
  intros.
  inversion H.
  congruence.
  assert (nth 1 (get_factors (S (S x)) (S (S x))) 1 <
     nth 0 (get_factors (S (S x)) (S (S x))) 1).
  apply : strong_distinction.
  apply : factors_descending'.
  auto.
  auto.
  lia.
  rewrite e in H.
  destruct (Gt.gt_irrefl _ H).
  destruct (Gt.gt_asym _ _ H l0).
Qed.

Theorem composite_correspondence : forall x, prime_dec (S (S x)) = false -> composite (S (S x)).
  intros.
  unfold prime_dec in H.
  move => H'.
  destruct H'.
  assert (length (get_factors (S (S x)) (S (S x))) > 2).
  pose (_2_minimuim_factors x).
  move : l H.
  generalize dependent (get_factors (S (S x)) (S (S x))).
  intros.
  inversion l0.
  pose (eq_rel_false H).
  destruct (n (eq_sym H1)).
  lia.
  destruct (factor_composite H0).
  destruct p.
  exists x0.
  intuition.
Qed.

Theorem prime_decibility : forall x, {prime (S (S x))} + {composite (S (S x))}.
  intros.
  set (prime_dec x).
  remember (prime_dec (S (S x))).
  destruct b0.
  by left; apply : prime_correspondence.
  by right; apply : composite_correspondence.
Qed.

Theorem composite_prime_dec : forall x, composite (S (S x)) -> prime_dec (S (S x)) = false.
  intros.
  assert(~ length (get_factors (S (S x)) (S (S x))) = 2).
  move => H'.
  destruct H.
  apply : prime_correspondence.
  unfold prime_dec.
  rewrite H'.
  apply : eq_refl.
  unfold prime_dec.
  by apply : false_eq_rel.
Qed.

Theorem prime_number_dec : forall x, prime (S (S x)) -> prime_dec (S (S x)) = true.
  intros.
  unfold prime_dec.
  destruct (lt_eq_lt_dec (length (get_factors (S (S x)) (S (S x)))) 2).
  destruct s.
  pose (_2_minimuim_factors x); lia.
  by rewrite e.
  assert(prime_dec (S (S x)) = false).
  unfold prime_dec.
  inversion l.
  by simpl; rewrite <- H1.
  destruct m.
  by simpl; rewrite <- H0.
  destruct m.
  simpl in l; rewrite <- H0 in l; lia.
  by simpl; rewrite <- H0.
  destruct (composite_correspondence H0 H).
Qed.

Theorem constructive_prime_dec : forall x, composite (S (S x)) -> {y & (divisible (S (S x)) y ** y <> 1 /\ y <> S (S x))}.
  intros.
  apply : factor_composite.
  pose (composite_prime_dec H).
  pose (_2_minimuim_factors x).
  unfold prime_dec in e.
  pose (eq_rel_false e).
  lia.
Qed.

Theorem constructive_prime_number : 
  forall x, prime (S (S x)) -> forall y, divisible (S (S x)) y -> y = 1 \/ y = (S (S x)).
  intros.
  by apply : (uniquess_2factors (eq_rel (prime_number_dec H))).
Qed.

Theorem exists_factors_le_2 : forall x, composite (S (S x)) ->
   {H | H.1 >= 2 /\ H.2 >= 2 /\ H.1*H.2 = (S (S x))}.
  intros.
  destruct (constructive_prime_dec H).
  destruct p.
  destruct a.
  destruct d.
  exists (x0, x1).
  simpl.
  constructor.
  destruct x0.
  lia.
  destruct x0.
  lia.
  lia.
  constructor.
  destruct x1.
  lia.
  destruct x1.
  lia.
  lia.
  exact e.
Qed.

Theorem cicle_mul_absurd : forall x y, ~ S x * (S (S y)) = S x.
  intros.
  move => H.
  generalize dependent y.
  induction x.
  intros.
  simpl in H.
  rewrite <- plus_n_O in H.
  inversion H.
  intros.
  destruct y.
  lia.
  apply : (IHx y).
  lia.
Qed.

Theorem prime_prime_dec : forall x, prime (S (S x)) -> prime_dec (S (S x)) = true.
   intros.
   assert(~ prime_dec (S (S x)) = false).
   move => H'.
   unfold prime_dec in H'.
   pose (_2_minimuim_factors x).
   pose (eq_rel_false H').
   assert(length (get_factors (S (S x)) (S (S x))) > 2) by lia.
   destruct (factor_composite H0).
   destruct H.
   destruct p.
   destruct a.
   by exists x0.
   destruct (prime_dec (S (S x))).
   trivial.
   intuition.
Qed.

Compute Nat.div_mod.

Theorem prime_prop_strong : forall x, prime (S (S x)) -> (forall y, divisible (S (S x)) y -> y = 1 \/ y = (S (S (x)))).
  move => x H.
  apply : (@uniquess_2factors _ (eq_rel (prime_prime_dec H))).
Qed.

Theorem div_completeness : forall x y, y <> 0 -> {H | x = y*H.1 + H.2 /\ H.2 < y}.
  intros.
  exists (x/y, x mod y).
  constructor.
  by apply : Nat.div_mod.
  simpl.
  assert(0 <= x /\ 0 < y).
  constructor.
  auto with arith.
  destruct y.
  intuition.
  auto with arith.
  destruct H0.
  pose (Nat.mod_bound_pos x y H0 H1).
  destruct a.
  exact H3.
Qed.

Notation "( x | y )" := (Nat.divide x y) (at level 0) : nat_scope.

Definition divide_to_divisible : forall x y, divisible x y -> (y | x).
 intros.
 destruct H.
 exists x0.
 by rewrite Nat.mul_comm.
Qed.

Require Import Coq.Init.Logic.
Require Import Coq.Sorting.Mergesort.

Definition divisible_to_divide : forall x y, (y | x) -> divisible x y.
 intros.
 destruct x.
 by exists 0.
 destruct(Decibility_division x y).
 exact d.
 assert(~ indivisible (S x) y).
 move => H'.
 destruct H. 
 destruct i.
 exists x0.
 lia.
 intuition.
Qed.


Require Import Coq.Sorting.Mergesort.
Require Import List Setoid Permutation Sorted Orders.


Export NatSort .

Compute Sorted_merge.

(* A set {x | x divides f(x)} is just a function going to a decision whether p is inside 
  of factors of x or not *)

Definition Factors p (f : nat -> nat) :=  forall x, {In p (get_factors (f x) (f x))} + {~ In p (get_factors (f x) (f x))} .

Definition Set_Factors p (f : nat -> nat) :
   Factors p f := fun x =>
  in_dec Nat.eq_dec p (get_factors (f x) (f x)).

Fixpoint get_factors_by_set (x : nat) p f (H : Factors p f) {struct x} : list nat.
refine (match x with
         |0 => _
         |(S n) => _
       end).
destruct (H 0).
exact [0].
exact [].
destruct (H (S n)).
refine (S n :: get_factors_by_set n p f H).
refine (get_factors_by_set n p f H).
Defined.

Definition elim_dec {A B} (x : {A} + {B}) (H : A -> Type) (H' : B -> Type) : Type.
destruct x.
exact (H a).
exact (H' b).
Defined.

Definition In_Set {p f} (H : Factors p f) := fun y => elim_dec (H y) (fun _ => True) (fun _ => False).

Definition min_set {p f y} (H : Factors p f) : In_Set H y -> nat := fun x => min (get_factors_by_set y H).

Theorem exists_set_by_In : 
  forall {y p f h} (H : Factors p f) (H' : In h (get_factors_by_set y H)), In_Set H h.
  unfold In_Set.
  unfold elim_dec.
  elim.
  intros.
  simpl in H'.
  destruct (H 0).
  simpl in H'.
  remember (H h).
  destruct s.
  exact I.
  destruct H'.
  subst;intuition.
  intuition.
  inversion H'.
  intros.
  simpl in H'.
  destruct (H (S n)).
  remember (H h).
  destruct s.
  exact I.
  destruct H'.
  subst; intuition.
  pose (X _ _ _ _ H0).
  by rewrite <- Heqs in y.
  by apply : X.
Qed.

Theorem min_set_factors_In : forall {p f y} (H : Factors p f) (H' : In_Set H y), In_Set H (min_set H').
  intros.
  unfold In_Set.
  unfold In_Set in H'.
  unfold min_set.
  assert (length (get_factors_by_set y H) > 0).
  induction y.
  simpl.
  by destruct (H 0).
  simpl.
  destruct (H (S y)).
  simpl.
  auto with arith.
  by apply : IHy.
  assert((get_factors_by_set y H) <> []).
  destruct (get_factors_by_set y H).
  inversion H0.
  congruence.
  pose (min_In H1).
  generalize dependent i.
  clear H0 H1.
  intros.
  exact (exists_set_by_In i).
Qed.

Theorem no_inhabitant_less_min : forall {p f y} (H : Factors p f) (H' : In_Set H y),
    min_set H' <= y.
  intros.
  unfold min_set.
  unfold min.
  unfold In_Set in H'.
  destruct y.
  by simpl; destruct (H 0).
  simpl.
  remember (H (S y)).
  destruct s.
  simpl.
  rewrite (dec_le (le_n y)).
  apply : left_le_min.
  intuition.
Qed.

Theorem hd_get_factors_by_set : 
  forall {p f} (H : Factors p f) y, hd 0 (get_factors_by_set y H) <= y.
  intros.
  induction y.
  simpl.
  by destruct (H 0).
  simpl.
  destruct (H (S y)).
  auto with arith.
  rewrite -> IHy.
  auto with arith.
Qed.

Theorem set_factors_sorted : forall {p f y} (H : Factors p f) (H' : In_Set H y),
  descending (get_factors_by_set y H).
  intros.
  unfold In_Set in H'.
  destruct (H y).
  clear H'.
  generalize dependent (f y).
  unfold descending.
  induction y.
  by intros;simpl;destruct (H 0).
  intros.
  pose (IHy _ i).
  simpl.
  remember (H (S y)).
  destruct s.
  destruct y.
  simpl.
  destruct (H 0).
  constructor.
  auto with arith.
  by simpl.
  auto with arith.
  simpl.
  remember (H (S y)).
  destruct s.
  constructor.
  auto with arith.
  simpl in p0.
  by rewrite <- Heqs0 in p0.
  simpl in p0.
  rewrite <- Heqs0 in p0.
  remember (get_factors_by_set y H).
  destruct l.
  auto with arith.
  constructor.
  pose (hd_get_factors_by_set H y).
  rewrite <- Heql in l0.
  simpl in l0.
  auto with arith.
  exact p0.
  exact p0.
  inversion H'.
Qed.

Theorem factors_not_list_empty : forall {p f y} (H : Factors p f) (H' : In_Set H y),
  (get_factors_by_set y H) <> [].
  intros.
  unfold In_Set in H'.
  destruct (H y).
  clear H'. 
  induction y.
  simpl.
  destruct (H 0).
  congruence.
  intuition.
  simpl.
  remember (H (S y)).
  simpl in i.
  destruct s.
  congruence.
  intuition.
  inversion H'.
Qed.

Theorem factors_not_list_empty_succ : forall {p f y} (H : Factors p f),
  (get_factors_by_set y H) <> [] -> (get_factors_by_set (S y) H) <> [] .
  intros.
  induction y.
  simpl.
  simpl in H0.
  destruct (H 0).
  destruct (H 1).
  congruence.
  congruence. 
  intuition.
  simpl.
  simpl in H0.
  destruct (H (S (S y))).
  congruence.
  exact H0.
Qed.

Theorem succ_factors_preserves_order : 
  forall {y p f} (H : Factors p f) h, (get_factors_by_set y H) <> [] -> 
   last (get_factors_by_set y H) h = last (get_factors_by_set (S y) H) h.
  elim.
  intros.
  simpl.
  simpl in H0.
  destruct(H 0).
  by destruct (H 1).
  intuition.
  intros.
  simpl.
  simpl in H1.
  remember (H0 (S n)).
  remember (H0 (S (S n))).
  destruct s.
  destruct s0.
  trivial.
  trivial.
  destruct s0.
  destruct (get_factors_by_set n H0).
  intuition.
  trivial.
  trivial.
Qed.

  
Theorem factors_preserve_last : forall {y z p f} (H : Factors p f) h, y <= z ->
  get_factors_by_set y H <> [] -> last (get_factors_by_set y H) h = last (get_factors_by_set z H) h.
  intros.
  assert(z = y + (z - y)) by lia.
  generalize dependent (z - y).
  intros.
  rewrite H2.
  clear H2 H0.
  generalize dependent y.
  induction n.
  intros.
  by rewrite <- plus_n_O.
  intros.
  pose (IHn _ H1).
  rewrite Nat.add_comm.
  rewrite e.
  replace (S n + y) with (S (y + n)).
  apply : succ_factors_preserves_order.
  clear e IHn.
  induction n.
  by rewrite <- plus_n_O.
  rewrite Nat.add_comm.
  apply : factors_not_list_empty_succ.
  fold add.
  by rewrite Nat.add_comm.
  lia.
Qed.
  
Theorem In_Set_In_Factors : forall {p f y z} (H : Factors p f) (H' : In_Set H y) ,
   In_Set H z -> min (get_factors_by_set y H) = min (get_factors_by_set z H).

  intros.
  pose (set_factors_sorted H').
  pose (set_factors_sorted X).
  rewrite (descending_min_pred 0 d).
  by apply : factors_not_list_empty.
  rewrite (descending_min_pred 0 d0).
  by apply : factors_not_list_empty.
  destruct (le_lt_dec y z).
  apply : factors_preserve_last.
  assumption.
  by apply : factors_not_list_empty.
  symmetry.
  apply : factors_preserve_last.
  auto with arith.
  by apply : factors_not_list_empty.
Qed.

Lemma less_mul : forall x y z, x < x * (S y) + (S z).
  intros.
  elim/@nat_double_ind : x/y .
  intros; lia.
  intros; lia.
  intros; lia.
Qed.

Lemma auxiliar_le_mul : forall x n a, (S (S x)) <= S x * S n + S a.
  intros.
  elim/@nat_double_ind : x/n.
  intros; lia.
  intros; lia.
  intros; lia.
Qed.

Lemma auxiliar_less_mul : forall {x y} z, x <= y <-> x * S z <= y * S z.
  intros.
  constructor.
  elim/@nat_double_ind : x/y.
  intros; lia.
  intros; lia.
  intros; lia.
  elim/@nat_double_ind : x/y.
  intros; lia.
  intros.
  simpl in H.
  inversion H.
  intros; lia.
Qed.

Theorem auxiliar_less : forall x b p x', b + x * (S p) <= x' * (S p) -> x <= x'.
  intros.
  elim/@nat_double_ind : x/x' H.
  intros;lia.
  intros.
  simpl in H.
  destruct b.
  lia.
  lia.
  intros;lia.
Qed.

Lemma euclides_lemma : forall p a b, prime (S (S p)) ->
   divisible ((S a) * (S b)) (S (S p)) ->
       divisible (S a) (S (S p)) + divisible (S b) (S (S p)).
  intros.
  destruct (Decibility_division a (S (S p))).
  by left.
  pose (Set_Factors (S (S p)) (fun x => (S x)*(S b))).
  assert (In_Set f (S p)).
  unfold In_Set.
  unfold f.
  unfold Set_Factors.
  remember ((in_dec Nat.eq_dec (S (S p)) (get_factors ((S (S p)) * (S b)) ((S (S p)) * (S b))))).
  destruct s.
  done.
  assert (In (S (S p)) (get_factors (S (S p) * (S b)) (S (S p) * (S b)))).
  apply : all_factors_inhabits.
  fold add; fold mul.
  by exists (S b).
  intuition.
  assert(forall x, In_Set f x -> (S (min_set X) * S b | S x * S b)).
  move => x X0.
  assert(S (min_set X) <> 0) by auto with arith.
  destruct (div_completeness (S x) H1).
  assert((S (S p)) | (S x*S b)).
  unfold In_Set in X0.
  destruct (f x).
  destruct (list_factors_inhabited i0).
  by exists x1; symmetry; rewrite Nat.mul_comm.
  destruct X0.
  assert ((S (S p)) | S (min_set X)*(S b)).
  pose (min_set_factors_In X).
  unfold In_Set in i0.
  unfold elim_dec in i0.
  move : i0.
  remember (f (min_set X)).
  destruct s.
  move => I.
  destruct (list_factors_inhabited i0).
  by exists x1; symmetry; rewrite Nat.mul_comm.
  intuition.
  destruct x0.
  destruct a0.
  simpl in H4; simpl in H5.
  destruct n0.
  rewrite <- plus_n_O in H4. 
  exists n.
  rewrite H4.
  assert ((n + min_set X * n) = (S (min_set X) * n)) by lia.
  rewrite H6.
  lia.
  assert ((S (S p)) | (S n0 * (S b))).
  destruct H2.
  destruct H3.
  assert ((n + min_set X * n) = (S (min_set X) * n)) by lia.
  rewrite H6 in H4; clear H6.
  assert(S x*b - (S (min_set X) * n)*b = S n0*b) by lia.
  destruct n.
  rewrite <- mult_n_O in H4.
  simpl in H4.
  rewrite <- H4.
  by exists x0.
  assert(S (min_set X) < S x).
  rewrite H4.
  apply : less_mul.
  assert(S (S p) * x1 * (S n0) = S (min_set X) * (S n0) * (S b)).
  apply (f_equal (fun x => x*(S n0))) in H3; lia.
  exists (x0 - (x1 * S n)).
  replace ((x0 - (x1 * S n)) * S (S p)) with ((S (S p) * (x0 - (x1 * S n)))) by lia.
  rewrite Nat.mul_sub_distr_l.
  replace (S (S p) * x0) with (x0 * (S (S p))) by lia.
  rewrite <- H2.
  replace (S (S p) * (x1 * S n)) with (x1 * S (S p) * S n) by lia.
  rewrite <- H3.
  lia.
  assert(In_Set f n0).
  unfold In_Set.
  destruct (f n0).
  exact I.
  destruct n1.
  destruct H6.
  apply : all_factors_inhabits.
  fold add; fold mul.
  exists x0.
  lia.
  pose (no_inhabitant_less_min X1).
  pose (no_inhabitant_less_min X0).    
  assert(min_set X < x).
  apply : le_S_n.
  rewrite H4.
  assert(n + (min_set X) * n + S n0 = (S (min_set X)) * n + S n0) by lia.
  rewrite H7.
  destruct n.
  assert(x = n0) by lia.
  rewrite -> H8 in l0.
  unfold min_set in H5.
  unfold min_set in l0.
  rewrite <- (In_Set_In_Factors X X0) in l0.
  unfold "<" in H5.
  apply le_S_n in H5.
  rewrite <- H5 in l0.
  lia.
  apply : auxiliar_le_mul.
  unfold min_set in l.
  unfold min_set in H5.
  unfold min_set in l0.
  unfold min_set in H7.
  rewrite <- (In_Set_In_Factors X X1) in l.
  assert(S n0 <= (min (get_factors_by_set (S p) f))).
  by apply : le_S_n.
  lia.
  assert(In_Set f a).
  unfold In_Set.
  destruct (f a).
  exact I.
  destruct H0.
  assert(In (S (S p)) (get_factors (S a * S b) (S a * S b))).
  apply : all_factors_inhabits.
  fold add; fold mul.
  by exists x.
  intuition.
  pose (H1 _ X).
  pose (H1 _ X0).
  assert((S (min_set X) | S (S p))).
  destruct d.
  exists x.
  assert(S b * S (S p) = S b * (x * (S (min_set X)))) by lia.
  apply : (injective_mult H3).
  assert((S (min_set X) | S a)).
  destruct d0.
  exists x.
  assert(S b * S a = S b * (x * (S (min_set X)))) by lia.
  apply : (injective_mult H4).
  right.
  clear d d0.
  apply : divisible_to_divide.
  destruct (constructive_prime_number H (divisible_to_divide H2)).
  assert (In_Set f 0).
  inversion H4.
  apply : min_set_factors_In.
  unfold In_Set in X1.
  destruct (f 0).
  pose (divide_to_divisible (list_factors_inhabited i0)).
  by rewrite -> Nat.mul_1_l in d.
  inversion X1.
  destruct H3.
  rewrite H4 in H3.
  destruct i.
  exists x.
  lia.
Qed.

Theorem every_non_prime_have_prime_factors : forall (x : nat), x >= 2 -> ~ prime x -> {y | prime (S (S y)) /\ isTotal (div2 x (S (S y))) }.
  apply : (Wf.well_founded_induction (Wf_nat.lt_wf)).
  intros.
  destruct x.
  assert(~ 0 >= 2) by lia; intuition.
  destruct x.
  assert(~ 1 >= 2) by lia; intuition.
  destruct (prime_decibility x).
  intuition.
  destruct (exists_factors_le_2 c).
  destruct a.
  destruct H3.
  assert(x0 ´ 1 < S (S x)).
  destruct (Nat.eq_dec (x0 ´ 1) (S (S x))).
  rewrite e in H4.
  destruct (x0 ´ 2).
  lia.
  destruct n.
  inversion H3.
  inversion H6.
  destruct (cicle_mul_absurd H4).
  destruct ( x0 ´ 1).
  inversion H2.
  destruct ( x0 ´ 2).
  inversion H3.
  destruct (div_less H4).
  inversion H5.
  subst.
  destruct n1.
  inversion H3.
  inversion H8.
  lia.
  lia.
  destruct (x0 ´ 1).
  assert(~ 0 >= 2) by lia; intuition.
  destruct n.
  assert(~ 1 >= 2) by lia; intuition.
  destruct (prime_decibility n).
  exists n.
  constructor.
  assumption.
  apply : definition_div_to_induction.
  by exists (x0.2).
  destruct (H _ H5 H2 c0).
  destruct a.
  exists x1.
  constructor.
  assumption.
  destruct (induction_div_to_definition H7).
  apply : definition_div_to_induction.
  unfold divisible.
  exists (x2*x0 ´ 2).
  lia.
Qed.

Definition primes x := x <> [] /\ forall k, In k x -> k > 1 /\ prime k.

Definition product (xs : list nat) : nat.
destruct xs.
exact 1.
exact (fold_left Nat.mul xs n).
Defined.

Lemma strong_div_less : forall x y z, S (S x) * S (S y) = S z -> S (S x) < S z /\ S (S y) < S z.
  have : forall y z, ~ S z * S (S y) = S z.
  intros.
  move => H.
  elim/@nat_double_ind : z/y H.
  intros; lia.
  intros; lia.
  intros; lia.
intros.
destruct (div_less H).
inversion H0.
subst.  
destruct (x _ _ H).
inversion H1.
subst.
rewrite Nat.mul_comm in H.
destruct (x _ _ H).
lia.
Qed.

Theorem list_In_concat : forall A (xs : list A) ys k, In k xs -> In k (xs ++ ys).
  intros.
  generalize dependent ys.
  induction xs.
  intros;intuition.
  intros;destruct H.
  subst.
  by left.
  right.
  by apply : IHxs.
Qed.

Theorem list_In_comm : forall A (xs : list A) ys k, In k (xs ++ ys) -> In k (ys ++ xs).  
  intros.
  have : forall l k xs, In k (l ++ k :: xs).
  move => T l.
  induction l.
  intros.
  by left.
  intros.
  right.
  apply : (IHl _ xs0).
  destruct ys.
  intros.
  by rewrite app_nil_r in H.
  move => H2.
  generalize dependent ys.
  induction xs.
  intros;intuition.
  intros;destruct H.
  right.
  rewrite H.
  apply : H2.
  have : 
    forall ys xs a a0 k, In k (a :: a0 :: (ys ++ xs)) -> In k ((a :: ys) ++ a0 :: xs).
  clear a0 xs a IHxs k ys H.  
  move => T ys.
  induction ys.
  intros.
  destruct H.
  subst.
  by left.
  by right.
  intros.
  destruct H.
  subst.
  by left.
  destruct H.
  simpl.
  rewrite H.
  right;right.
  apply : H2.
  destruct H.
  simpl.
  intuition.
  right.
  apply : IHys.
  by right;right.
  move => H3.
  pose (IHxs _ H).
  apply : H3.
  destruct i.
  rewrite H0.
  by left.
  by right;right.
Qed.


Theorem list_or_In: forall A (xs : list A) ys k, In k (xs ++ ys) -> In k xs \/ In k ys.  
  move => A.
  elim.
  intros.
  by right.
  intros.
  destruct H0.
  subst.
  by left;left.
  destruct (H _ _ H0). 
  by left;right.
  by right.
Qed.

Theorem fold_distr : forall l x y,
  fold_left Nat.mul l (x * y) = y *  fold_left Nat.mul l x.
  intros.
  rewrite Nat.mul_comm.
  generalize dependent x.
  generalize dependent y.
  induction l.
  auto.
  intros.
  pose (IHl y (x * a)).
  simpl.
  replace (y * (x * a)) with (y * x * a) in e.
  exact e.
  lia.
Qed.

Theorem product_unfold_aux : forall x y a b,
  fold_left Nat.mul (x ++ b :: y) a = fold_left Nat.mul x a * fold_left Nat.mul y b.
  elim.
  intros.
  simpl.
  rewrite Nat.mul_comm.
  by rewrite fold_distr.
  intros.
  simpl.
  pose (H y a0 b).
  do 2! rewrite fold_distr.
  rewrite e.
  lia.
Qed.

Theorem product_unfold : forall x y, x <> [] -> y <> [] ->
  product (x ++ y) = product x * (product y).
  intros.
  destruct x.
  intuition.
  destruct y.
  intuition.
  simpl.
  apply : product_unfold_aux.
Qed.

Definition list_2_rect (P : list nat -> Prop) (H : P []) (H1 : forall a, P [a])
  (H3 : forall a b xs, P xs -> P (a :: b :: xs)) : forall xs, P xs.
 refine(fix rect_S xs : P xs := _).
 refine(match xs with
          | [] => _
          | a :: [] => _
          | a :: b :: xs => _ 
    end).
 apply : H.
 apply : H1.
 apply : H3.
 exact (rect_S xs).
Defined.

 
Theorem euclides_product : forall p xs, prime (S (S p)) -> primes xs -> 
  divisible (product xs) (S (S p)) -> {z & In z xs /\ (S (S p) | z)}.
  intros.
  destruct H0.
  induction xs.
  intuition.
  destruct xs.
  destruct H1.
  exists a.
  constructor.
  by left.
  exists x.
  simpl in e.
  by rewrite Nat.mul_comm.
  simpl in H1.
  destruct a.
  destruct (H2 0).
  by left.
  assert(False) by lia; easy.
  rewrite Nat.mul_comm in H1.
  rewrite fold_distr in H1.
  assert( divisible (product (n :: xs)) (S (S p)) ->
       {z : nat & In z (n :: xs) /\ (S (S p) | z)}).
  apply : IHxs.
  congruence.
  move => k H'.
  apply : H2.
  by right.
  simpl in H3.
  destruct (fold_left Nat.mul xs n).
  destruct H3.
  by exists 0.
  exists x.
  destruct a0.
  constructor.
  by right.
  assumption.
  destruct (euclides_lemma H H1).
  exists (S a).
  constructor.
  by left.
  destruct d.
  exists x; lia.
  destruct (H3 d).
  destruct a0. 
  exists x.
  constructor.
  destruct H4.
  rewrite H4.
  by right;left.
  by right;right.
  assumption.
Qed.
  
Theorem arithmetic_existence : forall x, x > 1 -> {xs & primes xs /\ product xs = x}.
apply : (Wf.well_founded_induction (Wf_nat.lt_wf)).
intros.
do 2! (destruct x; auto with arith).
destruct x.
exists [2].
do 2! constructor.
congruence.
move => k H'.
destruct H' as [H1 | H2].
rewrite <- H1.
constructor.
auto.
by apply : prime_correspondence.
intuition.
destruct (prime_decibility (S x)).
exists [(S (S (S x)))].
do 2! constructor.
congruence.
move => K H'.
destruct H'.
by rewrite <- H1.
intuition.
destruct (constructive_prime_dec c); destruct p.
destruct d.
assert(x0 < S (S (S x))).
destruct x0. lia.
destruct x1. lia.
destruct (div_less e).
lia.
destruct x0.
simpl in e.
inversion e.
destruct x1.
rewrite Nat.mul_comm in e.
inversion e.
destruct a.
destruct x0.
intuition.
assert(S (S x0) > 1) by lia.
destruct x1.
rewrite Nat.mul_1_r in e.
rewrite e in H1.
destruct (Nat.lt_irrefl _ H1).
assert(S (S x1) > 1) by lia.
assert(S (S x1) < S (S (S x))).
by destruct (strong_div_less e).
pose (H _ H1 H4).
pose (H _ H6 H5).
destruct s.
destruct s0.
exists (x2 ++ x3).
destruct a.
destruct a0.
destruct H7; destruct H9.
constructor.
constructor.
destruct x2.
congruence.
simpl; congruence.
move => k H'.
destruct (list_or_In H').
by apply : H11.
by apply : H12.
rewrite product_unfold. 
assumption. 
assumption.
by rewrite H8 H10.
Qed.

Theorem product_divisibility : forall x xs, In x xs -> (x | product xs).
  intros.
  induction xs.
  intuition.
  destruct H.
  subst.
  destruct xs.
  exists 1.
  auto with arith.
  simpl.
  rewrite Nat.mul_comm.
  rewrite fold_distr.
  exists (fold_left Nat.mul xs n).
  auto with arith.
  destruct (IHxs H).
  destruct xs.
  intuition.
  simpl in *.
  rewrite Nat.mul_comm.
  rewrite fold_distr.
  rewrite H0.
  exists (a * x0).
  auto with arith.
Qed.

Theorem prime_self_divisibility : forall x y, prime (S (S x)) -> prime (S (S y)) ->
  divisible (S (S x)) (S (S y)) -> S (S x) = S (S y).
  intros.
  destruct (constructive_prime_number H H1).
  inversion H2.
  by symmetry.
Qed.

Fixpoint list_to_vector A (x: list A) : VectorDef.t A (length x) :=
  match x as c return VectorDef.t A (length c) with
     |x :: xs => VectorDef.cons _ x _ (list_to_vector xs)
     |[] => VectorDef.nil _
  end.

Fixpoint remove A (xs : list A) (f : A -> A -> bool) (a : A) {struct xs}
   : list A.
  refine (match xs with
    |x :: xs =>  _
    |[] => []
  end).
 destruct (f a x).
 refine xs.
 refine (x :: remove _ xs f a).
Defined.

Fixpoint remove_all A (xs : list A) (f : A -> A -> bool) (a : A) {struct xs}
   : list A.
  refine (match xs with
    |x :: xs =>  _
    |[] => []
  end).
 destruct (f a x).
 refine (remove_all _ xs f a).
 refine (x :: remove_all _ xs f a).
Defined.

Fixpoint remove_by_nat A (xs : list A) (f : A -> A -> bool) (a : A) (q : nat) {struct q}
   : list A := match q with
                |0 => xs
                |S n => (remove_by_nat (remove xs f a) f a n)
              end.

Fixpoint remove_many A (xs : list A) (ys : list A) (f : A -> A -> bool) {struct ys} : list A.
refine (match ys with
         |y :: ys' => _
         |[] => _
       end).
exact xs.
refine (remove (remove_many _ xs ys' f) f y).
Defined.

Definition remove_nat (xs : list nat) n := remove xs Nat.eqb n.
Definition remove_all_nat (xs : list nat) n := remove_all xs Nat.eqb n.
Definition remove_nat_by_nat (xs : list nat) n q := remove_by_nat xs Nat.eqb n q.
Definition remove_many_nat (xs : list nat) ys := remove_many xs ys Nat.eqb.

Fixpoint insert A (xs : list A) y (x : y < length xs) (h : A) {struct y} : list A.
destruct y.
exact (h :: xs).
destruct xs.
assert(~ S y < @length A []).
move => H.
inversion H.
intuition.
refine (a :: (insert _ xs y (le_S_n _ _ x) h)).
Defined.

Fixpoint insert_vector A n (xs : VectorDef.t A n) y (x : y < n) (h : A) {struct y} : VectorDef.t A (S n).
destruct y.
exact (VectorDef.cons _ h _ xs).
destruct xs.
assert(~ S y < 0).
move => H.
inversion H.
intuition.
refine (VectorDef.cons _ h0 _ (insert_vector _ _  xs y (le_S_n _ _ x) h)).
Defined.

Theorem remove_fold_mul : forall xs a, a > 0 ->
  product xs = fold_left Nat.mul xs a / a.
  intros.
  generalize dependent a.
  induction xs.
  simpl.
  intros;rewrite Nat.div_same.
  by inversion H.
  apply : eq_refl.
  simpl.
  intros.
  rewrite Nat.mul_comm.
  rewrite fold_distr.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul.
  by inversion H.
  trivial.
Qed.

Theorem prod_left : forall xs a, a * product xs = fold_left Nat.mul xs a.
  elim.
  intros.
  simpl; auto with arith.
  intros.
  pose (H a0).
  simpl.
  destruct l.
  by simpl.
  simpl in *.
  replace (a * n) with (n * a).
  rewrite fold_distr.
  replace (a0 * (a * fold_left Nat.mul l n)) with (a * (a0 * fold_left Nat.mul l n)).
  rewrite e.
  symmetry.
  replace (a0 * a * n) with (a0 * n * a).
  by rewrite fold_distr.
  lia.
  lia.
  lia.
Qed.

Theorem not_nullable_product : forall ys,
  (forall z : nat, In z ys -> z > 0) -> product ys <> 0.
  intros.
  induction ys.
  by simpl.
  assert(a > 0).
  apply : H.
  by left.
  simpl.
  destruct ys.
  simpl; lia.
  simpl.
  assert(product (n :: ys) <> 0). 
  apply : IHys.
  move => z H'.
  apply : H.
  by right.
  simpl in H1.
  rewrite Nat.mul_comm fold_distr.
  destruct a.
  inversion H0.
  destruct (fold_left Nat.mul ys n).
  congruence.
  simpl.
  lia.
Qed.

Theorem preserv_remove : 
  forall xs a, In a xs -> product xs = product (remove xs Nat.eqb a) * a.
  elim.
  intros.
  intuition.
  intros.
  destruct H0.
  rewrite H0.
  simpl.
  rewrite refl_nat_dec.
  rewrite <- prod_left.
  auto with arith.
  pose (H _ H0).
  simpl.
  remember (a0 =? a).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)).
  rewrite <- prod_left.
  auto with arith.
  simpl.
  rewrite <- prod_left.
  rewrite e.
  rewrite <- prod_left.
  auto with arith.
Qed.

Theorem remove_uniquess : forall xs a, In a xs -> a > 0 ->
   product(remove_nat xs a) = product xs / a.
  intros.
  induction xs.
  inversion H.
  destruct H.
  subst.
  unfold remove_nat.
  simpl.
  rewrite refl_nat_dec.
  by apply : remove_fold_mul.
  unfold remove_nat.
  simpl.
  remember (a =? a0).
  destruct b.
  rewrite <- (eq_rel (eq_sym Heqb)).
  by apply : remove_fold_mul.
  simpl.
  pose (IHxs H).
  unfold remove_nat in e.
  rewrite <- prod_left.
  rewrite e.
  rewrite <- prod_left.
  rewrite Nat.divide_div_mul_exact.
  by inversion H0.
  exists (product xs / a).
  rewrite <- e.
  by apply : preserv_remove.
  trivial.
Qed.

Fixpoint ele A (x : list A) (H : A) (f : A -> A -> bool) {struct x}: nat.
destruct x.
exact 0.
destruct (f a H).
exact (S (ele _ x H f)).
exact (ele _ x H f).
Defined.

Definition ele_nat := fun x h => ele x h Nat.eqb.


Theorem ele_nat_In : forall xs a, ele_nat xs a > 0 -> In a xs.
  unfold ele_nat.
  elim.
  intros.
  inversion H.
  intros.
  simpl in *.
  remember (a =? a0).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)).
  by left.
  by right; apply : H.
Qed.

Theorem In_ele_nat: forall xs a, In a xs -> ele_nat xs a > 0.
  unfold ele_nat.
  elim.
  intros.
  inversion H.
  intros.
  destruct H0.
  simpl.
  rewrite H0.
  rewrite refl_nat_dec.
  auto with arith.
  simpl.
  destruct (a =? a0).
  auto with arith.
  by apply : H.
Qed.

Theorem ele_remove_duplication : forall xs a, 1 < ele_nat xs a -> 
  In a (remove_nat xs a).
  unfold remove_nat; unfold ele_nat.
  elim.
  intros.
  inversion H.
  intros.
  simpl in *.
  remember(a =? a0).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)).
  rewrite refl_nat_dec.
  apply : ele_nat_In.
  auto with arith.
  remember(a0 =? a).
  destruct b.
  pose(eq_rel_false (eq_sym Heqb)).
  pose (eq_rel (eq_sym Heqb0)).
  intuition.
  right.
  exact (H a0 H0).
Qed.

Theorem ele_remove : forall xs a, 
   ele_nat (remove_nat xs a) a = pred (ele_nat xs a).
  unfold ele_nat; unfold remove_nat.
  elim.
  intuition.
  intros.
  simpl in *.
  remember (a0 =? a).
  destruct b.
  apply symmetry in Heqb.
  rewrite (eq_rel (symm_nat_dec Heqb)).
  rewrite refl_nat_dec.
  by simpl.
  simpl.
  rewrite (symm_nat_dec (eq_sym Heqb)).
  by apply : H.
Qed.

Theorem remove_diff_preservers_ele :
  forall xs a a0, a <> a0 -> ele_nat (remove xs Nat.eqb a) a0 = ele_nat xs a0.
  unfold ele_nat.
  elim. 
  intros.
  trivial.
  intros.
  simpl.
  remember (a0 =? a).
  remember (a =? a1).
  destruct b.
  destruct b0.
  assert(a0 = a1).
  by rewrite (eq_rel (eq_sym Heqb)) (eq_rel (eq_sym Heqb0)).
  intuition.
  trivial.
  destruct b0.
  simpl.
  rewrite (eq_rel (eq_sym Heqb0)).
  rewrite refl_nat_dec.
  pose (H _ _ H0).
  lia.
  simpl.
  rewrite <- Heqb0.
  by apply : H.
Qed.

Theorem ele_remove_pred : forall ys xs a,
  ele_nat (remove_many_nat xs ys) a = ele_nat xs a - ele_nat ys a.
  unfold remove_many_nat; unfold ele_nat.
  elim.
  intros.
  simpl.
  auto with arith.
  intros.
  simpl in *.
  pose(H xs a0).
  remember (a =? a0).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)). 
  pose ele_remove.
  unfold ele_nat in e0.
  unfold remove_nat in e0.
  rewrite e0.
  rewrite e.
  lia.
  pose (remove_diff_preservers_ele).
  unfold ele_nat in e0.
  rewrite e0.
  by apply : eq_rel_false.
  apply : H.
Qed.
  
Theorem ele_remove_preserv : forall ys xs a, ele_nat ys a < ele_nat xs a ->
  In a (remove_many_nat xs ys).
  unfold ele_nat.
  unfold remove_many_nat.
  elim.
  intros.
  destruct xs.
  inversion H.
  simpl in H.
  remember (n =? a).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)).
  by left.
  simpl.
  by right; apply : ele_nat_In.
  intros.
  simpl in H0.
  remember (a =? a0).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)).
  simpl.
  apply : ele_remove_duplication.
  rewrite ele_remove_pred.
  unfold ele_nat.
  lia.
  simpl.
  apply : ele_nat_In.
  rewrite remove_diff_preservers_ele.
  by apply : eq_rel_false.
  pose(H _ _ H0).
  by apply : In_ele_nat.
Qed.

Theorem remove_many_fold_mul : forall xs ys (H : forall z, In z ys -> ele_nat ys z <= ele_nat xs z /\ z > 0),
     product (remove_many_nat xs ys) = product xs / product ys.
  intros.
  unfold ele_nat in H.
  unfold remove_many_nat.
  generalize dependent xs.
  induction ys.
  intros.
  by rewrite Nat.div_1_r.
  intros.
  simpl.
  assert(product (remove_many xs ys Nat.eqb) = product xs / product ys).
  apply : IHys.
  move => z H'.
  destruct (H z).
  by right.
  simpl in H0.
  destruct (a =? z).
  constructor.
  auto with arith.
  assumption.
  by constructor.
  pose (H a).
  rewrite remove_uniquess.
  apply : ele_remove_preserv.
  destruct a0.
  by left.
  simpl in H1.
  by rewrite refl_nat_dec in H1.
  destruct a0.
  by left.
  done. 
  rewrite H0.
  rewrite <- prod_left.
  rewrite Nat.div_div.
  assert(forall z, In z ys -> z > 0).
  intros.
  destruct (H z).
  by right.
  assumption.
  by apply : not_nullable_product.
  destruct a0.
  by left.
  lia.
  by rewrite Nat.mul_comm.
Qed.

Theorem comm_insert : forall i xs x (H : i < length xs),
    product (x :: xs) = product (insert H x).
elim.
intros.
destruct xs.
inversion H.
trivial.
intros.
destruct xs.
inversion H0.
pose (H _ x (le_S_n _ _ H0)).
simpl in *.
rewrite fold_distr.
rewrite e.
generalize ( (le_S_n (S n)
        ((fix length (l : list nat) : nat :=
            match l with
            | [] => 0
            | _ :: l' => S (length l')
            end) xs))).
move => H2.
unfold product.
destruct(insert (H2 H0) x).
simpl.
auto with arith.
simpl.
symmetry; rewrite Nat.mul_comm.
by rewrite fold_distr.
Qed.

Definition share_list {A} := fun (x : list A) y a => In a x <-> In a y.

Theorem remove_all_In : forall xs a, ~ In a (remove_all_nat xs a).
 elim.
 intuition.
 intros.
 move => H'.
 unfold remove_all_nat in H'.
 simpl in H'.
 remember (a0 =? a).
 destruct b.
 pose(H a0).
 unfold remove_all_nat in n.
 intuition.
 simpl in H'.
 destruct H'.
 rewrite H0 in Heqb.
 pose(refl_nat_dec a0).
 move : i.
 by destruct (a0 =? a0).
 pose (H a0).
 intuition.
Qed.

Theorem remov_comm : forall n xs a, 
  remove_by_nat (remove xs Nat.eqb a) Nat.eqb a n =
   remove (remove_by_nat xs Nat.eqb a n) Nat.eqb a.
 elim.
 intros.
 trivial.
 intros.
 simpl.
 by rewrite H.
Qed.

Theorem remove_by_nat_aux : forall xs a n, 
  ele_nat (remove_nat_by_nat xs a (S n)) a =
   ele_nat (remove_nat (remove_nat_by_nat xs a n) a) a.
  intros.
  unfold remove_nat_by_nat.
  unfold remove_nat.
  induction n.
  trivial.
  simpl in *.
  rewrite remov_comm.
  by rewrite remov_comm.
Qed.


Theorem remove_by_nat_arith : forall xs a q,
    ele_nat (remove_nat_by_nat xs a q) a = ele_nat xs a - q.
  intros.
  unfold remove_nat_by_nat.
  unfold ele_nat.
  pose (ele_remove).
  unfold remove_nat in e.
  unfold ele_nat in e.
  induction q.
  simpl.
  lia.
  simpl.
  rewrite remov_comm.
  rewrite e.
  fold remove_by_nat.
  lia.
Qed.

Theorem remove_by_nat_In_le : forall xs ys a, ele_nat ys a < ele_nat xs a ->
   In a (remove_nat_by_nat xs a (ele_nat ys a)).
  intros.
  apply : ele_nat_In.
  rewrite remove_by_nat_arith.
  simpl.
  lia.
Qed.

Theorem remove_by_nat_In_le' : forall xs ys a, ele_nat ys a < ele_nat xs a ->
  ~ In a (remove_nat_by_nat ys a (ele_nat xs a)).
  intros.
  move => H'.
  pose (In_ele_nat H').
  move : g.
  rewrite remove_by_nat_arith.
  lia.
Qed.

Theorem product_remove_uniquess : forall xs ys a, a > 0 -> In a xs -> In a ys -> 
    product xs = product ys ->
   product(remove_nat xs a) = product (remove_nat ys a).
  intros.
  rewrite remove_uniquess .
  assumption.
  assumption.
  rewrite remove_uniquess.
  assumption.
  assumption.
  by rewrite H2.
Qed.

Definition In_Prop {A} (x : list A) (P : A -> Prop) := forall a, In a x -> P a.

Theorem product_remove_many_uniquess : forall xs ys ls, In_Prop ls (fun x => x > 0) ->
  (forall z, In z ls -> ele_nat ls z <= ele_nat xs z /\ ele_nat ls z <= ele_nat ys z) -> 
  product xs = product ys ->
        product(remove_many_nat xs ls) = product (remove_many_nat ys ls).
  intros.
  rewrite remove_many_fold_mul.
  move => z H'.
  destruct (H0 z).
  assumption.
  intuition.
  rewrite remove_many_fold_mul.
  move => z H'.
  destruct (H0 z).
  assumption.
  intuition.
  by rewrite H1.
Qed.

Theorem ele_exist_nth : forall xs ys z, (forall i z : nat, i < length xs ->
       exists j : nat, j < length ys /\ nth i xs z = nth j ys z) -> 
         In z ys -> ele_nat ys z <= ele_nat xs z.
  intros.
  assert( forall i z : nat,
    i < length xs -> In (nth i xs z) ys).
  intros.
  destruct(H i z0).
  assumption.
  destruct H2.
  pose (nth_In ys z0 H2).
  by rewrite H3.
  clear H.
Admitted.

Theorem divisible_product : forall xs z, z > 1 -> prime z -> primes xs -> (z | product xs) -> In z xs.
  intros.
  destruct z. lia.
  destruct z. lia.
  destruct (euclides_product H0 H1 (divisible_to_divide H2)).
  destruct a.
  unfold primes in H1.
  destruct H1.
  destruct (H5 _ H3).
  assert(x = S (S z)).
  destruct x. lia.
  destruct x. lia.
  apply : prime_self_divisibility.
  exact H7.
  exact H0.
  by apply : divisible_to_divide.
  by rewrite <- H8.
Qed.

Theorem unique_pair_product_of_primes : forall a xs ys, primes xs -> primes ys -> 
      product xs = product ys -> In a xs -> In a ys.
  intros.
  unfold primes in H.
  destruct H.
  destruct (H3 _ H2).
  apply : divisible_product.
  assumption.
  assumption.
  assumption.
  rewrite <- H1.
  by apply : product_divisibility.
Qed.

Theorem product_primes_remove_uniquess : forall xs ys a, a > 0 -> In a xs \/ In a ys -> 
   primes xs -> primes ys ->
      product xs = product ys ->
        product(remove_nat xs a) = product (remove_nat ys a).
  intros.
  apply : product_remove_uniquess.
  assumption.
  destruct H0.
  assumption.
  by apply : (@unique_pair_product_of_primes _ ys xs).
  destruct H0.
  by apply : (@unique_pair_product_of_primes _ xs ys).
  exact H0.
  exact H3.
Qed.

(*
Theorem product_remove_cons : forall z xs ys h a, ys <> [] -> xs <> [] ->
 product (remove_by_nat (S h :: ys) Nat.eqb a z) =
   product (remove_by_nat (S h :: xs) Nat.eqb a z) ->
      product (remove_by_nat ys Nat.eqb a z) =
   product (remove_by_nat xs Nat.eqb a z).
  unfold remove_by_nat.
  elim. 
  intros.
  simpl in H.
  destruct xs.
  intuition.
  destruct ys.
  intuition.
  simpl in H1.
  
  rewrite Nat.mul_comm in H1.
  rewrite fold_distr in H1.
  symmetry in H1.
  rewrite Nat.mul_comm in H1.
  rewrite fold_distr in H1.
  destruct h.
  simpl in H1.
  
  apply : (injective_mult).
*)

Theorem remove_nat_by_pred : forall xs a n,
  remove_by_nat (a :: xs) Nat.eqb a (S n) 
    = remove_by_nat xs Nat.eqb a n.
 unfold remove_nat_by_nat.
 unfold remove_nat.
 elim.
 intros.
 simpl.
 by rewrite refl_nat_dec.
 intros.
 destruct n.
 by simpl; rewrite refl_nat_dec.
 intros.
 pose (H a n).
 move : e.
 simpl in *.
 do 2! rewrite refl_nat_dec.
 intros.
 simpl.
 destruct (a0 =? a).
 trivial.
 trivial.
Qed.

Theorem cons_dif_remove :
  forall z a a0 l, a <> a0 -> 
  remove_by_nat (a :: l) Nat.eqb a0 z = a :: remove_by_nat l Nat.eqb a0 z.
 elim.
 intros.
 trivial.
 intros.
 simpl. 
 remember (a0 =? a).
 destruct b.
 pose (eq_rel (eq_sym Heqb)); intuition.
 by rewrite H.
Qed.

Theorem remove_by_nat_ele_is_remove_all : forall xs a,
  remove_nat_by_nat xs a (ele_nat xs a) = remove_all_nat xs a.
 unfold remove_nat_by_nat.
 unfold remove_all_nat.
 unfold ele_nat.
 elim.
 intros.
 trivial.
 intros.
 simpl.
 remember (a =? a0).
 destruct b.
 rewrite Nat.eqb_sym.
 rewrite <- Heqb.
 rewrite <- H.
 rewrite (eq_rel (eq_sym Heqb)).
 by rewrite remove_nat_by_pred.
 rewrite Nat.eqb_sym.
 rewrite <- Heqb.
 rewrite <- H.
 simpl.
 rewrite H.
 rewrite cons_dif_remove.
 by apply : eq_rel_false.
 by rewrite H.
Qed.

Theorem In_remove_all : forall xs a,
  ~ In a (remove_all xs Nat.eqb a).
  intros.
  induction xs.
  move => H'.
  inversion H'.
  move => H'.
  destruct IHxs.
  simpl in H'.
  remember (a =? a0).
  destruct b.
  trivial.
  destruct H'.
  rewrite H in Heqb.
  pose (refl_nat_dec a).
  rewrite i in Heqb.
  intuition.
  assumption.
Qed.

Theorem remove_identity : forall xs a,
  ~ In a xs -> remove xs Nat.eqb a = xs.
  elim.
  intros.
  trivial.
  intros.
  simpl.
  remember (a0 =? a).
  destruct b.
  destruct H0.
  by left; rewrite (eq_rel (eq_sym Heqb)).
  rewrite H.
  move => H'.
  intuition.
  by [].
Qed.

Theorem remove_by_nat_ele_is_remove_all_leb : forall xs a z, (ele_nat xs a) < z ->
  remove_nat_by_nat xs a z = remove_all_nat xs a.
  intros.  
  assert({n | z = n + ele_nat xs a}).
  exists (z - (ele_nat xs a)).
  lia.
  unfold remove_nat_by_nat; unfold ele_nat.
  destruct H0.
  rewrite e.
  clear e H.
  generalize dependent xs; generalize dependent a.
  induction x.
  intros.
  rewrite plus_O_n.
  by rewrite <- remove_by_nat_ele_is_remove_all.
  intros.
  simpl.
  rewrite <- remove_by_nat_ele_is_remove_all.
  pose (IHx a xs).
  rewrite remov_comm.
  rewrite e.
  rewrite remove_identity.
  apply : In_remove_all.
  by rewrite remove_by_nat_ele_is_remove_all.
Qed.
  
Theorem min_for_non_zero_product :
   forall l a, fold_left Nat.mul l (S a) > 0 -> (S a) <= fold_left Nat.mul l (S a).
  elim.
  intros.
  auto with arith.
  intros.
  simpl in H0.
  replace (a + a0 * a) with (S a0 * a) in H0 by lia.
  rewrite fold_distr in H0.
  simpl.
  replace (a + a0 * a) with (S a0 * a) by lia.
  rewrite fold_distr.
  assert(fold_left Nat.mul l (S a0) > 0).
  destruct (fold_left Nat.mul l (S a0)).
  lia.
  auto with arith.
  pose (H _ H1).
  destruct a.
  inversion H0.
  destruct a.
  lia.
  assert(fold_left Nat.mul l (S a0) <= S (S a) * fold_left Nat.mul l (S a0)).
  move : l0.
  destruct (fold_left Nat.mul l (S a0)).
  lia.
  intros.
  assert(forall x z, S x <= S x * S z).
  intros.
  elim/@nat_double_ind : x/z.
  intros; lia.
  intros; lia.
  intros; lia.
  by rewrite Nat.mul_comm.
  lia.
Qed.

Theorem fold_mult_refl_one : 
  forall l x y, S x * fold_left Nat.mul l (S y) = S y -> S x = 1.
  elim.
  intros.
  simpl in H.
  replace (S (y + x * S y)) with (S x * S y) in H by lia.
  destruct x.
  trivial.
  rewrite Nat.mul_comm in H.
  destruct (cicle_mul_absurd H).
  intros.
  simpl in H0.
  do 2! replace (a + y * a) with (S y * a) in H0 by lia.
  replace (fold_left Nat.mul l (S y * a) + x * fold_left Nat.mul l (S y * a))
       with (S x * fold_left Nat.mul l (S y * a)) in H0 by lia.
  replace (S y * a) with (a * S y) in H0 by lia.
  rewrite fold_distr in H0.
  destruct x.
  trivial.
  destruct (fold_left Nat.mul l a).
  lia.
  replace (S (S x) * (S y * S n)) with (S y * (S n * S (S x))) in H0 by lia.
  replace (S n * S (S x)) with (S (S (x + n * S (S x)))) in H0 by lia.
  destruct (cicle_mul_absurd H0).
Qed.

Theorem fold_mul_empty_list : 
  forall l a, fold_left Nat.mul l (S a) = (S a) -> fold_left Nat.mul l 1 = 1.
  elim.
  intros.
  trivial.
  intros.
  simpl in *.
  rewrite <- plus_n_O.
  replace (a + a0 * a) with (S a0 * a) in H0.
  rewrite fold_distr in H0.
  destruct a.
  simpl in H0.
  inversion H0.
  assert(S a = 1).
  remember (fold_left Nat.mul l (S a0)).
  destruct n.
  lia.
  destruct (div_less H0).
  rewrite Heqn in H2.
  rewrite Heqn in H0.
  destruct a.
  trivial.
  inversion H2.
  rewrite H4 in H0.
  rewrite Nat.mul_comm in H0.
  destruct (cicle_mul_absurd H0).
  assert(fold_left Nat.mul l (S a0) > 0) by lia.
  pose (min_for_non_zero_product H5).
  lia.
  rewrite H1; apply (H a0); lia.
  lia.
Qed.

Theorem product_distr_fold : 
  forall l a, product (a :: l) = a * product l.
  case.
  move => a /=; lia.
  by move => a l a0 /=; rewrite Nat.mul_comm fold_distr.
Qed.

Theorem product_div : 
  forall l a, a > 0 -> product (a :: l) / a = product l.
  case.
  move => a H /=.
  rewrite (Nat.div_same); lia; done.
  move => a l a0 H /=. rewrite Nat.mul_comm fold_distr Nat.mul_comm Nat.div_mul.
  lia.
  trivial.
Qed.

Theorem remove_neq_In : 
  forall l a, ~ In a l -> remove l Nat.eqb a = l.
  intros.
  generalize dependent a.
  induction l.
  intros.
  trivial.
  intros.
  simpl.
  remember (a0 =? a).
  destruct b.
  rewrite (eq_rel (eq_sym Heqb)) in H.
  destruct H.
  by left.
  rewrite IHl.
  move => H'.
  intuition.
  trivial.
Qed.

Theorem In_pred_remov : forall l a,
   In a (remove l Nat.eqb a) -> In a l.
  elim.
  intros.
  inversion H.
  intros.
  simpl in *.
  remember (a0 =? a).
  destruct b.
  by right.
  destruct H0.
  by left.
  by right; apply : H.
Qed.

Theorem In_pred_remov' : forall l a,
   In a (remove (a :: l) Nat.eqb a) -> In a l.
  intros.
  simpl in *.
  by rewrite refl_nat_dec in H.
Qed.

Theorem In_pred_remove_by_nat : forall z l a,
  In a (remove_by_nat l Nat.eqb a (S z)) -> In a (remove_by_nat l Nat.eqb a z).
 elim.
 intros.
 simpl in *.
 by apply : In_pred_remov.
 intros.
 simpl in *.
 apply : In_pred_remov.
 by rewrite <- remov_comm.
Qed.

Theorem In_pred_remove_by_nat' : forall z l a,
  In a (remove_by_nat (a :: l) Nat.eqb a (S z)) -> In a (remove_by_nat l Nat.eqb a z).
 elim.
 intros.
 simpl in *.
 by apply : In_pred_remov'.
 intros.
 apply : In_pred_remov'.
 simpl in *.
 rewrite refl_nat_dec.
 by rewrite refl_nat_dec in H0.
Qed.

Theorem fold_left_remove_identity : forall l a, In a l ->
  product (a :: remove l Nat.eqb a) = product l.
  elim.
  intros.
  inversion H.
  intros.
  simpl in *.
  remember (a0 =? a).
  destruct b.
  by rewrite (eq_rel (eq_sym Heqb)).
  destruct H0.
  destruct ((eq_rel_false (eq_sym Heqb)) (eq_sym H0)). 
  simpl.
  pose(H _ H0).
  rewrite fold_distr.
  destruct l.
  inversion H0.
  simpl in *.
  rewrite fold_distr.
  rewrite e.
  clear e H0 Heqb a0 H.
  move : l a n; elim.
  auto with arith.
  intros.
  simpl.
  rewrite fold_distr.
  replace (a0 * a) with (a * a0) by lia.
  rewrite fold_distr.
  rewrite H.
  lia.
Qed.


Theorem product_uniquess_remove_sort : forall z l a, In a (remove_by_nat (a :: l) Nat.eqb a z) -> (forall z, In z (a :: l) -> z > 0) -> 
  product (remove_by_nat (a :: l) Nat.eqb a z) = product (a :: remove_by_nat l Nat.eqb a z).
  elim.
  intros.
  trivial.
  intros.
  unfold remove_by_nat.
  fold remove_by_nat.
  rewrite remov_comm.
  rewrite remov_comm.
  rewrite remove_uniquess.
  by apply : In_pred_remove_by_nat.
  by apply : H1;left.
  rewrite (H l a).
  by apply : In_pred_remove_by_nat.
  assumption.
  rewrite fold_left_remove_identity.
  simpl in H0.
  by rewrite refl_nat_dec in H0.
  rewrite product_div.
  by apply : H1;left.
  done.
Qed.

Theorem succ_remove_by_nat_leb : forall xs z a, (ele_nat xs a) < z ->
   remove_nat_by_nat xs a (ele_nat xs a) = remove_nat_by_nat xs a z.
  unfold ele_nat; unfold remove_nat_by_nat.
  elim.
  intros.
  simpl in *.
  assert(forall z, remove_by_nat [] Nat.eqb a z = []).
  by elim.
  intuition.
  intros.
  simpl.
  remember (a =? a0).
  destruct b.
  simpl.
  rewrite Nat.eqb_sym.
  rewrite <- Heqb.
  pose (H z a0).
  destruct z.
  inversion H0.
  rewrite (eq_rel (eq_sym Heqb)).
  rewrite remove_nat_by_pred.
  simpl in H0.
  rewrite <- Heqb in H0.
  rewrite e.
  lia.
  clear H Heqb e.
  pose (remove_by_nat_ele_is_remove_all_leb).
  unfold remove_nat_by_nat in e.
  rewrite e.
  unfold ele_nat.
  lia.
  symmetry; apply : e.
  unfold ele_nat; lia.
  rewrite cons_dif_remove.
  by apply : eq_rel_false.
  pose (H z a0).
  rewrite e.
  simpl in H0.
  by rewrite <- Heqb in H0.
  rewrite cons_dif_remove.
  by apply : eq_rel_false.
  trivial.
Qed.

Theorem product_remove_by_nat_refl : forall xs ys a, ele_nat ys a < ele_nat xs a -> 
   primes xs -> primes ys ->
  product xs = product ys -> 
  product (remove_nat_by_nat ys a (ele_nat xs a)) =
    product (remove_nat_by_nat xs a (ele_nat ys a)).
  unfold ele_nat.
  unfold remove_nat_by_nat.
  elim.
  intros. 
  simpl in *.
  inversion H.
  intros.
  destruct ys.
  simpl in *.
  admit.
  simpl.
  remember (a =? a0).
  remember (n =? a0).
  destruct b. destruct b0.
  simpl.
  rewrite Nat.eqb_sym.
  rewrite <- Heqb0.
  rewrite Nat.eqb_sym.
  rewrite <- Heqb.
  simpl in H0.
  rewrite <- Heqb in H0.
  rewrite <- Heqb0 in H0.
  destruct l.
  destruct ys.
  trivial.
  simpl in H0.
  inversion H0.
  lia.
  destruct ys.
  simpl in *.
  rewrite fold_distr in H3.
  rewrite (eq_rel (eq_sym Heqb0)) in H3.
  rewrite (eq_rel (eq_sym Heqb)) in H3.
  destruct n0.
  destruct H1.
  destruct (H4 0).
  by right;left.
  inversion H5.
  assert(S n0 = 1).
  destruct a0.
  admit.
  apply : (fold_mult_refl_one H3).
  rewrite H4 in H3.
  simpl in H3.
  rewrite <- plus_n_O in H3.
  assert(  (remove_by_nat [] Nat.eqb a0
     (if S n0 =? a0 then S (ele l a0 Nat.eqb) else ele l a0 Nat.eqb)) = []).
  admit.
  rewrite H5; clear H5.
  rewrite H4.
  destruct a0.
  rewrite (eq_rel (eq_sym Heqb)) in H1.
  destruct H1.
  destruct (H5 0).
  by left.
  inversion H6.
  by rewrite (fold_mul_empty_list H3).
  simpl in H0.
  unfold primes in H1.
  apply : H.
  simpl; lia.
  constructor.
  congruence.
  move => k H'.
  destruct H1.
  destruct (H1 k).
  by right.
  by [].
  unfold primes in H2.
  constructor.
  congruence.
  destruct H2.
  move => k H'.
  destruct (H2 k).
  by right.
  by constructor.
  admit.
  rewrite (eq_rel (eq_sym Heqb)).
  rewrite cons_dif_remove.
  by apply : eq_rel_false.
  simpl in H0.
  rewrite (eq_sym Heqb) in H0.
  rewrite (eq_sym Heqb0) in H0.
  rewrite product_uniquess_remove_sort.
  apply : remove_by_nat_In_le.
  unfold ele_nat; simpl.
  by rewrite refl_nat_dec.
  move => z H'.
  destruct H1.
  destruct (H4 z).
  by rewrite (eq_rel (eq_sym Heqb)).
  auto with arith.
  pose (succ_remove_by_nat_leb).
  unfold remove_nat_by_nat in e.
  rewrite <- e.
  unfold ele_nat.
  rewrite product_distr_fold product_distr_fold.
  pose (remove_by_nat_ele_is_remove_all).
  unfold remove_nat_by_nat in e0.
  rewrite e0.
  pose (remove_by_nat_ele_is_remove_all_leb).
  unfold remove_nat_by_nat in e1.
  rewrite e1.
Admitted.

Theorem unique_pairs : forall a xs ys, primes xs -> primes ys -> 
      ele_nat xs a < ele_nat ys a -> False.
  intros.
  pose (remove_by_nat_In_le H1).
  pose (remove_by_nat_In_le' H1).
  destruct n.
  apply : (@unique_pair_product_of_primes a (remove_nat_by_nat ys a (ele_nat xs a)) (remove_nat_by_nat xs a (ele_nat ys a))).
  unfold primes.
  admit.
  admit.
Admitted.
  
 
Theorem arithmetic_uniquess : forall x xs ys, descending xs -> descending ys ->
    primes xs -> primes ys -> 
      x = product xs /\ x = product ys -> xs = ys.
  intros.
  destruct H3.
  assert(forall z, In z xs -> (z | product ys)).
  rewrite <- H4.
  move => z H'.
  destruct H1.
  destruct H2.
  set (H5 _ H').
  rewrite H3.
  by apply : product_divisibility.
  destruct H1.
  destruct H2.

  assert(forall i z, i < length xs -> exists j, j < length ys /\ nth i xs z = nth j ys z).
  intros.
  assert(exists j, j < length ys /\ (nth i xs z | nth j ys z)).
  destruct (H6 _ (nth_In xs z H8)).
  pose (divisible_to_divide (H5 _ (nth_In xs z H8))).
  move : H10 d.
  destruct (nth i xs z).
  inversion H9.
  destruct n.
  inversion H9.
  inversion H11.
  intros.
  destruct (euclides_product H10 (conj H2 H7) d).
  destruct a.
  destruct (In_nth ys _ z H11).
  exists x1.
  destruct H13.
  rewrite -> H14.
  intuition.
  destruct H9.
  exists x0.
  destruct H9.
  constructor.
  assumption.
  destruct ((H6 _ (nth_In xs z H8))).
  destruct ((H7 _ (nth_In ys z H9))).
  destruct (nth i xs z).
  inversion H11.
  destruct n. lia.
  destruct (nth x0 ys z).
  inversion H13.
  destruct n0. lia.
  symmetry; apply : prime_self_divisibility.
  assumption.
  assumption.
  by apply : divisible_to_divide.


  assert(forall z, In z ys -> (z | product xs)).
  rewrite <- H3.
  move => z H'.
  destruct (H7 z).
  exact H'.
  rewrite H4. 
  by apply : product_divisibility.
  
  assert(forall i z, i < length ys -> exists j, j < length xs /\ nth i ys z = nth j xs z).
  intros.
  assert(exists j, j < length xs /\ (nth i ys z | nth j xs z)).
  destruct (H7 _ (nth_In ys z H10)).
  pose (divisible_to_divide (H9 _ (nth_In ys z H10))).
  move : H10 d.
  destruct (nth i ys z).
  inversion H11.
  destruct n.
  lia.
  intros.
  destruct (euclides_product H12 (conj H1 H6) d).
  destruct a.
  destruct (In_nth xs _ z H13).
  exists x1.
  destruct H15.
  rewrite H16.
  by constructor.
  destruct H11.
  exists x0.
  destruct H11.
  constructor.
  assumption.
  destruct ((H7 _ (nth_In ys z H10))).
  destruct ((H6 _ (nth_In xs z H11))).
  destruct (nth x0 xs z).
  lia.
  destruct n. lia.
  destruct (nth i ys z).
  inversion H13.
  destruct n0. lia.
  symmetry; apply : prime_self_divisibility.
  assumption.
  assumption.
  by apply : divisible_to_divide.
  assert(~ exists n, ele_nat xs n <> ele_nat ys n).
  move => H'.
  destruct H'.
  assert(ele_nat xs x0 < ele_nat ys x0 \/ ele_nat xs x0 > ele_nat ys x0) by lia.
  destruct H12.
  assert(product(remove_many_nat xs ys) = product (remove_many_nat ys ys)).
  apply : product_remove_many_uniquess.
  admit.
  intros.
  constructor.
  admit.
  intuition.
  assert(forall z, In z xs -> ele_nat xs z <= ele_nat xs z
     /\ ele_nat xs z <= ele_nat ys z).
  intros.
  constructor.
  apply : le_n.
  pose(In_nth ).
Admitted.
