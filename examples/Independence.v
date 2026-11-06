(** * The carrier [nat ∪ {-∞}] with [max] and [+]

    This carrier is selective and has the meet property but is not bounded.
    With the tropical semiring (selective, no meet) and the diamond (meet, not
    selective), both in SharpnessWitness.v, it shows that boundedness,
    selectivity, and the meet property are independent.  It also shows that
    meet_iff_mul_idempotent really needs boundedness: here the meet property
    holds and [x * x = x] fails. *)

From Stdlib Require Import Utf8 Arith Lia.
From HB Require Import structures.
From Semiring Require Import Structures OrelN.

Definition MP : Type := option nat.   (* None is -∞ *)

Definition mp_add (u v : MP) : MP :=
  match u, v with
  | None, w | w, None => w
  | Some x, Some y => Some (Nat.max x y)
  end.

Definition mp_mul (u v : MP) : MP :=
  match u, v with
  | Some x, Some y => Some (Nat.add x y)
  | _, _ => None
  end.

Local Ltac mp_solve :=
  repeat (match goal with x : MP |- _ => destruct x end);
  cbn; try reflexivity; f_equal; lia.

Lemma mp_addA : forall x y z : MP, mp_add (mp_add x y) z = mp_add x (mp_add y z).
Proof. intros; mp_solve. Qed.
Lemma mp_addC : forall x y : MP, mp_add x y = mp_add y x.
Proof. intros; mp_solve. Qed.
Lemma mp_add0r : forall x : MP, mp_add None x = x.
Proof. intros; mp_solve. Qed.
Lemma mp_addr0 : forall x : MP, mp_add x None = x.
Proof. intros; mp_solve. Qed.

HB.instance Definition _ := IsCommutativeMonoid.Build MP
  None mp_add mp_addA mp_addC mp_add0r mp_addr0.

Lemma mp_mulA : forall x y z : MP, mp_mul (mp_mul x y) z = mp_mul x (mp_mul y z).
Proof. intros; mp_solve. Qed.
Lemma mp_mul1r : forall x : MP, mp_mul (Some 0) x = x.
Proof. intros; mp_solve. Qed.
Lemma mp_mulr1 : forall x : MP, mp_mul x (Some 0) = x.
Proof. intros; mp_solve. Qed.
Lemma mp_mulDr : forall x y z : MP,
  mp_mul (mp_add x y) z = mp_add (mp_mul x z) (mp_mul y z).
Proof. intros; mp_solve. Qed.
Lemma mp_mulDl : forall x y z : MP,
  mp_mul x (mp_add y z) = mp_add (mp_mul x y) (mp_mul x z).
Proof. intros; mp_solve. Qed.
Lemma mp_mul0r : forall x : MP, mp_mul None x = None.
Proof. intros; mp_solve. Qed.
Lemma mp_mulr0 : forall x : MP, mp_mul x None = None.
Proof. intros; mp_solve. Qed.

HB.instance Definition _ := IsSemiring.Build MP
  (Some 0) mp_mul mp_mulA mp_mul1r mp_mulr1 mp_mulDr mp_mulDl mp_mul0r mp_mulr0.

Import SemiringNotations.
Local Infix "≤" := Orel (at level 70).

Theorem mp_selective : forall x y : MP, x + y = x \/ x + y = y.
Proof.
  intros [x|] [y|]; cbn; auto.
  destruct (Nat.max_dec x y) as [E|E]; rewrite E; auto.
Qed.

Theorem mp_meet : forall m a b : MP, m ≤ a -> m ≤ b -> m ≤ a * b.
Proof.
  unfold Orel. intros [m|] [a|] [b|] Ha Hb; cbn in *; try reflexivity;
    try discriminate.
  injection Ha as Ha. f_equal. lia.
Qed.

Theorem mp_not_bounded : ~ (forall a : MP, 1 + a = 1).
Proof. intro H. specialize (H (Some (S O))). cbn in H. discriminate. Qed.

Theorem mp_not_mul_idempotent : ~ (forall x : MP, x * x = x).
Proof. intro H. specialize (H (Some (S O))). cbn in H. discriminate. Qed.
