(* ========================================================================= *)
(*  Brute-force search: is the Schulze relation transitive over a given       *)
(*  finite algebra?                                                           *)
(*                                                                           *)
(*  [SelectivityNeeded.v] exhibits ONE non-selective algebra and ONE matrix   *)
(*  on which [schulze_beats] fails to be transitive.  That shows selectivity  *)
(*  cannot be dropped, but leaves open whether NON-selectivity is always      *)
(*  fatal.  Analysing the witness suggests the real obstruction is the        *)
(*  existence of zero divisors (a, b non-zero with a * b = 0) rather than     *)
(*  incomparability as such.                                                  *)
(*                                                                           *)
(*  This file settles the question for a candidate algebra by exhaustion.     *)
(*  Over three nodes a matrix is fixed by its six off-diagonal entries, so    *)
(*  for a carrier of size k there are k^6 matrices — 15625 for k = 5.  We     *)
(*  enumerate all of them and look for one that breaks transitivity.          *)
(*                                                                           *)
(*  Everything here is a computation, deliberately independent of the HB      *)
(*  hierarchy so that candidate algebras can be plugged in as plain data.     *)
(*  [check_semiring] verifies that the candidate really is a bounded          *)
(*  semiring before any conclusion is drawn from a search over it, and the    *)
(*  closure is computed with the same association order as [geom_sum] and     *)
(*  [matrix_mul] in MatN.v so that the results transfer.                      *)
(* ========================================================================= *)

From Stdlib Require Import List Bool Utf8.
Import ListNotations.

Section Search.

  Context {C : Type}
    (eqb : C -> C -> bool)
    (zero one : C)
    (add mul : C -> C -> C)
    (carrier : list C).

  (* ------------------------------------------------------------------ *)
  (*  Is the candidate actually a bounded semiring?                      *)
  (* ------------------------------------------------------------------ *)

  Definition all3 (p : C -> C -> C -> bool) : bool :=
    forallb (fun x => forallb (fun y => forallb (fun z => p x y z) carrier) carrier) carrier.

  Definition all2 (p : C -> C -> bool) : bool :=
    forallb (fun x => forallb (fun y => p x y) carrier) carrier.

  Definition all1 (p : C -> bool) : bool := forallb p carrier.

  Definition check_semiring : bool :=
    all3 (fun x y z => eqb (add (add x y) z) (add x (add y z)))    (* + assoc  *)
    && all2 (fun x y => eqb (add x y) (add y x))                   (* + comm   *)
    && all1 (fun x => eqb (add zero x) x)                          (* 0 id     *)
    && all1 (fun x => eqb (add x x) x)                             (* + idem   *)
    && all3 (fun x y z => eqb (mul (mul x y) z) (mul x (mul y z))) (* * assoc  *)
    && all1 (fun x => eqb (mul one x) x)                           (* 1 id l   *)
    && all1 (fun x => eqb (mul x one) x)                           (* 1 id r   *)
    && all1 (fun x => eqb (mul zero x) zero)                       (* 0 annih  *)
    && all1 (fun x => eqb (mul x zero) zero)
    && all3 (fun x y z => eqb (mul x (add y z)) (add (mul x y) (mul x z)))
    && all3 (fun x y z => eqb (mul (add x y) z) (add (mul x z) (mul y z)))
    && all1 (fun x => eqb (add one x) one).                        (* bounded  *)

  (* Reported, not required: selectivity, and freedom from zero divisors. *)
  Definition check_selective : bool :=
    all2 (fun x y => eqb (add x y) x || eqb (add x y) y).

  Definition check_no_zero_divisors : bool :=
    all2 (fun x y =>
      implb (negb (eqb x zero) && negb (eqb y zero)) (negb (eqb (mul x y) zero))).

  (* the natural order [x <= y := x + y = y] *)
  Definition leb (x y : C) : bool := eqb (add x y) y.

  (* the second hypothesis of schulze_trans_weaker:
     m <= a -> m <= b -> m <= a * b *)
  Definition check_meet_lower_bound : bool :=
    all3 (fun m a b => implb (leb m a && leb m b) (leb m (mul a b))).

  (* [Hmeet] in prudence / minmax_beats: multiplication IS the meet,
     x <= y -> x * y = x /\ y * x = x *)
  Definition check_meet : bool :=
    all2 (fun x y => implb (leb x y) (eqb (mul x y) x && eqb (mul y x) x)).

  (* ------------------------------------------------------------------ *)
  (*  Closure over three nodes, mirroring geom_sum / matrix_mul          *)
  (* ------------------------------------------------------------------ *)

  Definition nodes : list nat := [0; 1; 2]%nat.

  Definition idm (i j : nat) : C := if Nat.eqb i j then one else zero.

  (* sum over [0;1;2] folded right, exactly as [sum] in MatN.v *)
  Definition mmul (m1 m2 : nat -> nat -> C) (i j : nat) : C :=
    add (mul (m1 i 0) (m2 0 j))
        (add (mul (m1 i 1) (m2 1 j))
             (add (mul (m1 i 2) (m2 2 j)) zero)).

  (* geom_sum m 2 = (I + m·I) + m·(m·I) *)
  Definition star (m : nat -> nat -> C) (i j : nat) : C :=
    add (add (idm i j) (mmul m idm i j)) (mmul m (mmul m idm) i j).

  Definition mkM (xy xz yx yz zx zy : C) (i j : nat) : C :=
    match i, j with
    | 0, 0 => one | 1, 1 => one | 2, 2 => one
    | 0, 1 => xy  | 0, 2 => xz
    | 1, 0 => yx  | 1, 2 => yz
    | 2, 0 => zx  | 2, 1 => zy
    | _, _ => zero
    end%nat.

  (* Materialise the closure once per matrix. *)
  Definition star_tbl (m : nat -> nat -> C) : list (list C) :=
    map (fun i => map (fun j => star m i j) nodes) nodes.

  Definition get (t : list (list C)) (i j : nat) : C :=
    nth j (nth i t []) zero.

  (* [a] beats [b]: star b a <= star a b and they differ *)
  Definition beatsb (t : list (list C)) (a b : nat) : bool :=
    let sab := get t a b in
    let sba := get t b a in
    eqb (add sba sab) sab && negb (eqb sba sab).

  Definition trans_ok (m : nat -> nat -> C) : bool :=
    let t := star_tbl m in
    forallb (fun a => forallb (fun b => forallb (fun c =>
      implb (beatsb t a b && beatsb t b c) (beatsb t a c)) nodes) nodes) nodes.

  (* ------------------------------------------------------------------ *)
  (*  Enumerate every matrix and look for a failure                      *)
  (* ------------------------------------------------------------------ *)

  Definition tuples : list (C * C * C * C * C * C) :=
    flat_map (fun xy =>
    flat_map (fun xz =>
    flat_map (fun yx =>
    flat_map (fun yz =>
    flat_map (fun zx =>
    map      (fun zy => (xy, xz, yx, yz, zx, zy))
    carrier) carrier) carrier) carrier) carrier) carrier.

  Definition matrix_of (t : C * C * C * C * C * C) : nat -> nat -> C :=
    let '(xy, xz, yx, yz, zx, zy) := t in mkM xy xz yx yz zx zy.

  Definition search : option (C * C * C * C * C * C) :=
    find (fun t => negb (trans_ok (matrix_of t))) tuples.

  Definition num_matrices : nat := length tuples.

  (* ------------------------------------------------------------------ *)
  (*  The same instrument, aimed at prudence (Schulze §4.9)              *)
  (*                                                                     *)
  (*  [prudence] in SocialchoiceN.v assumes [Hmeet] — that multiplication *)
  (*  is the meet of the natural order.  Swapping the criterion here     *)
  (*  tests whether that hypothesis can be dropped.                       *)
  (* ------------------------------------------------------------------ *)

  Definition ltbC (x y : C) : bool := leb x y && negb (eqb x y).

  (** λ_D: the strength of the strongest non-trivial cycle, as in
      [cycle_strength] — the link a -> b composed with the best route back. *)
  Definition lambda (m : nat -> nat -> C) (t : list (list C)) : C :=
    fold_right add zero
      (flat_map (fun a =>
         map (fun b => if Nat.eqb a b then zero else mul (m a b) (get t b a))
             nodes) nodes).

  (** Prudence: a link strictly stronger than every cycle is respected. *)
  Definition prudence_ok (m : nat -> nat -> C) : bool :=
    let t := star_tbl m in
    let lam := lambda m t in
    forallb (fun a => forallb (fun b =>
      if Nat.eqb a b then true
      else implb (ltbC lam (m a b)) (beatsb t a b)) nodes) nodes.

  Definition search_prudence : option (C * C * C * C * C * C) :=
    find (fun t => negb (prudence_ok (matrix_of t))) tuples.

End Search.

(* ========================================================================= *)
(*  Candidate 1: max-min on a three-element chain 0 < a < 1 (SELECTIVE)      *)
(*  Sanity check in the positive direction — expect no failure.              *)
(* ========================================================================= *)

Module Chain3.

  Inductive T := C0 | Ca | C1.

  Definition eqb (x y : T) : bool :=
    match x, y with C0,C0 => true | Ca,Ca => true | C1,C1 => true | _,_ => false end.

  (* max *)
  Definition add (x y : T) : T :=
    match x, y with
    | C1, _ | _, C1 => C1
    | Ca, _ | _, Ca => Ca
    | _, _ => C0
    end.

  (* min *)
  Definition mul (x y : T) : T :=
    match x, y with
    | C0, _ | _, C0 => C0
    | Ca, _ | _, Ca => Ca
    | _, _ => C1
    end.

  Definition carrier : list T := [C0; Ca; C1].

End Chain3.

(* ========================================================================= *)
(*  Candidate 2: the 2x2 Boolean algebra (NOT selective, HAS zero divisors)  *)
(*  Sanity check in the negative direction — expect the known failure.       *)
(* ========================================================================= *)

Module Bool22.

  Inductive T := Bot | Ba | Bb | Top.

  Definition eqb (x y : T) : bool :=
    match x, y with
    | Bot,Bot => true | Ba,Ba => true | Bb,Bb => true | Top,Top => true
    | _,_ => false end.

  Definition add (x y : T) : T :=
    match x, y with
    | Bot, w => w | w, Bot => w
    | Top, _ => Top | _, Top => Top
    | Ba, Ba => Ba | Bb, Bb => Bb
    | Ba, Bb => Top | Bb, Ba => Top
    end.

  Definition mul (x y : T) : T :=
    match x, y with
    | Bot, _ => Bot | _, Bot => Bot
    | Top, w => w | w, Top => w
    | Ba, Ba => Ba | Bb, Bb => Bb
    | Ba, Bb => Bot | Bb, Ba => Bot
    end.

  Definition carrier : list T := [Bot; Ba; Bb; Top].

End Bool22.

(* ========================================================================= *)
(*  Candidate 3: 0 < c < {a, b} < 1 with a /\ b = c                          *)
(*  NOT selective, but NO zero divisors.  This is the open case.             *)
(* ========================================================================= *)

Module Lattice5.

  Inductive T := L0 | Lc | La | Lb | L1.

  Definition eqb (x y : T) : bool :=
    match x, y with
    | L0,L0 => true | Lc,Lc => true | La,La => true | Lb,Lb => true | L1,L1 => true
    | _,_ => false end.

  (* join *)
  Definition add (x y : T) : T :=
    match x, y with
    | L0, w => w | w, L0 => w
    | L1, _ => L1 | _, L1 => L1
    | Lc, w => w | w, Lc => w
    | La, La => La | Lb, Lb => Lb
    | La, Lb => L1 | Lb, La => L1
    end.

  (* meet *)
  Definition mul (x y : T) : T :=
    match x, y with
    | L0, _ => L0 | _, L0 => L0
    | L1, w => w | w, L1 => w
    | Lc, _ => Lc | _, Lc => Lc
    | La, La => La | Lb, Lb => Lb
    | La, Lb => Lc | Lb, La => Lc
    end.

  Definition carrier : list T := [L0; Lc; La; Lb; L1].

End Lattice5.

(* ========================================================================= *)
(*  A generic direct product, so candidates can be combined                  *)
(*                                                                           *)
(*  The product of two selective algebras is typically NOT selective — the   *)
(*  componentwise join of (a,0) and (0,a) is (a,a), neither operand — which  *)
(*  makes products the cheapest source of new non-selective test cases.      *)
(* ========================================================================= *)

Section Product.

  Context {C D : Type}
    (eqbC : C -> C -> bool) (zC oC : C) (addC mulC : C -> C -> C) (carC : list C)
    (eqbD : D -> D -> bool) (zD oD : D) (addD mulD : D -> D -> D) (carD : list D).

  Definition Peqb (x y : C * D) : bool :=
    eqbC (fst x) (fst y) && eqbD (snd x) (snd y).
  Definition Padd (x y : C * D) : C * D :=
    (addC (fst x) (fst y), addD (snd x) (snd y)).
  Definition Pmul (x y : C * D) : C * D :=
    (mulC (fst x) (fst y), mulD (snd x) (snd y)).
  Definition Pzero : C * D := (zC, zD).
  Definition Pone : C * D := (oC, oD).
  Definition Pcarrier : list (C * D) := list_prod carC carD.

End Product.

(* ========================================================================= *)
(*  Candidate 4: two-element max-min {0,1}                                   *)
(* ========================================================================= *)

Module Bool2.

  Inductive T := B0 | B1.
  Definition eqb (x y : T) : bool :=
    match x, y with B0,B0 => true | B1,B1 => true | _,_ => false end.
  Definition add (x y : T) : T :=
    match x, y with B1, _ | _, B1 => B1 | _, _ => B0 end.
  Definition mul (x y : T) : T :=
    match x, y with B0, _ | _, B0 => B0 | _, _ => B1 end.
  Definition carrier : list T := [B0; B1].

End Bool2.

(* ========================================================================= *)
(*  Candidate 5: truncated min-plus {0, 1, inf}                              *)
(*                                                                           *)
(*  Selective, but multiplication is truncated ADDITION, not the meet:       *)
(*  P1 * P1 = Pinf, whereas the meet of P1 with itself is P1.  Every         *)
(*  candidate above had * = meet, so this is the first test of whether the   *)
(*  picture depends on that.                                                  *)
(* ========================================================================= *)

Module MinPlus3.

  Inductive T := P0 | P1 | Pinf.

  Definition eqb (x y : T) : bool :=
    match x, y with P0,P0 => true | P1,P1 => true | Pinf,Pinf => true | _,_ => false end.

  (* semiring addition is numeric min; semiring zero is Pinf, one is P0 *)
  Definition add (x y : T) : T :=
    match x, y with
    | P0, _ | _, P0 => P0
    | P1, _ | _, P1 => P1
    | _, _ => Pinf
    end.

  (* semiring multiplication is numeric addition, truncated at Pinf *)
  Definition mul (x y : T) : T :=
    match x, y with
    | Pinf, _ | _, Pinf => Pinf
    | P0, w => w
    | w, P0 => w
    | P1, P1 => Pinf
    end.

  Definition carrier : list T := [P0; P1; Pinf].

End MinPlus3.

(* ========================================================================= *)
(*  Candidate 6: the non-distributive diamond M3 — NOT a semiring            *)
(*  Included to confirm [check_semiring] rejects invalid candidates.         *)
(* ========================================================================= *)

Module M3.

  Inductive T := D0 | Da | Db | Dc | D1.

  Definition eqb (x y : T) : bool :=
    match x, y with
    | D0,D0 => true | Da,Da => true | Db,Db => true | Dc,Dc => true | D1,D1 => true
    | _,_ => false end.

  Definition add (x y : T) : T :=   (* three incomparable atoms, all joins = D1 *)
    match x, y with
    | D0, w => w | w, D0 => w
    | D1, _ | _, D1 => D1
    | Da, Da => Da | Db, Db => Db | Dc, Dc => Dc
    | _, _ => D1
    end.

  Definition mul (x y : T) : T :=   (* all pairwise meets of atoms = D0 *)
    match x, y with
    | D0, _ | _, D0 => D0
    | D1, w => w | w, D1 => w
    | Da, Da => Da | Db, Db => Db | Dc, Dc => Dc
    | _, _ => D0
    end.

  Definition carrier : list T := [D0; Da; Db; Dc; D1].

End M3.

(* ========================================================================= *)
(*  RESULTS                                                                  *)
(*                                                                           *)
(*  M3 is rejected by [check_semiring] (it is not distributive).  The other   *)
(*  four candidates are confirmed bounded semirings, and give this table —    *)
(*  SEL is selectivity, MLB the meet-lower-bound property, the two            *)
(*  hypotheses of [schulze_trans_weaker] in SocialchoiceN.v:                  *)
(*                                                                           *)
(*    algebra     SEL   MLB   no zero div   matrices   transitivity           *)
(*    ---------   ---   ---   -----------   --------   ------------           *)
(*    Chain3      yes   yes       yes            729   holds throughout       *)
(*    MinPlus3    yes   NO        no             729   FAILS                  *)
(*    Bool22      NO    yes       no            4096   FAILS                  *)
(*    Lattice5    NO    yes       yes          15625   FAILS                  *)
(*                                                                           *)
(*  So the hypothesis set of [schulze_trans_weaker] is TIGHT: each of its     *)
(*  two hypotheses can be dropped only at the cost of the theorem, and the    *)
(*  witnesses are natural algebras, not contrivances — MinPlus3 is truncated  *)
(*  min-plus, the standard shortest-path algebra with a finite cap.           *)
(*                                                                           *)
(*  Two distinct failure mechanisms show up, and the two hypotheses block     *)
(*  one each.                                                                 *)
(*                                                                           *)
(*  (1) ZERO DIVISORS (MinPlus3, Bool22).  The composite route collapses to   *)
(*      the bottom.  In MinPlus3, P1 * P1 = Pinf = 0 by truncation, so the    *)
(*      route X -> Z -> Y carries nothing while the direct edge Y -> X ties   *)
(*      it, and X fails to beat Y despite beating Z and Z beating Y.          *)
(*      Selectivity together with MLB forbids this: if a, b are non-zero,     *)
(*      selectivity orders them, say a <= b, so a is a lower bound of both    *)
(*      and MLB gives a <= a * b, whence a * b = 0 would force a = 0.         *)
(*                                                                           *)
(*  (2) INCOMPARABILITY (Lattice5).  The composite need not reach the bottom  *)
(*      — only the level of the reverse path.  With a, b incomparable,        *)
(*      a * b lies STRICTLY below both, and in Lattice5 the route             *)
(*      Y -> Z -> X carries a * b = c while the reverse X -> Z -> Y also      *)
(*      carries c, so the two closure entries tie and strictness fails.       *)
(*      Selectivity forbids this: a + b <> a and a + b <> b say precisely     *)
(*      that neither a <= b nor b <= a, so a selective algebra has no         *)
(*      incomparable pair at all.                                             *)
(*                                                                           *)
(*  Note that Lattice5 has no zero divisors and Bool22 is not selective, so   *)
(*  neither property alone accounts for the data; the conjunction does.       *)
(*                                                                           *)
(*  Open: is the conjunction also sufficient in the sense that EVERY algebra  *)
(*  failing SEL or MLB admits a bad matrix?  Four data points are consistent  *)
(*  with that but do not establish it.  Further candidates can be fed to the  *)
(*  same instrument, and [Product] below makes non-selective ones easy to     *)
(*  manufacture.                                                              *)
(* ========================================================================= *)

Section Results.

  (* M3 is not distributive, so not a semiring — the instrument says so. *)
  Compute (check_semiring M3.eqb M3.D0 M3.D1 M3.add M3.mul M3.carrier).
  (* = false *)

  (* (bounded semiring, selective, meet-lower-bound, no zero divisors) *)
  Definition profile {C} eqb zero one add mul carrier : bool * bool * bool * bool :=
    (@check_semiring C eqb zero one add mul carrier,
     @check_selective C eqb add carrier,
     @check_meet_lower_bound C eqb add mul carrier,
     @check_no_zero_divisors C eqb zero mul carrier).

  Compute profile Chain3.eqb Chain3.C0 Chain3.C1 Chain3.add Chain3.mul Chain3.carrier.
  (* = (true, true, true, true) *)
  Compute (num_matrices Chain3.carrier,
           search Chain3.eqb Chain3.C0 Chain3.C1 Chain3.add Chain3.mul Chain3.carrier).
  (* = (729, None) *)

  Compute profile Bool22.eqb Bool22.Bot Bool22.Top Bool22.add Bool22.mul Bool22.carrier.
  (* = (true, false, true, false) *)
  Compute (num_matrices Bool22.carrier,
           search Bool22.eqb Bool22.Bot Bool22.Top Bool22.add Bool22.mul Bool22.carrier).
  (* = (4096, Some (Bot, Bot, Bot, Ba, Bb, Bot)) — a relabelling of the
       hand-built witness in SelectivityNeeded.v *)

  Compute profile Lattice5.eqb Lattice5.L0 Lattice5.L1 Lattice5.add Lattice5.mul Lattice5.carrier.
  (* = (true, false, true, true) *)
  Compute (num_matrices Lattice5.carrier,
           search Lattice5.eqb Lattice5.L0 Lattice5.L1 Lattice5.add Lattice5.mul Lattice5.carrier).
  (* = (15625, Some (L0, Lc, L0, La, Lb, Lc)) *)

  Compute profile MinPlus3.eqb MinPlus3.Pinf MinPlus3.P0 MinPlus3.add MinPlus3.mul MinPlus3.carrier.
  (* = (true, true, false, false) *)
  Compute (num_matrices MinPlus3.carrier,
           search MinPlus3.eqb MinPlus3.Pinf MinPlus3.P0 MinPlus3.add MinPlus3.mul MinPlus3.carrier).
  (* = (729, Some (P1, P1, P1, Pinf, Pinf, P1)) *)

  (* --------------------------------------------------------------- *)
  (*  PRUDENCE (§4.9) — the same instrument, a different criterion    *)
  (*                                                                   *)
  (*  [prudence] assumes selectivity and [Hmeet] (multiplication is    *)
  (*  the meet).  The three searches below show each is necessary:     *)
  (*                                                                   *)
  (*    algebra     selective   Hmeet   prudence                        *)
  (*    ---------   ---------   -----   --------                        *)
  (*    Chain3         yes       yes    holds throughout                *)
  (*    MinPlus3       yes       NO     FAILS                           *)
  (*    Bool22         NO        yes    FAILS                           *)
  (*                                                                   *)
  (*  So prudence has the same 2x2 independence structure as           *)
  (*  transitivity: neither hypothesis is redundant given the other.   *)
  (* --------------------------------------------------------------- *)

  Compute (check_meet Chain3.eqb Chain3.add Chain3.mul Chain3.carrier,
           check_meet MinPlus3.eqb MinPlus3.add MinPlus3.mul MinPlus3.carrier,
           check_meet Bool22.eqb Bool22.add Bool22.mul Bool22.carrier).
  (* = (true, false, true) *)

  Compute search_prudence Chain3.eqb Chain3.C0 Chain3.C1
            Chain3.add Chain3.mul Chain3.carrier.
  (* = None — selective with * the meet: prudence holds everywhere *)

  Compute search_prudence MinPlus3.eqb MinPlus3.Pinf MinPlus3.P0
            MinPlus3.add MinPlus3.mul MinPlus3.carrier.
  (* = Some (P0, P0, Pinf, P1, Pinf, P1) — selective, but * is truncated
       addition rather than the meet, and prudence fails *)

  Compute search_prudence Bool22.eqb Bool22.Bot Bool22.Top
            Bool22.add Bool22.mul Bool22.carrier.
  (* = Some (Bot, Bot, Bot, Ba, Bot, Bb) — * is the meet, but the algebra
       is not selective, and prudence fails *)

End Results.
