From Coq Require Import Init.Prelude Unicode.Utf8.
From Coq Require Import ZArith.
From Coq Require Import ZArith.Znumtheory.
From Coq Require Import Lia.

Open Scope Z_scope.

Record M := mkM
  { data : Z
  ; height : positive
  ; width : positive
  ; spacing : positive
  }.

Definition Zheight (m : M) := Z.pos (height m).
Definition Zwidth (m : M) := Z.pos (width m).
Definition Zspacing (m : M) := Z.pos (spacing m).

Definition atm (m : M) (x : Z) (y : Z) := (data m) + (Zspacing m) * x + y.
Definition inm (m : M) (x : Z) (y : Z) := 0 <= y < (Zheight m) ∧ 0 <= x < (Zwidth m).

Definition overlap_definition (m1 : M) (m2 : M) :=
  exists x1 y1 x2 y2,
      inm m1 x1 y1
    ∧ inm m2 x2 y2
    ∧ atm m1 x1 y1 = atm m2 x2 y2.

Section Examples.
  Example m1 := mkM 0 10 10 20.

  Example example_in_m1 : inm m1 5 5.
  Proof.
    unfold m1, inm, Zheight, Zwidth, height, width.
    lia.
  Qed.

  Example m2 := mkM 10 1 10 21.

  Example example_m1_m2_no_overlap : ~(overlap_definition m1 m2).
  Proof.
    unfold overlap_definition.
    unfold m1, m2, inm, atm.
    unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
    intros [x1 [y1 [x2 [y2 [[] [[]] ]]]]].
    lia.
  Qed.

  Example m3 := mkM 24 4 4 20.

  Example example_m1_m3_overlap : overlap_definition m1 m3.
  Proof.
    unfold overlap_definition.
    unfold m1, m3, inm, atm.
    unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
    exists 1, 4, 0, 0.
    lia.
  Qed.
End Examples.

Definition overlap_definition_short (m0 m1 : M) :=
  let d := data m1 - data m0 in
    exists x0 x1,
      0 <= x0 < Zwidth m0 ∧
      0 <= x1 < Zwidth m1 ∧
      d - (Zheight m0) < x0 * (Zspacing m0) - x1 * (Zspacing m1) < d + (Zheight m1).

Lemma overlap_definition_short_correct : forall M0 M1, overlap_definition_short M0 M1 <-> overlap_definition M0 M1.
Proof.
  destruct M0, M1.
  unfold overlap_definition_short, overlap_definition.
  unfold inm, atm.
  unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
  split.
  - intros [x0 [x1 [x0_in_range [x1_in_range [LOW HIGH]]]]].
    remember (data0 + x0 * Z.pos spacing0 - (data1 + x1 * Z.pos spacing1)) as y.
    destruct y as [ | py | ny].
    * exists x0, 0, x1, 0. lia.
    * exists x0, 0, x1, (Z.pos py). lia.
    * exists x0, (Z.pos ny), x1, 0. lia.
  - intros [x0 [y0 [x1 [y1 [[] [[]] ]]]]].
    exists x0, x1. lia.
Qed.

Definition overlap_definition_paral (m0 : M) (m1 : M) :=
  let d := data m1 - data m0 in
    exists x0 x1,
      0 <= x0 < Zwidth m0 ∧
      atm m0 x0 (Zheight m0 - 1) >= atm m1 0 0 ∧
      atm m0 x0 0 <= atm m1 (Zwidth m1 - 1) (Zheight m1 - 1) ∧
      d - (Zheight m0) < x0 * (Zspacing m0) - x1 * (Zspacing m1) < d + (Zheight m1).

Lemma overlap_definition_paral_correct : forall M0 M1, overlap_definition_paral M0 M1 <-> overlap_definition_short M0 M1.
Proof.
  destruct M0, M1.
  unfold overlap_definition_paral, overlap_definition_short.
  unfold inm, atm.
  unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
  split.
  - intros [x0 [x1 [x0_in_range [H1 [H2 [LOW HIGH]]]]]].
    exists x0.
    assert (x1 < 0 \/ 0 <= x1 < Z.pos width1 \/ Z.pos width1 <= x1) as s by lia.
    destruct s as [Clip_low | [Normal | Clip_high]].
    + exists 0. lia.
    + exists x1. lia.
    + exists (Z.pos width1 - 1).
      pose proof (Zmult_le_compat_r (Z.pos width1 - 1) x1 (Z.pos spacing1)).
      lia.
  - intros [x0 [x1 [x0_in_range [x1_in_range [LOW HIGH]]]]].
    exists x0, x1.
    pose proof (Zmult_le_compat_r x1 (Z.pos width1 - 1) (Z.pos spacing1)).
    lia.
Qed.

(* count x0 a b c w = number of integer solutions (x y) to x0 <= x < x0 + w and 0 <= y and a*x + b*y <= c *)
Fixpoint count_rtrap_definition (x0 a b c : Z) (w : nat) :=
  match w with
  | O    => 0
  | S w' => (c - a * (x0 + Z.of_nat w')) / b + 1 + count_rtrap_definition x0 a b c w'
  end.

Lemma count_rtrap_irr : forall x0 a b c w, b > 0 -> count_rtrap_definition x0 a b c w = let d := Z.gcd a b in count_rtrap_definition x0 (a / d) (b / d) (c / d) w.
Proof.
  intros. simpl.
  induction w.
  - now reflexivity.
  - unfold count_rtrap_definition. fold count_rtrap_definition.
    rewrite <- IHw.
    destruct (Zgcd_is_gcd a b) as [[ar A] [br B] _].
    remember (Z.gcd a b) as d in *.
    set (x := x0 + Z.of_nat w).
    assert ((c - a * x) / b = (c / d - a / d * x) / (b / d)).
    + destruct d.
      * rewrite Zdiv_0_r.
        rewrite Zdiv_0_r.
        rewrite Zdiv_0_r.
        rewrite Zdiv_0_r.
        replace b with 0 by lia.
        rewrite Zdiv_0_r.
        reflexivity.
      * rewrite B. rewrite Z_div_mult by lia.
        replace (br * Z.pos p) with (Z.pos p * br) by lia.
        rewrite <- (Zdiv_Zdiv) by lia.
        rewrite A. rewrite Z_div_mult by lia.
        replace (c - ar * Z.pos p * x) with (c + (- ar * x) * Z.pos p) by lia.
        rewrite (Z_div_plus c _ (Z.pos p)) by lia.
        replace (c / Z.pos p + - ar * x) with (c / Z.pos p - ar * x) by lia.
        lia.
      * pose proof (Z.gcd_nonneg a b) as GP.
        rewrite <- Heqd in GP.
        contradiction.
    + lia.
Qed.

(* count_triangle a b w =
   for positive w: number of integer solutions (x y) to 0 <= x < w and 0 <= y and b * y <= a * x
   for negative w: number of integer solutions (x y) to w <= x < 0 and y < 0 and a * x < b * y
   for w equal 0 the answer is zero (both predicates above would give zero)
 *)

Fixpoint count_triangle_definition_pos (a b : Z) (w : nat) :=
  match w with
  | O    => 0
  | S w' => a * (Z.of_nat w') / b + 1 + count_triangle_definition_pos a b w'
  end.

Fixpoint count_triangle_definition_neg (a b : Z) (w : nat) :=
  match w with
  | O    => 0
  | S w' => (a * (Z.of_nat w) - 1) / b + count_triangle_definition_neg a b w'
  end.

Definition count_triangle_definition (a b w : Z) :=
  match w with
  | 0 => 0
  | Z.pos p => count_triangle_definition_pos a b (Pos.to_nat p)
  | Z.neg p => count_triangle_definition_neg a b (Pos.to_nat p)
  end.

Lemma Z_div_opp : forall a b:Z, b > 0 -> (-a)/b = -((a-1)/b)-1.
Proof.
  intros.
  assert (b <> 0) as Bnz by lia.
  pose proof (Zdiv_eucl_exist H (a - 1)) as [[q r] [M R]].
  rewrite M.
  replace (-a) with (-1 - (a - 1)) by lia.
  rewrite M.
  replace (-1 - (b * q + r)) with ((- 1 - q) * b + (b - r - 1)) by lia.
  rewrite (Z_div_plus_full_l (- 1 -q) b (b - r - 1) Bnz).
  replace (b * q) with (q * b) by lia.
  rewrite (Z_div_plus_full_l q b r Bnz).
  rewrite (Zdiv_small r b) by (apply R).
  rewrite (Zdiv_small) by lia.
  lia.
Qed.


Lemma count_triangle_plus_one : forall a b w, b > 0 -> count_triangle_definition a b (w + 1) = count_triangle_definition a b w + a * w / b + 1.
Proof.
  intros.
  unfold count_triangle_definition.
  destruct w.
  - replace (0 + 1) with 1 by lia.
    replace (Pos.to_nat 1) with 1%nat by lia.
    unfold count_triangle_definition_pos.
    lia.
  - replace (Z.pos p + 1) with (Z.pos (p + 1)) by lia.
    replace (Pos.to_nat (p + 1)) with (S (Pos.to_nat p)) by lia.
    unfold count_triangle_definition_pos.
    lia.
  - remember (Z.neg p + 1) as q.
    destruct q.
    + replace p with 1%positive by lia.
      replace (Pos.to_nat 1) with 1%nat by lia.
      unfold count_triangle_definition_neg.
      replace (Z.of_nat 1) with 1 by lia.
      replace (a * -1) with (-a) by lia.
      rewrite Z_div_opp by apply H.
      replace (a * 1) with a by lia.
      lia.
    + lia.
    + replace (Pos.to_nat p) with (S (Pos.to_nat p0)) by lia.
      replace (Z.neg p) with (Z.neg p0 - 1) by lia.
      unfold count_triangle_definition_neg.
      ring_simplify.
      replace (a * (Z.neg p0 - 1)) with (- (a * (Z.pos p0 + 1))) by lia.
      rewrite Z_div_opp by apply H.
      lia.
Qed.

Definition count_rtrap_implementation (x0 a b c w : Z) : Z :=
  let (p, d) := extgcd a b in
  let (x1, y1) := p in
  let mar := (-a) / d in
  let br := b / d in
  let cr := c / d in
  let xc := cr * x1 in
  let yc := cr * y1 in
    count_triangle_definition mar br (x0 + w - xc) - count_triangle_definition mar br (x0 - xc) + yc * w.

Lemma Zgcd_pos: forall a b, b > 0 -> Z.gcd a b > 0.
Proof.
  intros.
  destruct b.
  - lia.
  - unfold Z.gcd.
    destruct a.
    + lia.
    + lia.
    + lia.
  - lia.
Qed.

Lemma count_rtrap_correct : forall x0 a b c w, b > 0 -> count_rtrap_implementation x0 a b c (Z.of_nat w) = count_rtrap_definition x0 a b c w.
Proof.
  intros.
  induction w.
  - unfold count_rtrap_definition.
    unfold count_rtrap_implementation.
    unfold Z.of_nat.
    destruct (extgcd a b) as [[x1 y1] d].
    replace (x0 + 0) with x0 by lia.
    lia.
  - unfold count_rtrap_definition. fold count_rtrap_definition. destruct IHw.
    replace (Z.of_nat (S w)) with (Z.of_nat w + 1) by lia.
    remember (Z.of_nat w) as Zw.
    unfold count_rtrap_implementation.
    remember (extgcd a b) as eg. symmetry in Heqeg.
    destruct eg as [[x1 y1] d].
    pose proof (extgcd_correct a b Heqeg) as [Bez D].
    set (k1 := (count_triangle_definition (- a / d) (b / d) (x0 - c / d * x1))).
    replace (x0 + (Zw + 1) - c / d * x1) with ((x0 + Zw - c / d * x1) + 1) by lia.
    rewrite count_triangle_plus_one.
    * set (k2 := count_triangle_definition (- a / d) (b / d) (x0 + Zw - c / d * x1)).
      destruct (Zgcd_is_gcd a b) as [[ar A] [br B] _].
      rewrite <- D in *.
      rewrite A. rewrite B.
      destruct d.
      + lia.
      + rewrite Z_div_mult by lia.
        replace (- (ar * Z.pos p)) with (- ar * Z.pos p) by lia.
        rewrite Z_div_mult by lia.
        assert (- ar * (x0 + Zw - c / Z.pos p * x1) / br + c / Z.pos p * y1 = (c - ar * Z.pos p * (x0 + Zw)) / (br * Z.pos p)).
        2: lia.
        replace (br * Z.pos p) with (Z.pos p * br) by lia.
        rewrite <- Zdiv_Zdiv by lia.
        replace (c - ar * Z.pos p * (x0 + Zw)) with (c + (- ar * (x0 + Zw) * Z.pos p)) by lia.
        rewrite Z_div_plus by lia.
        rewrite <- (Z_div_plus) by lia.
        replace (c / Z.pos p * y1 * br) with (c / Z.pos p * (y1 * br)) by lia.
        replace (y1 * br) with (1 - x1 * ar).
        replace (- ar * (x0 + Zw - c / Z.pos p * x1) + c / Z.pos p * (1 - x1 * ar)) with (c / Z.pos p + - ar * (x0 + Zw)) by lia.
        lia.
        replace 1 with (Z.pos p / Z.pos p).
        2: {apply Z_div_same_full. lia. }
        rewrite <- Bez at 1. rewrite A. rewrite B.
        rewrite Z.mul_assoc. rewrite Z.mul_assoc.
        rewrite (Z_div_plus) by lia.
        rewrite Z_div_mult by lia.
        lia.
      + pose proof (Z.gcd_nonneg a b) as GP.
        rewrite <- D in GP.
        contradiction.
    * pose proof (Zgcd_pos a b H) as GP.
      destruct (Zgcd_is_gcd a b) as [_ [br B] _].
      rewrite <- D in *. rewrite B.
      rewrite Z_div_mult by lia.
      lia.
Qed.




From Coq Require Import Extraction.

Extraction Language OCaml.

Extraction M. Extraction atm. Extraction inm. Extraction count_rtrap_implementation.

