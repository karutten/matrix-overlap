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

Fact overlap_definition_symm :
  forall m1 m2, overlap_definition m1 m2 <-> overlap_definition m2 m1.
Proof.
  assert (forall m1 m2, overlap_definition m1 m2 -> overlap_definition m2 m1).
  { intros m1 m2 [x1 [y1 [x2 [y2]]]].
    exists x2, y2, x1, y1.
    intuition.
  }
  intuition.
Qed.

Section Examples.
  Example example_m1 := mkM 0 10 10 20.

  Example example_in_m1 : inm example_m1 5 5.
  Proof.
    unfold example_m1, inm, Zheight, Zwidth, height, width.
    lia.
  Qed.

  Example example_m2 := mkM 10 1 10 21.

  Example example_m1_m2_no_overlap : ~(overlap_definition example_m1 example_m2).
  Proof.
    unfold overlap_definition.
    unfold example_m1, example_m2, inm, atm.
    unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
    intros [x1 [y1 [x2 [y2 [[] [[]] ]]]]].
    lia.
  Qed.

  Example example_m3 := mkM 24 4 4 20.

  Example example_m1_m3_overlap : overlap_definition example_m1 example_m3.
  Proof.
    unfold overlap_definition.
    unfold example_m1, example_m3, inm, atm.
    unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
    exists 1, 4, 0, 0.
    lia.
  Qed.
End Examples.


Theorem Zstep_lt_l: forall a b, a < b <-> a + 1 <= b.
Proof. lia. Qed.

Theorem Zstep_lt_r: forall a b, a < b <-> a <= b - 1.
Proof. lia. Qed.

Theorem Zstep_le_l: forall a b, a <= b <-> a - 1 < b.
Proof. lia. Qed.

Theorem Zstep_le_r: forall a b, a <= b <-> a < b + 1.
Proof. lia. Qed.



Theorem Zdiv_mul_le : forall a b q, 0 < b -> a <= q * b <-> (a + b - 1) / b <= q.
Proof.
  intros.
  split.
  { assert (forall x y, x <= y <-> x - 1 < y) as S by lia.
    repeat rewrite S.
    unfold Z.sub at 2.
    rewrite <- (Z_div_plus (a + b - 1) (-(1)) b) by lia.
    replace (a + b - 1 + - (1) * b) with (a - 1) by lia.
    apply Zdiv_lt_upper_bound.
    lia.
  }
  { intro A.
    assert (b > 0) as Pb by lia.
    pose proof (Zdiv_eucl_exist Pb (a + b - 1)) as [[v r] [M R]].
    rewrite M in A.
    replace (b * v + r) with (r + v * b) in A by lia.
    rewrite (Z_div_plus r v b Pb) in A.
    rewrite (Zdiv_small r b R) in A.
    replace a with (v * b + (r - b + 1)) by lia.
    assert (v * b + (r - b + 1) <= v * b) by lia.
    pose proof (Zmult_le_compat_r v q b).
    lia.
  }
Qed.

Theorem Zdiv_mul_ge : forall a b q, 0 < b -> a >= q * b <-> a / b >= q.
Proof.
  intros.
  split.
  { intro A.
    apply Z.le_ge.
    apply Zdiv_le_lower_bound.
    all: lia.
  }
  { intro A.
    apply Znot_lt_ge.
    intro C.
    apply Zdiv_lt_upper_bound in C.
    all: lia.
  }
Qed.

Theorem Zdiv_mul_lt : forall a b q, 0 < b -> a < q * b <-> a / b < q.
Proof.
  intros a b q Bp.
  split.
  { intro A.
    apply Zlt_not_le in A.
    apply Znot_ge_lt.
    rewrite <- Zdiv_mul_ge by lia.
    lia.
  }
  { intro A.
    apply Zlt_not_le in A.
    apply Znot_ge_lt.
    rewrite Zdiv_mul_ge by lia.
    lia.
  }
Qed.


Definition parallelogram_has_gridpoint x0 x1 a b u0 u1 :=
    exists x y, x0 <= x <= x1 /\ u0 < a * x + b * y <= u1.

Lemma parallelogram_reduce:
  forall x0 x1 a b u0 u1,
      parallelogram_has_gridpoint x0 x1 a b u0 u1 <->
      parallelogram_has_gridpoint x0 x1 (a mod b) b u0 u1.
Proof.
  intros x0 x1 a b u0 u1.
  unfold parallelogram_has_gridpoint.
  split.
  { intros [x [y [X U]]].
    exists x, (y + (a / b) * x).
    replace (a mod b * x + b * (y + a / b * x)) with ((b * (a / b) + a mod b) * x + b * y) by lia.
    rewrite <- Z_div_mod_eq_full.
    split. exact X. exact U.
  }
  { intros [x [y [X U]]].
    exists x, (y - (a / b) * x).
    assert (b = 0 \/ b <> 0) as [Bz | Bnz] by lia.
    { rewrite Bz in U.
      rewrite Zmod_0_r in U. 
      lia.
    }
    { rewrite (Zmod_eq_full a b Bnz) in U.
      lia.
    }
  }
Qed.

Lemma parallelogram_simple:
  forall x0 x1 b u0 u1, 0 < b ->
      parallelogram_has_gridpoint x0 x1 0 b u0 u1 <->
      (x0 <= x1 /\ u0 / b < u1 / b).
Proof.
  intros x0 x1 b u0 u1 Pb.
  unfold parallelogram_has_gridpoint.
  split.
  { intros [x [y [X [U0 U1]]]].
    replace (0 * x + b * y) with (y * b) in * by lia.
    apply (Zdiv_lt_upper_bound u0 b y Pb) in U0.
    apply (Zdiv_le_lower_bound u1 b y Pb) in U1.
    lia.
  }
  { intros [X U].
    exists x0, (u1 / b).
    replace (0 * x0 + b * (u1 / b)) with ((u1 / b) * b) in * by lia.
    split.
    lia.
    split.
    apply Zdiv_mul_lt. lia. lia.
    pose proof (Z_mult_div_ge u1 b).
    lia.
  }
Qed.

Lemma parallelogram_flip:
  forall x0 x1 a b u0 u1, 0 < a -> 0 < b -> x0 <= x1 ->
      parallelogram_has_gridpoint x0 x1 a b u0 u1 <->
      let y0 := (u0 - a * x1) / b + 1 in
      let y1 := (u1 - a * x0) / b in
          parallelogram_has_gridpoint y0 y1 b a u0 u1.
Proof.
  intros x0 x1 a b u0 u1 Pa Pb Xs.
  unfold parallelogram_has_gridpoint.
  split.
  { intros [x [y [[X0 X1] [U0 U1]]]].
    exists y, x.
    repeat (split; try lia).
    { apply Zstep_lt_l.
      apply (Zdiv_mul_lt _ b _ Pb).
      apply (Zmult_le_compat_l _ _ a) in X1.
      lia.
      lia.
    }
    { apply Z.ge_le.
      apply (Zdiv_mul_ge _ b _ Pb).
      apply (Zmult_le_compat_l _ _ a) in X0.
      lia.
      lia.
    }
  }
  { intros [x [y [[X0 X1] [U0 U1]]]].
    assert (y < x0 \/ x0 <= y < x1 \/ x1 <= y) as [Clip_low | [Normal | Clip_high ]] by lia.
    { exists x0, x.
      apply (Zmult_lt_compat_l y x0 a Pa) in Clip_low.
      apply Z.le_ge in X1.
      apply (Zdiv_mul_ge _ _ _ Pb) in X1.
      lia.
    }
    { exists y, x.
      lia.
    }
    { exists x1, x.
      apply (Zmult_le_compat_l x1 y a) in Clip_high.
      apply Zstep_lt_l in X0.
      apply (Zdiv_mul_lt _ _ _ Pb) in X0.
      lia.
      lia.
    }
  }
Qed.

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
  { intros [x0 [x1 [x0_in_range [x1_in_range [LOW HIGH]]]]].
    remember (data0 + x0 * Z.pos spacing0 - (data1 + x1 * Z.pos spacing1)) as y.
    destruct y as [ | py | ny].
    { exists x0, 0,          x1, 0.          lia. }
    { exists x0, 0,          x1, (Z.pos py). lia. }
    { exists x0, (Z.pos ny), x1, 0.          lia. }
  }
  { intros [x0 [y0 [x1 [y1 [[] [[]] ]]]]].
    exists x0, x1. lia.
  }
Qed.

Definition overlap_definition_bound (m0 : M) (m1 : M) :=
  let d := data m1 - data m0 in
    exists x0 x1,
      0 <= x0 < Zwidth m0 ∧
      atm m0 x0 (Zheight m0 - 1) >= atm m1 0 0 ∧
      atm m0 x0 0 <= atm m1 (Zwidth m1 - 1) (Zheight m1 - 1) ∧
      d - (Zheight m0) < x0 * (Zspacing m0) - x1 * (Zspacing m1) < d + (Zheight m1).

Lemma overlap_definition_bound_correct : forall M0 M1, overlap_definition_bound M0 M1 <-> overlap_definition_short M0 M1.
Proof.
  destruct M0, M1.
  unfold overlap_definition_bound, overlap_definition_short.
  unfold inm, atm.
  unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
  split.
  { intros [x0 [x1 [x0_in_range [H1 [H2 [LOW HIGH]]]]]].
    exists x0.
    assert (x1 < 0 \/ 0 <= x1 < Z.pos width1 \/ Z.pos width1 <= x1) as s by lia.
    destruct s as [Clip_low | [Normal | Clip_high]].
    { exists 0.
      lia.
    }
    { exists x1.
      lia.
    }
    { exists (Z.pos width1 - 1).
      pose proof (Zmult_le_compat_r (Z.pos width1 - 1) x1 (Z.pos spacing1)).
      lia.
    }
  }
  { intros [x0 [x1 [x0_in_range [x1_in_range [LOW HIGH]]]]].
    exists x0, x1.
    pose proof (Zmult_le_compat_r x1 (Z.pos width1 - 1) (Z.pos spacing1)).
    lia.
  }
Qed.

Definition overlap_definition_parallelogram (m0 : M) (m1 : M) :=
  let d := data m1 - data m0 in
  let u0 := d - Zheight m0 in
  let u1 := d + Zheight m1 - 1 in
  let x0 := Z.max 0 (u0 / Zspacing m0 + 1) in
  let x1 := Z.min (Zwidth m0 - 1) ((u1 + Zspacing m1 * (Zwidth m1 - 1)) / Zspacing m0) in
      parallelogram_has_gridpoint x0 x1 (Zspacing m0) (Zspacing m1) u0 u1.

Lemma overlap_definition_parallelogram_correct : forall M0 M1, overlap_definition_parallelogram M0 M1 <-> overlap_definition_bound M0 M1.
Proof.
  destruct M0, M1.
  unfold overlap_definition_parallelogram, overlap_definition_bound.
  unfold inm, atm.
  unfold data, Zheight, Zwidth, Zspacing, height, width, spacing.
  split.
  { intros [x0 [x1 [[LOW_x0 HIGH_x0] [LOW_p HIGH_p]]]].
    exists x0, (-x1).
    replace (x0 * Z.pos spacing0 - - x1 * Z.pos spacing1) with (x0 * Z.pos spacing0 + x1 * Z.pos spacing1) by lia.
    repeat (split; try lia).
    { assert (x0 * Z.pos spacing0 >= data1 - data0 - (Z.pos height0 - 1)).
      { apply Z.le_ge.
        rewrite Zdiv_mul_le by lia.
        replace (data1 - data0 - (Z.pos height0 - 1) + Z.pos spacing0 - 1) with (data1 - data0 - Z.pos height0 + 1 * Z.pos spacing0) by lia.
        rewrite Z_div_plus by lia.
        lia.
      }
      lia.
    }
    { assert (data1 - data0 + Z.pos spacing1 * (Z.pos width1 - 1) + (Z.pos height1 - 1) >= x0 * Z.pos spacing0) as G.
      { rewrite Zdiv_mul_ge by lia.
        apply Z.le_ge.
        apply Zstep_le_r.
        replace (data1 - data0 + Z.pos spacing1 * (Z.pos width1 - 1) + (Z.pos height1 - 1))
           with (data1 - data0 + Z.pos height1 - 1 + Z.pos spacing1 * (Z.pos width1 - 1)) by lia.
         lia.
      }
      { lia. }
    }
  }
  { intros [x0 [x1 [[LOW_x0 HIGH_x0] [Clip_low [Clip_high [LOW_p HIGH_p]]]]]].
    exists x0, (-x1).
    repeat (split; try lia).
    { apply Z.max_lub.
      { lia. }
      { assert (data1 - data0 - (Z.pos height0 - 1) <= x0 * Z.pos spacing0) as H by lia.
        rewrite Zdiv_mul_le in H by lia.
        replace (data1 - data0 - (Z.pos height0 - 1) + Z.pos spacing0 - 1) with (data1 - data0 - Z.pos height0 + 1 * Z.pos spacing0) in H by lia.
        rewrite Z_div_plus in H by lia.
        lia.
      }
    }
    { apply Z.min_glb.
      { lia. }
      { assert (data1 - data0 + Z.pos spacing1 * (Z.pos width1 - 1) + (Z.pos height1 - 1) >= x0 * Z.pos spacing0) as H by lia.
        rewrite Zdiv_mul_ge in H by lia.
        apply Z.ge_le in H.
        apply Zstep_le_r in H.
        replace (data1 - data0 + Z.pos spacing1 * (Z.pos width1 - 1) + (Z.pos height1 - 1))
           with (data1 - data0 + Z.pos height1 - 1 + Z.pos spacing1 * (Z.pos width1 - 1)) in H by lia.
        lia.
      }
    }
  }
Qed.

Inductive Result := Overlap | NoOverlap | Timeout.

Definition result_correct r p := (p <-> (r = Overlap)) /\ (r <> Timeout).

Fixpoint parallelogram_implementation x0 x1 a b u0 u1 gas :=
  match gas with
  | O => Timeout
  | S g => 
      match x0 <=? x1 with
      | false => NoOverlap
      | true =>
          match b =? 0 with
          | true => Overlap
          | false =>
              let a2 := a mod b in
              let y0 := (u0 - a2 * x1) / b + 1 in
              let y1 := (u1 - a2 * x0) / b in
                  parallelogram_implementation y0 y1 b a2 u0 u1 g
          end
      end
  end.

Lemma Zmod_nn : forall a b, 0 < b -> (a mod b = 0) \/ (a mod b > 0).
Proof.
  intros a b Pb.
  assert (b > 0) as Pb2 by lia.
  pose proof Z_mod_lt a b Pb2.
  lia.
Qed.

Lemma parallelogram_implementation_correct : forall gas x0 x1 a b u0 u1, (Nat.lt (Z.to_nat b) gas) -> 0 < b -> 
    result_correct (parallelogram_implementation x0 x1 a b u0 u1 gas) (parallelogram_has_gridpoint x0 x1 a b u0 u1).
Proof.
  induction gas.
  { lia.
  }
  { intros x0 x1 a b u0 u1 Gas Pb.
    unfold parallelogram_implementation. fold parallelogram_implementation.
    unfold result_correct.
    rewrite parallelogram_reduce by lia.
    assert (x1 < x0 \/ x0 <= x1) as [NX | X] by lia.
    { pose proof (Z.leb_gt x0 x1) as [_ H].
      rewrite (H NX).
      repeat (split; try discriminate).
      intros [x [y [C _]]].
      lia.
    }
    { rewrite (Zle_imp_le_bool x0 x1 X).
      pose proof (Z.eqb_neq b 0) as [_ H].
      rewrite H by lia.
      pose proof (Zmod_nn a b Pb) as [Zm | Pm].
      { rewrite Zm.
        rewrite parallelogram_simple by lia.
        rewrite Zstep_lt_l.
        replace (u0 - 0 * x1) with u0 by lia.
        replace (u1 - 0 * x0) with u1 by lia.
        destruct gas.
        { lia.
        }
        { unfold parallelogram_implementation.
          assert (u0 / b + 1 <= u1 / b \/ u1 / b < u0 / b + 1) as [R | NR] by lia.
          { rewrite (Zle_imp_le_bool _ _ R).
            rewrite Z.eqb_refl.
            repeat (split; try lia; try discriminate).
          }
          { pose proof (Z.leb_gt (u0 / b + 1) (u1 / b)) as [_ H1].
            rewrite (H1 NR).
            repeat (split; try lia; try discriminate).
          }
        }
      }
      { pose proof (Z_mod_lt a b).
        rewrite parallelogram_flip by lia.
        apply IHgas.
        all: lia.
      }
    }
  }
Qed.

Definition overlap_implementation (m0 : M) (m1 : M) :=
  let a := Zspacing m0 in
  let b := Zspacing m1 in
  let d := data m1 - data m0 in
  let u0 := d - Zheight m0 in
  let u1 := d + Zheight m1 - 1 in
  let x0 := Z.max 0 (u0 / a + 1) in
  let x1 := Z.min (Zwidth m0 - 1) ((u1 + b * (Zwidth m1 - 1)) / a) in
  let gas := (S (Z.to_nat b)) in
      parallelogram_implementation x0 x1 a b u0 u1 gas.

Lemma overlap_implementation_correct : forall m0 m1, result_correct (overlap_implementation m0 m1) (overlap_definition m0 m1).
Proof.
  intros m0 m1.
  unfold result_correct.
  rewrite <- overlap_definition_short_correct.
  rewrite <- overlap_definition_bound_correct.
  rewrite <- overlap_definition_parallelogram_correct.
  unfold overlap_implementation, overlap_definition_parallelogram.
  apply parallelogram_implementation_correct.
  all: (unfold Zspacing; lia).
Qed.

Close Scope Z_scope.

From Coq Require Import Extraction.

Extraction Language OCaml.

Extraction M. Extraction parallelogram_implementation. Extraction overlap_implementation.

