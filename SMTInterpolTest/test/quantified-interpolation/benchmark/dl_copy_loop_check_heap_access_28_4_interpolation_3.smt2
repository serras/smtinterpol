(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-option :print-terms-cse false)

(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_copy.spl:28:4-19:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun Axiom_17$0 () Bool)
(declare-fun Axiom_18$0 () Bool)
(declare-fun Axiom_19$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_2$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun b_2$0 () Loc)
(declare-fun b_init$0 () Loc)
(declare-fun c_3$0 () Loc)
(declare-fun c_init$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun d_3$0 () Loc)
(declare-fun d_4$0 () Loc)
(declare-fun d_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_5$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun old_d_2$0 () Loc)
(declare-fun old_d_4$0 () Loc)
(declare-fun old_d_init$0 () Loc)
(declare-fun prev$0 () FldLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun tmp_2$0 () Loc)
(declare-fun tmp_3$0 () Loc)
(declare-fun tmp_init$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y)
            (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_d_4$0 ?y ?y)) (= old_d_4$0 ?y)
            (Btwn$0 next$0 old_d_4$0 (read$0 next$0 old_d_4$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b_init$0) b_init$0))
            (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_d_4$0) old_d_4$0))
            (not (Btwn$0 next$0 old_d_4$0 ?y ?y)) (= old_d_4$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P8))

(assert (! (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) (read$0 next$0 b_init$0)) :named P9))

(assert (! (Btwn$0 next$0 old_d_4$0 (read$0 next$0 old_d_4$0) (read$0 next$0 old_d_4$0)) :named P10))

(assert (! (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0)
  (read$0 next$0 old_curr_4$0)) :named P11))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_23$0)) (not (in$0 null$0 sk_?X_23$0)))) :named P12))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_23$0)) (not (in$0 null$0 sk_?X_23$0)))) :named P13))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_23$0)) (not (in$0 null$0 sk_?X_23$0)))) :named P14))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_23$0)) (not (in$0 null$0 sk_?X_23$0)))) :named P15))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_23$0))
        (not (in$0 a_2$0 sk_?X_23$0)))) :named P16))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_23$0)) (not (in$0 a_2$0 sk_?X_23$0)))) :named P17))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_23$0)) (not (in$0 a_2$0 sk_?X_23$0)))) :named P18))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_23$0)) (not (in$0 a_2$0 sk_?X_23$0)))) :named P19))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_23$0))
        (not (in$0 c_3$0 sk_?X_23$0)))) :named P20))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_23$0)) (not (in$0 c_3$0 sk_?X_23$0)))) :named P21))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_23$0)) (not (in$0 c_3$0 sk_?X_23$0)))) :named P22))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_23$0)) (not (in$0 c_3$0 sk_?X_23$0)))) :named P23))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_23$0)) (not (in$0 curr_init$0 sk_?X_23$0)))) :named P24))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_23$0)) (not (in$0 curr_init$0 sk_?X_23$0)))) :named P25))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_23$0))
        (not (in$0 curr_init$0 sk_?X_23$0)))) :named P26))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_23$0))
        (not (in$0 curr_init$0 sk_?X_23$0)))) :named P27))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_24$0)) (not (in$0 null$0 sk_?X_24$0)))) :named P28))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_24$0)) (not (in$0 null$0 sk_?X_24$0)))) :named P29))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_24$0)) (not (in$0 null$0 sk_?X_24$0)))) :named P30))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_24$0)) (not (in$0 null$0 sk_?X_24$0)))) :named P31))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_24$0))
        (not (in$0 a_2$0 sk_?X_24$0)))) :named P32))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_24$0)) (not (in$0 a_2$0 sk_?X_24$0)))) :named P33))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_24$0)) (not (in$0 a_2$0 sk_?X_24$0)))) :named P34))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_24$0)) (not (in$0 a_2$0 sk_?X_24$0)))) :named P35))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_24$0))
        (not (in$0 c_3$0 sk_?X_24$0)))) :named P36))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_24$0)) (not (in$0 c_3$0 sk_?X_24$0)))) :named P37))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_24$0)) (not (in$0 c_3$0 sk_?X_24$0)))) :named P38))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_24$0)) (not (in$0 c_3$0 sk_?X_24$0)))) :named P39))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_24$0)) (not (in$0 curr_init$0 sk_?X_24$0)))) :named P40))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_24$0)) (not (in$0 curr_init$0 sk_?X_24$0)))) :named P41))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_24$0))
        (not (in$0 curr_init$0 sk_?X_24$0)))) :named P42))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_24$0))
        (not (in$0 curr_init$0 sk_?X_24$0)))) :named P43))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_21$0)) (not (in$0 null$0 sk_?X_21$0)))) :named P44))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_21$0)) (not (in$0 null$0 sk_?X_21$0)))) :named P45))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_21$0)) (not (in$0 null$0 sk_?X_21$0)))) :named P46))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_21$0)) (not (in$0 null$0 sk_?X_21$0)))) :named P47))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_21$0))
        (not (in$0 a_2$0 sk_?X_21$0)))) :named P48))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_21$0)) (not (in$0 a_2$0 sk_?X_21$0)))) :named P49))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_21$0)) (not (in$0 a_2$0 sk_?X_21$0)))) :named P50))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_21$0)) (not (in$0 a_2$0 sk_?X_21$0)))) :named P51))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_21$0))
        (not (in$0 c_3$0 sk_?X_21$0)))) :named P52))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_21$0)) (not (in$0 c_3$0 sk_?X_21$0)))) :named P53))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_21$0)) (not (in$0 c_3$0 sk_?X_21$0)))) :named P54))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_21$0)) (not (in$0 c_3$0 sk_?X_21$0)))) :named P55))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_21$0)) (not (in$0 curr_init$0 sk_?X_21$0)))) :named P56))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_21$0)) (not (in$0 curr_init$0 sk_?X_21$0)))) :named P57))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_21$0))
        (not (in$0 curr_init$0 sk_?X_21$0)))) :named P58))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_21$0))
        (not (in$0 curr_init$0 sk_?X_21$0)))) :named P59))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P60))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 Alloc$0 (setenum$0 tmp_3$0)))
                 (or (in$0 x Alloc$0) (in$0 x (setenum$0 tmp_3$0))))
            (and (not (in$0 x Alloc$0)) (not (in$0 x (setenum$0 tmp_3$0)))
                 (not (in$0 x (union$0 Alloc$0 (setenum$0 tmp_3$0))))))) :named P61))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_22$0 sk_?X_21$0))
                 (or (in$0 x sk_?X_22$0) (in$0 x sk_?X_21$0)))
            (and (not (in$0 x sk_?X_22$0)) (not (in$0 x sk_?X_21$0))
                 (not (in$0 x (union$0 sk_?X_22$0 sk_?X_21$0)))))) :named P62))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 (setenum$0 tmp_3$0)))
                 (or (in$0 x FP$0) (in$0 x (setenum$0 tmp_3$0))))
            (and (not (in$0 x FP$0)) (not (in$0 x (setenum$0 tmp_3$0)))
                 (not (in$0 x (union$0 FP$0 (setenum$0 tmp_3$0))))))) :named P63))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P64))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_24$0 sk_?X_23$0))
                 (or (in$0 x sk_?X_24$0) (in$0 x sk_?X_23$0)))
            (and (not (in$0 x sk_?X_24$0)) (not (in$0 x sk_?X_23$0))
                 (not (in$0 x (union$0 sk_?X_24$0 sk_?X_23$0)))))) :named P65))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_24$0) (in$0 x sk_?X_23$0)
                 (in$0 x (intersection$0 sk_?X_24$0 sk_?X_23$0)))
            (and (or (not (in$0 x sk_?X_24$0)) (not (in$0 x sk_?X_23$0)))
                 (not (in$0 x (intersection$0 sk_?X_24$0 sk_?X_23$0)))))) :named P66))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_22$0) (in$0 x sk_?X_21$0)
                 (in$0 x (intersection$0 sk_?X_22$0 sk_?X_21$0)))
            (and (or (not (in$0 x sk_?X_22$0)) (not (in$0 x sk_?X_21$0)))
                 (not (in$0 x (intersection$0 sk_?X_22$0 sk_?X_21$0)))))) :named P67))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P68))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P69))

(assert (! (= (read$0 next$0 null$0) null$0) :named P70))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P71))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P72))

(assert (! (or
    (and (Btwn$0 next$0 a_init$0 curr_init$0 curr_init$0)
         (or (and (= null$0 old_curr_init$0) (= a_init$0 curr_init$0))
             (and (= (read$0 next$0 old_curr_init$0) curr_init$0)
                  (= (read$0 prev$0 a_init$0) null$0)
                  (in$0 old_curr_init$0 sk_?X_24$0)))
         Axiom_17$0)
    (not
         (dlseg_struct$0 sk_?X_24$0 next$0 prev$0 a_init$0 null$0 curr_init$0
           old_curr_init$0))) :named P73))

(assert (! (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) old_curr_init$0)
                  (in$0 b_init$0 sk_?X_23$0))
             (and (= curr_init$0 null$0) (= old_curr_init$0 b_init$0)))
         Axiom_19$0)
    (not
         (dlseg_struct$0 sk_?X_23$0 next$0 prev$0 curr_init$0 old_curr_init$0
           null$0 b_init$0))) :named P74))

(assert (! (= FP_3$0 (union$0 FP$0 (setenum$0 tmp_3$0))) :named P75))

(assert (! (= a_2$0 a_init$0) :named P76))

(assert (! (= c_3$0 c_init$0) :named P77))

(assert (! (= d_3$0 d_init$0) :named P78))

(assert (! (= old_curr_4$0 old_curr_init$0) :named P79))

(assert (! (= old_d_2$0 old_d_init$0) :named P80))

(assert (! (= tmp_2$0 tmp_init$0) :named P81))

(assert (! (= emptyset$0 (intersection$0 sk_?X_22$0 sk_?X_21$0)) :named P82))

(assert (! (= sk_?X_20$0 (union$0 sk_?X_22$0 sk_?X_21$0)) :named P83))

(assert (! (= sk_?X_21$0 (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0)) :named P84))

(assert (! (= sk_?X_23$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0 b_init$0)) :named P85))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P86))

(assert (! (dlseg_struct$0 sk_?X_23$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0
  b_init$0) :named P87))

(assert (! (not (= curr_4$0 null$0)) :named P88))

(assert (! (not (in$0 null$0 Alloc$0)) :named P89))

(assert (! (not (in$0 tmp_3$0 Alloc$0)) :named P90))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0
                     d_init$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 c_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0
                          d_init$0)))))) :named P91))

(assert (! (or
    (and (Btwn$0 next$0 c_init$0 null$0 null$0)
         (or (and (= null$0 d_init$0) (= c_init$0 null$0))
             (and (= (read$0 next$0 d_init$0) null$0)
                  (= (read$0 prev$0 c_init$0) null$0)
                  (in$0 d_init$0 sk_?X_21$0)))
         Axiom_18$0)
    (not
         (dlseg_struct$0 sk_?X_21$0 next$0 prev$0 c_init$0 null$0 null$0
           d_init$0))) :named P92))

(assert (! (= Alloc_2$0 (union$0 Alloc$0 (setenum$0 tmp_3$0))) :named P93))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P94))

(assert (! (= b_2$0 b_init$0) :named P95))

(assert (! (= curr_4$0 curr_init$0) :named P96))

(assert (! (= d_4$0 tmp_3$0) :named P97))

(assert (! (= old_curr_5$0 curr_4$0) :named P98))

(assert (! (= old_d_4$0 d_3$0) :named P99))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P100))

(assert (! (= emptyset$0 (intersection$0 sk_?X_24$0 sk_?X_23$0)) :named P101))

(assert (! (= sk_?X_20$0 FP$0) :named P102))

(assert (! (= sk_?X_22$0 (union$0 sk_?X_24$0 sk_?X_23$0)) :named P103))

(assert (! (= sk_?X_24$0
  (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0 old_curr_init$0)) :named P104))

(assert (! (dlseg_struct$0 sk_?X_21$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0) :named P105))

(assert (! (dlseg_struct$0 sk_?X_24$0 next$0 prev$0 a_init$0 null$0 curr_init$0
  old_curr_init$0) :named P106))

(assert (! (not (= tmp_3$0 null$0)) :named P107))

(assert (! (not (in$0 d_4$0 FP_3$0)) :named P108))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_init$0 l1 curr_init$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0
                     old_curr_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 a_init$0 l1 curr_init$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a_init$0 null$0
                          curr_init$0 old_curr_init$0)))))) :named P109))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0
                     null$0 b_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0
                          old_curr_init$0 null$0 b_init$0)))))) :named P110))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P111))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P112))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P113))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P114))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P115))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P116))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P117))

(check-sat)

(get-interpolants (and P33 P66 P56 P17 P103 P3 P78 P98 P85 P67 P14 P117 P43 P34 P28 P10 P72 P102 P68 P27 P37 P6 P104 P94 P83 P4 P38 P96 P12 P21 P5 P105 P15 P100 P51 P49 P0 P81 P57 P20 P109 P74 P64 P52 P42 P62 P44 P80 P89 P22 P8 P77 P75 P48 P36 P31 P39 P25 P97) (and P32 P46 P76 P88 P115 P113 P13 P40 P41 P101 P58 P86 P71 P79 P92 P107 P61 P108 P63 P30 P2 P54 P70 P82 P73 P93 P90 P45 P91 P95 P18 P19 P110 P35 P65 P69 P87 P50 P16 P23 P111 P114 P53 P112 P55 P9 P47 P1 P106 P116 P59 P60 P11 P29 P7 P26 P84 P99 P24))

(exit)