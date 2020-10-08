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
  tests/spl/dl/dl_copy.spl:29:4-20:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun Axiom_20$0 () Bool)
(declare-fun Axiom_21$0 () Bool)
(declare-fun Axiom_22$0 () Bool)
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
(declare-fun next_2$0 () FldLoc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_5$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun old_d_2$0 () Loc)
(declare-fun old_d_4$0 () Loc)
(declare-fun old_d_init$0 () Loc)
(declare-fun prev$0 () FldLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
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
        (or (not (Btwn$0 next$0 tmp_3$0 ?y ?y)) (= tmp_3$0 ?y)
            (Btwn$0 next$0 tmp_3$0 (read$0 next$0 tmp_3$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_d_4$0 ?y ?y)) (= old_d_4$0 ?y)
            (Btwn$0 next$0 old_d_4$0 (read$0 next$0 old_d_4$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b_init$0) b_init$0))
            (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 tmp_3$0) tmp_3$0))
            (not (Btwn$0 next$0 tmp_3$0 ?y ?y)) (= tmp_3$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_d_4$0) old_d_4$0))
            (not (Btwn$0 next$0 old_d_4$0 ?y ?y)) (= old_d_4$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))) :named P9))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P10))

(assert (! (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) (read$0 next$0 b_init$0)) :named P11))

(assert (! (Btwn$0 next$0 tmp_3$0 (read$0 next$0 tmp_3$0) (read$0 next$0 tmp_3$0)) :named P12))

(assert (! (Btwn$0 next$0 old_d_4$0 (read$0 next$0 old_d_4$0) (read$0 next$0 old_d_4$0)) :named P13))

(assert (! (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0)
  (read$0 next$0 old_curr_4$0)) :named P14))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))) :named P15))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))) :named P16))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) null$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))) :named P17))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))) :named P18))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))) :named P19))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_28$0))
        (not (in$0 a_2$0 sk_?X_28$0)))) :named P20))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))) :named P21))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) a_2$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))) :named P22))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))) :named P23))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))) :named P24))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_28$0))
        (not (in$0 c_3$0 sk_?X_28$0)))) :named P25))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))) :named P26))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) c_3$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))) :named P27))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))) :named P28))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))) :named P29))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_28$0)) (not (in$0 curr_init$0 sk_?X_28$0)))) :named P30))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 curr_init$0 sk_?X_28$0)))) :named P31))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) curr_init$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 curr_init$0 sk_?X_28$0)))) :named P32))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_28$0))
        (not (in$0 curr_init$0 sk_?X_28$0)))) :named P33))

(assert (! (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0))
        (not (in$0 curr_init$0 sk_?X_28$0)))) :named P34))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))) :named P35))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))) :named P36))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) null$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))) :named P37))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))) :named P38))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))) :named P39))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_29$0))
        (not (in$0 a_2$0 sk_?X_29$0)))) :named P40))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))) :named P41))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) a_2$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))) :named P42))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))) :named P43))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))) :named P44))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_29$0))
        (not (in$0 c_3$0 sk_?X_29$0)))) :named P45))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))) :named P46))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) c_3$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))) :named P47))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))) :named P48))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))) :named P49))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_29$0)) (not (in$0 curr_init$0 sk_?X_29$0)))) :named P50))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 curr_init$0 sk_?X_29$0)))) :named P51))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) curr_init$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 curr_init$0 sk_?X_29$0)))) :named P52))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_29$0))
        (not (in$0 curr_init$0 sk_?X_29$0)))) :named P53))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0))
        (not (in$0 curr_init$0 sk_?X_29$0)))) :named P54))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))) :named P55))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))) :named P56))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) null$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))) :named P57))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))) :named P58))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))) :named P59))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_26$0))
        (not (in$0 a_2$0 sk_?X_26$0)))) :named P60))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))) :named P61))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) a_2$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))) :named P62))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))) :named P63))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))) :named P64))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_26$0))
        (not (in$0 c_3$0 sk_?X_26$0)))) :named P65))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))) :named P66))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) c_3$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))) :named P67))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))) :named P68))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))) :named P69))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_26$0)) (not (in$0 curr_init$0 sk_?X_26$0)))) :named P70))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 curr_init$0 sk_?X_26$0)))) :named P71))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) curr_init$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 curr_init$0 sk_?X_26$0)))) :named P72))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_26$0))
        (not (in$0 curr_init$0 sk_?X_26$0)))) :named P73))

(assert (! (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0))
        (not (in$0 curr_init$0 sk_?X_26$0)))) :named P74))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P75))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 Alloc$0 (setenum$0 tmp_3$0)))
                 (or (in$0 x Alloc$0) (in$0 x (setenum$0 tmp_3$0))))
            (and (not (in$0 x Alloc$0)) (not (in$0 x (setenum$0 tmp_3$0)))
                 (not (in$0 x (union$0 Alloc$0 (setenum$0 tmp_3$0))))))) :named P76))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_27$0 sk_?X_26$0))
                 (or (in$0 x sk_?X_27$0) (in$0 x sk_?X_26$0)))
            (and (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_26$0))
                 (not (in$0 x (union$0 sk_?X_27$0 sk_?X_26$0)))))) :named P77))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 (setenum$0 tmp_3$0)))
                 (or (in$0 x FP$0) (in$0 x (setenum$0 tmp_3$0))))
            (and (not (in$0 x FP$0)) (not (in$0 x (setenum$0 tmp_3$0)))
                 (not (in$0 x (union$0 FP$0 (setenum$0 tmp_3$0))))))) :named P78))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P79))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_29$0 sk_?X_28$0))
                 (or (in$0 x sk_?X_29$0) (in$0 x sk_?X_28$0)))
            (and (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_28$0))
                 (not (in$0 x (union$0 sk_?X_29$0 sk_?X_28$0)))))) :named P80))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_29$0) (in$0 x sk_?X_28$0)
                 (in$0 x (intersection$0 sk_?X_29$0 sk_?X_28$0)))
            (and (or (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_28$0)))
                 (not (in$0 x (intersection$0 sk_?X_29$0 sk_?X_28$0)))))) :named P81))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_27$0) (in$0 x sk_?X_26$0)
                 (in$0 x (intersection$0 sk_?X_27$0 sk_?X_26$0)))
            (and (or (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_26$0)))
                 (not (in$0 x (intersection$0 sk_?X_27$0 sk_?X_26$0)))))) :named P82))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P83))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P84))

(assert (! (= (read$0 (write$0 next$0 tmp_3$0 null$0) tmp_3$0) null$0) :named P85))

(assert (! (or (= null$0 tmp_3$0)
    (= (read$0 next$0 null$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) null$0))) :named P86))

(assert (! (or (= b_init$0 tmp_3$0)
    (= (read$0 next$0 b_init$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) b_init$0))) :named P87))

(assert (! (or (= tmp_3$0 tmp_3$0)
    (= (read$0 next$0 tmp_3$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) tmp_3$0))) :named P88))

(assert (! (or (= old_d_4$0 tmp_3$0)
    (= (read$0 next$0 old_d_4$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) old_d_4$0))) :named P89))

(assert (! (or (= old_curr_4$0 tmp_3$0)
    (= (read$0 next$0 old_curr_4$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) old_curr_4$0))) :named P90))

(assert (! (= (read$0 next$0 null$0) null$0) :named P91))

(assert (! (= (read$0 next_2$0 null$0) null$0) :named P92))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P93))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P94))

(assert (! (or
    (and (Btwn$0 next$0 a_init$0 curr_init$0 curr_init$0)
         (or (and (= null$0 old_curr_init$0) (= a_init$0 curr_init$0))
             (and (= (read$0 next$0 old_curr_init$0) curr_init$0)
                  (= (read$0 prev$0 a_init$0) null$0)
                  (in$0 old_curr_init$0 sk_?X_29$0)))
         Axiom_20$0)
    (not
         (dlseg_struct$0 sk_?X_29$0 next$0 prev$0 a_init$0 null$0 curr_init$0
           old_curr_init$0))) :named P95))

(assert (! (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) old_curr_init$0)
                  (in$0 b_init$0 sk_?X_28$0))
             (and (= curr_init$0 null$0) (= old_curr_init$0 b_init$0)))
         Axiom_22$0)
    (not
         (dlseg_struct$0 sk_?X_28$0 next$0 prev$0 curr_init$0 old_curr_init$0
           null$0 b_init$0))) :named P96))

(assert (! (= FP_3$0 (union$0 FP$0 (setenum$0 tmp_3$0))) :named P97))

(assert (! (= a_2$0 a_init$0) :named P98))

(assert (! (= c_3$0 c_init$0) :named P99))

(assert (! (= d_3$0 d_init$0) :named P100))

(assert (! (= next_2$0 (write$0 next$0 d_4$0 null$0)) :named P101))

(assert (! (= old_curr_5$0 curr_4$0) :named P102))

(assert (! (= old_d_4$0 d_3$0) :named P103))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P104))

(assert (! (= emptyset$0 (intersection$0 sk_?X_29$0 sk_?X_28$0)) :named P105))

(assert (! (= sk_?X_25$0 FP$0) :named P106))

(assert (! (= sk_?X_27$0 (union$0 sk_?X_29$0 sk_?X_28$0)) :named P107))

(assert (! (= sk_?X_29$0
  (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0 old_curr_init$0)) :named P108))

(assert (! (dlseg_struct$0 sk_?X_26$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0) :named P109))

(assert (! (dlseg_struct$0 sk_?X_29$0 next$0 prev$0 a_init$0 null$0 curr_init$0
  old_curr_init$0) :named P110))

(assert (! (not (= tmp_3$0 null$0)) :named P111))

(assert (! (not (in$0 d_4$0 FP_3$0)) :named P112))

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
                          curr_init$0 old_curr_init$0)))))) :named P113))

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
                          old_curr_init$0 null$0 b_init$0)))))) :named P114))

(assert (! (or
    (and (Btwn$0 next$0 c_init$0 null$0 null$0)
         (or (and (= null$0 d_init$0) (= c_init$0 null$0))
             (and (= (read$0 next$0 d_init$0) null$0)
                  (= (read$0 prev$0 c_init$0) null$0)
                  (in$0 d_init$0 sk_?X_26$0)))
         Axiom_21$0)
    (not
         (dlseg_struct$0 sk_?X_26$0 next$0 prev$0 c_init$0 null$0 null$0
           d_init$0))) :named P115))

(assert (! (= Alloc_2$0 (union$0 Alloc$0 (setenum$0 tmp_3$0))) :named P116))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P117))

(assert (! (= b_2$0 b_init$0) :named P118))

(assert (! (= curr_4$0 curr_init$0) :named P119))

(assert (! (= d_4$0 tmp_3$0) :named P120))

(assert (! (= old_curr_4$0 old_curr_init$0) :named P121))

(assert (! (= old_d_2$0 old_d_init$0) :named P122))

(assert (! (= tmp_2$0 tmp_init$0) :named P123))

(assert (! (= emptyset$0 (intersection$0 sk_?X_27$0 sk_?X_26$0)) :named P124))

(assert (! (= sk_?X_25$0 (union$0 sk_?X_27$0 sk_?X_26$0)) :named P125))

(assert (! (= sk_?X_26$0 (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0)) :named P126))

(assert (! (= sk_?X_28$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0 b_init$0)) :named P127))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P128))

(assert (! (dlseg_struct$0 sk_?X_28$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0
  b_init$0) :named P129))

(assert (! (not (= curr_4$0 null$0)) :named P130))

(assert (! (not (in$0 null$0 Alloc$0)) :named P131))

(assert (! (not (in$0 tmp_3$0 Alloc$0)) :named P132))

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
                          d_init$0)))))) :named P133))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 d_4$0 null$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v d_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not (Btwn$0 next$0 ?z d_4$0 d_4$0)))))
                          (and (not (= d_4$0 ?v))
                               (or (Btwn$0 next$0 ?z d_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u d_4$0)
                               (or (Btwn$0 next$0 null$0 ?v d_4$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 d_4$0
                                               d_4$0)))))
                          (and (not (= d_4$0 ?v))
                               (or (Btwn$0 next$0 ?z d_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 null$0 ?u ?v)
                               (or (Btwn$0 next$0 null$0 ?v d_4$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 d_4$0
                                               d_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v d_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z d_4$0 d_4$0)))))
                 (and (not (= d_4$0 ?v))
                      (or (Btwn$0 next$0 ?z d_4$0 ?v)
                          (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u d_4$0)
                      (or (Btwn$0 next$0 null$0 ?v d_4$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 d_4$0 d_4$0)))))
                 (and (not (= d_4$0 ?v))
                      (or (Btwn$0 next$0 ?z d_4$0 ?v)
                          (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 null$0 ?u ?v)
                      (or (Btwn$0 next$0 null$0 ?v d_4$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 d_4$0 d_4$0)))))
                 (not (Btwn$0 (write$0 next$0 d_4$0 null$0) ?z ?u ?v))))) :named P134))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P135))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P136))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P137))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P138))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P139))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P140))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P141))

(check-sat)

(get-interpolants (and P50 P40 P83 P121 P15 P112 P96 P69 P9 P106 P7 P110 P45 P68 P44 P67 P122 P89 P13 P128 P5 P12 P64 P6 P75 P22 P17 P38 P1 P92 P39 P60 P27 P115 P102 P8 P72 P101 P82 P34 P80 P103 P117 P87 P86 P131 P54 P100 P108 P95 P53 P26 P62 P88 P104 P10 P66 P138 P57 P120 P107 P111 P84 P99 P23 P61 P129 P58 P31 P11 P93) (and P2 P141 P3 P29 P91 P116 P97 P135 P4 P74 P134 P113 P47 P14 P48 P35 P46 P42 P77 P70 P94 P76 P123 P130 P140 P71 P63 P118 P32 P20 P109 P85 P114 P90 P36 P51 P73 P41 P126 P137 P119 P125 P133 P49 P55 P16 P132 P139 P33 P43 P25 P79 P30 P28 P98 P37 P21 P18 P0 P19 P56 P24 P124 P127 P59 P105 P81 P78 P136 P52 P65))

(exit)