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
  tests/spl/dl/dl_remove.spl:40:6-28:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_13$0 () Bool)
(declare-fun Axiom_14$0 () Bool)
(declare-fun Axiom_15$0 () Bool)
(declare-fun Axiom_16$0 () Bool)
(declare-fun Axiom_17$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun c_1$0 () Loc)
(declare-fun c_2$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun d_1$0 () Loc)
(declare-fun d_2$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun tmp_2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y)
            (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y)
            (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_1$0) d_1$0))
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_3$0) prv_3$0))
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) (read$0 next$0 d_1$0)) :named P8))

(assert (! (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) (read$0 next$0 prv_3$0)) :named P9))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P10))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P11))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 c_1$0) FP_1$0)
    (= c_1$0 (ep$0 next$0 FP_1$0 c_1$0))) :named P12))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 d_1$0) FP_1$0)
    (= d_1$0 (ep$0 next$0 FP_1$0 d_1$0))) :named P13))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 curr_3$0) FP_1$0)
    (= curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0))) :named P14))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 prv_2$0) FP_1$0)
    (= prv_2$0 (ep$0 next$0 FP_1$0 prv_2$0))) :named P15))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 prv_3$0) FP_1$0)
    (= prv_3$0 (ep$0 next$0 FP_1$0 prv_3$0))) :named P16))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_21$0)) (not (in$0 c_1$0 sk_?X_21$0)))) :named P17))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_21$0)) (not (in$0 c_1$0 sk_?X_21$0)))) :named P18))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_21$0)) (not (in$0 c_1$0 sk_?X_21$0)))) :named P19))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_21$0)) (not (in$0 c_1$0 sk_?X_21$0)))) :named P20))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_21$0)) (not (in$0 curr_3$0 sk_?X_21$0)))) :named P21))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_21$0)) (not (in$0 curr_3$0 sk_?X_21$0)))) :named P22))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_21$0)) (not (in$0 curr_3$0 sk_?X_21$0)))) :named P23))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_21$0)) (not (in$0 curr_3$0 sk_?X_21$0)))) :named P24))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_21$0))
        (not (in$0 prv_2$0 sk_?X_21$0)))) :named P25))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_21$0)) (not (in$0 prv_2$0 sk_?X_21$0)))) :named P26))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_21$0)) (not (in$0 prv_2$0 sk_?X_21$0)))) :named P27))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_21$0)) (not (in$0 prv_2$0 sk_?X_21$0)))) :named P28))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P29))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P30))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P31))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P32))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P33))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P34))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P35))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P36))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_19$0))
        (not (in$0 prv_2$0 sk_?X_19$0)))) :named P37))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_19$0)) (not (in$0 prv_2$0 sk_?X_19$0)))) :named P38))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_19$0)) (not (in$0 prv_2$0 sk_?X_19$0)))) :named P39))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_19$0)) (not (in$0 prv_2$0 sk_?X_19$0)))) :named P40))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_27$0)) (not (in$0 c_1$0 sk_?X_27$0)))) :named P41))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_27$0)) (not (in$0 c_1$0 sk_?X_27$0)))) :named P42))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_27$0)) (not (in$0 c_1$0 sk_?X_27$0)))) :named P43))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_27$0)) (not (in$0 c_1$0 sk_?X_27$0)))) :named P44))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_27$0)) (not (in$0 curr_3$0 sk_?X_27$0)))) :named P45))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_27$0)) (not (in$0 curr_3$0 sk_?X_27$0)))) :named P46))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_27$0)) (not (in$0 curr_3$0 sk_?X_27$0)))) :named P47))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_27$0)) (not (in$0 curr_3$0 sk_?X_27$0)))) :named P48))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_27$0))
        (not (in$0 prv_2$0 sk_?X_27$0)))) :named P49))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_27$0)) (not (in$0 prv_2$0 sk_?X_27$0)))) :named P50))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_27$0)) (not (in$0 prv_2$0 sk_?X_27$0)))) :named P51))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_27$0)) (not (in$0 prv_2$0 sk_?X_27$0)))) :named P52))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 c_1$0 (ep$0 next$0 FP_1$0 c_1$0) ?y)
            (not (Btwn$0 next$0 c_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P53))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 d_1$0 (ep$0 next$0 FP_1$0 d_1$0) ?y)
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P54))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P55))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_2$0 (ep$0 next$0 FP_1$0 prv_2$0) ?y)
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P56))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 FP_1$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P57))

(assert (! (Btwn$0 next$0 c_1$0 (ep$0 next$0 FP_1$0 c_1$0) (ep$0 next$0 FP_1$0 c_1$0)) :named P58))

(assert (! (Btwn$0 next$0 d_1$0 (ep$0 next$0 FP_1$0 d_1$0) (ep$0 next$0 FP_1$0 d_1$0)) :named P59))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0)
  (ep$0 next$0 FP_1$0 curr_3$0)) :named P60))

(assert (! (Btwn$0 next$0 prv_2$0 (ep$0 next$0 FP_1$0 prv_2$0)
  (ep$0 next$0 FP_1$0 prv_2$0)) :named P61))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 FP_1$0 prv_3$0)
  (ep$0 next$0 FP_1$0 prv_3$0)) :named P62))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P63))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P64))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P65))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P66))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P67))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P68))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P69))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P70))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_24$0))
        (not (in$0 prv_2$0 sk_?X_24$0)))) :named P71))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_24$0)) (not (in$0 prv_2$0 sk_?X_24$0)))) :named P72))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_24$0)) (not (in$0 prv_2$0 sk_?X_24$0)))) :named P73))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_24$0)) (not (in$0 prv_2$0 sk_?X_24$0)))) :named P74))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_26$0)) (not (in$0 c_1$0 sk_?X_26$0)))) :named P75))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_26$0)) (not (in$0 c_1$0 sk_?X_26$0)))) :named P76))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_26$0)) (not (in$0 c_1$0 sk_?X_26$0)))) :named P77))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_26$0)) (not (in$0 c_1$0 sk_?X_26$0)))) :named P78))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_26$0)) (not (in$0 curr_3$0 sk_?X_26$0)))) :named P79))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_26$0)) (not (in$0 curr_3$0 sk_?X_26$0)))) :named P80))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_26$0)) (not (in$0 curr_3$0 sk_?X_26$0)))) :named P81))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_26$0)) (not (in$0 curr_3$0 sk_?X_26$0)))) :named P82))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_26$0))
        (not (in$0 prv_2$0 sk_?X_26$0)))) :named P83))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_26$0)) (not (in$0 prv_2$0 sk_?X_26$0)))) :named P84))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_26$0)) (not (in$0 prv_2$0 sk_?X_26$0)))) :named P85))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_26$0)) (not (in$0 prv_2$0 sk_?X_26$0)))) :named P86))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P87))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P88))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_26$0 sk_?X_24$0))
                 (or (in$0 x sk_?X_26$0) (in$0 x sk_?X_24$0)))
            (and (not (in$0 x sk_?X_26$0)) (not (in$0 x sk_?X_24$0))
                 (not (in$0 x (union$0 sk_?X_26$0 sk_?X_24$0)))))) :named P89))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_22$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_22$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_22$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_22$0)))))) :named P90))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_24$0 FP_Caller$0))
                 (or (in$0 x sk_?X_24$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_24$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_24$0 FP_Caller$0)))))) :named P91))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_19$0 sk_?X_21$0))
                 (or (in$0 x sk_?X_19$0) (in$0 x sk_?X_21$0)))
            (and (not (in$0 x sk_?X_19$0)) (not (in$0 x sk_?X_21$0))
                 (not (in$0 x (union$0 sk_?X_19$0 sk_?X_21$0)))))) :named P92))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_1$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_1$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_1$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P93))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 sk_?X_24$0))
                 (or (in$0 x FP_1$0) (in$0 x sk_?X_24$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x sk_?X_24$0))
                 (not (in$0 x (union$0 FP_1$0 sk_?X_24$0)))))) :named P94))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_26$0) (in$0 x sk_?X_24$0)
                 (in$0 x (intersection$0 sk_?X_26$0 sk_?X_24$0)))
            (and (or (not (in$0 x sk_?X_26$0)) (not (in$0 x sk_?X_24$0)))
                 (not (in$0 x (intersection$0 sk_?X_26$0 sk_?X_24$0)))))) :named P95))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_19$0) (in$0 x sk_?X_21$0)
                 (in$0 x (intersection$0 sk_?X_19$0 sk_?X_21$0)))
            (and (or (not (in$0 x sk_?X_19$0)) (not (in$0 x sk_?X_21$0)))
                 (not (in$0 x (intersection$0 sk_?X_19$0 sk_?X_21$0)))))) :named P96))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc$0 FP_1$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))))) :named P97))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P98))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_24$0) (in$0 x (setminus$0 sk_?X_24$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x sk_?X_24$0)))
                 (not (in$0 x (setminus$0 sk_?X_24$0 FP_1$0)))))) :named P99))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_24$0))
                 (not (in$0 x sk_?X_24$0)))
            (and (or (in$0 x sk_?X_24$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_24$0)))))) :named P100))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P101))

(assert (! (= (read$0 next$0 null$0) null$0) :named P102))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P103))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P104))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_27$0)))
         Axiom_13$0)
    (not (dlseg_struct$0 sk_?X_27$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P105))

(assert (! (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_19$0)))
         Axiom_15$0)
    (not
         (dlseg_struct$0 sk_?X_19$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))) :named P106))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_21$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_17$0)
    (not
         (dlseg_struct$0 sk_?X_21$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))) :named P107))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P108))

(assert (! (= c_2$0 c_1$0) :named P109))

(assert (! (= d_1$0 b$0) :named P110))

(assert (! (= prv_2$0 null$0) :named P111))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P112))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P113))

(assert (! (= emptyset$0 emptyset$0) :named P114))

(assert (! (= sk_?X_19$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)) :named P115))

(assert (! (= sk_?X_21$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)) :named P116))

(assert (! (= sk_?X_22$0 (union$0 sk_?X_20$0 sk_?X_21$0)) :named P117))

(assert (! (dlseg_struct$0 sk_?X_21$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0) :named P118))

(assert (! (= emptyset$0 emptyset$0) :named P119))

(assert (! (= sk_?X_23$0 (union$0 sk_?X_25$0 sk_?X_24$0)) :named P120))

(assert (! (= sk_?X_24$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P121))

(assert (! (= sk_?X_26$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P122))

(assert (! (dlseg_struct$0 sk_?X_24$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0) :named P123))

(assert (! (not (= curr_2$0 null$0)) :named P124))

(assert (! (= sk_?X_27$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P125))

(assert (! (dlseg_struct$0 sk_?X_27$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P126))

(assert (! (not (= a$0 b$0)) :named P127))

(assert (! (not (in$0 null$0 Alloc$0)) :named P128))

(assert (! (not (in$0 prv_3$0 FP_2$0)) :named P129))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_1$0 l1 curr_2$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                     prv_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 c_1$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                          prv_2$0)))))) :named P130))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                     d_1$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                          d_1$0)))))) :named P131))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P132))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_26$0)))
         Axiom_14$0)
    (not
         (dlseg_struct$0 sk_?X_26$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P133))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_24$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_16$0)
    (not
         (dlseg_struct$0 sk_?X_24$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P134))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P135))

(assert (! (= c_1$0 a$0) :named P136))

(assert (! (= curr_2$0 c_1$0) :named P137))

(assert (! (= d_2$0 d_1$0) :named P138))

(assert (! (= tmp_2$0 (read$0 next$0 curr_3$0)) :named P139))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P140))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P141))

(assert (! (= emptyset$0 (intersection$0 sk_?X_20$0 sk_?X_21$0)) :named P142))

(assert (! (= sk_?X_20$0 sk_?X_19$0) :named P143))

(assert (! (= sk_?X_22$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P144))

(assert (! (dlseg_struct$0 sk_?X_19$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0) :named P145))

(assert (! (not (= curr_3$0 null$0)) :named P146))

(assert (! (= emptyset$0 (intersection$0 sk_?X_25$0 sk_?X_24$0)) :named P147))

(assert (! (= sk_?X_23$0 FP_1$0) :named P148))

(assert (! (= sk_?X_25$0 sk_?X_26$0) :named P149))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P150))

(assert (! (dlseg_struct$0 sk_?X_26$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0) :named P151))

(assert (! (= sk_?X_27$0 FP$0) :named P152))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P153))

(assert (! (not (= a$0 null$0)) :named P154))

(assert (! (not (= prv_3$0 null$0)) :named P155))

(assert (! (not (in$0 null$0 Alloc$0)) :named P156))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P157))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_2$0 l1 curr_3$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0
                     prv_3$0))
                 (not (= l1 curr_3$0)))
            (and (or (= l1 curr_3$0) (not (Btwn$0 next$0 c_2$0 l1 curr_3$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0
                          prv_3$0)))))) :named P158))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                     d_2$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                          d_2$0)))))) :named P159))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P160))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P161))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P162))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P163))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P164))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P165))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P166))

(check-sat)

(get-interpolants (and P7 P66 P63 P164 P45 P123 P29 P137 P61 P118 P38 P41 P91 P70 P0 P160 P67 P5 P55 P47 P134 P92 P133 P132 P139 P46 P86 P68 P85 P112 P26 P99 P121 P8 P15 P28 P145 P161 P60 P56 P23 P57 P154 P94 P14 P20 P106 P108 P101 P155 P17 P10 P54 P125 P90 P52 P82 P111 P18 P44 P141 P3 P128 P4 P51 P49 P59 P71 P9 P11 P127 P126 P19 P42 P21 P77 P43 P81 P1 P36 P146 P113 P87 P116) (and P151 P158 P130 P89 P80 P120 P27 P35 P157 P53 P149 P140 P88 P93 P143 P109 P150 P84 P107 P22 P48 P153 P110 P12 P148 P135 P104 P58 P69 P165 P40 P32 P166 P76 P100 P31 P131 P37 P163 P159 P103 P50 P33 P6 P13 P73 P24 P39 P105 P78 P156 P147 P65 P79 P30 P117 P62 P102 P138 P119 P98 P162 P114 P144 P34 P152 P72 P136 P124 P115 P75 P64 P96 P129 P16 P95 P83 P25 P2 P142 P122 P97 P74))

(exit)