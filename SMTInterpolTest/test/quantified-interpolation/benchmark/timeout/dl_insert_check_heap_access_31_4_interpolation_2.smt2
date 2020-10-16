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
  tests/spl/dl/dl_insert.spl:31:4-21:Possible heap access through null or dangling reference
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
(declare-fun Axiom_6$0 () Bool)
(declare-fun Axiom_7$0 () Bool)
(declare-fun Axiom_8$0 () Bool)
(declare-fun Axiom_9$0 () Bool)
(declare-fun Axiom_10$0 () Bool)
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
(declare-fun elt$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y)
            (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y)
            (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_1$0) d_1$0))
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_3$0) prv_3$0))
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 elt$0) elt$0))
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P9))

(assert (! (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) (read$0 next$0 d_1$0)) :named P10))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P11))

(assert (! (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) (read$0 next$0 prv_3$0)) :named P12))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P13))

(assert (! (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) (read$0 next$0 elt$0)) :named P14))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_21$0 c_1$0) sk_?X_21$0)
    (= c_1$0 (ep$0 next$0 sk_?X_21$0 c_1$0))) :named P15))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_21$0 d_1$0) sk_?X_21$0)
    (= d_1$0 (ep$0 next$0 sk_?X_21$0 d_1$0))) :named P16))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_21$0 curr_3$0) sk_?X_21$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_21$0 curr_3$0))) :named P17))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_21$0 elt$0) sk_?X_21$0)
    (= elt$0 (ep$0 next$0 sk_?X_21$0 elt$0))) :named P18))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_21$0 prv_2$0) sk_?X_21$0)
    (= prv_2$0 (ep$0 next$0 sk_?X_21$0 prv_2$0))) :named P19))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_21$0 prv_3$0) sk_?X_21$0)
    (= prv_3$0 (ep$0 next$0 sk_?X_21$0 prv_3$0))) :named P20))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_22$0)) (not (in$0 c_1$0 sk_?X_22$0)))) :named P21))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_22$0)) (not (in$0 c_1$0 sk_?X_22$0)))) :named P22))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_22$0)) (not (in$0 c_1$0 sk_?X_22$0)))) :named P23))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_22$0)) (not (in$0 c_1$0 sk_?X_22$0)))) :named P24))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_22$0)) (not (in$0 c_1$0 sk_?X_22$0)))) :named P25))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_22$0)) (not (in$0 curr_3$0 sk_?X_22$0)))) :named P26))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_22$0)) (not (in$0 curr_3$0 sk_?X_22$0)))) :named P27))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_22$0)) (not (in$0 curr_3$0 sk_?X_22$0)))) :named P28))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_22$0)) (not (in$0 curr_3$0 sk_?X_22$0)))) :named P29))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_22$0)) (not (in$0 curr_3$0 sk_?X_22$0)))) :named P30))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_22$0))
        (not (in$0 prv_2$0 sk_?X_22$0)))) :named P31))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_22$0)) (not (in$0 prv_2$0 sk_?X_22$0)))) :named P32))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_22$0)) (not (in$0 prv_2$0 sk_?X_22$0)))) :named P33))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_22$0)) (not (in$0 prv_2$0 sk_?X_22$0)))) :named P34))

(assert (! (or (not Axiom_9$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_22$0))
        (not (in$0 prv_2$0 sk_?X_22$0)))) :named P35))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P36))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P37))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P38))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P39))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_24$0)) (not (in$0 c_1$0 sk_?X_24$0)))) :named P40))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P41))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P42))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P43))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P44))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_24$0)) (not (in$0 curr_3$0 sk_?X_24$0)))) :named P45))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_24$0))
        (not (in$0 prv_2$0 sk_?X_24$0)))) :named P46))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_24$0)) (not (in$0 prv_2$0 sk_?X_24$0)))) :named P47))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_24$0)) (not (in$0 prv_2$0 sk_?X_24$0)))) :named P48))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_24$0)) (not (in$0 prv_2$0 sk_?X_24$0)))) :named P49))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_24$0))
        (not (in$0 prv_2$0 sk_?X_24$0)))) :named P50))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_21$0 c_1$0) ?y)
            (not (Btwn$0 next$0 c_1$0 ?y ?y)) (not (in$0 ?y sk_?X_21$0)))) :named P51))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_21$0 d_1$0) ?y)
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (not (in$0 ?y sk_?X_21$0)))) :named P52))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_21$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_21$0)))) :named P53))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 elt$0 (ep$0 next$0 sk_?X_21$0 elt$0) ?y)
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (not (in$0 ?y sk_?X_21$0)))) :named P54))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_21$0 prv_2$0) ?y)
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (not (in$0 ?y sk_?X_21$0)))) :named P55))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_21$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y sk_?X_21$0)))) :named P56))

(assert (! (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_21$0 c_1$0)
  (ep$0 next$0 sk_?X_21$0 c_1$0)) :named P57))

(assert (! (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_21$0 d_1$0)
  (ep$0 next$0 sk_?X_21$0 d_1$0)) :named P58))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_21$0 curr_3$0)
  (ep$0 next$0 sk_?X_21$0 curr_3$0)) :named P59))

(assert (! (Btwn$0 next$0 elt$0 (ep$0 next$0 sk_?X_21$0 elt$0)
  (ep$0 next$0 sk_?X_21$0 elt$0)) :named P60))

(assert (! (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_21$0 prv_2$0)
  (ep$0 next$0 sk_?X_21$0 prv_2$0)) :named P61))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_21$0 prv_3$0)
  (ep$0 next$0 sk_?X_21$0 prv_3$0)) :named P62))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P63))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P64))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P65))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P66))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_19$0)) (not (in$0 c_1$0 sk_?X_19$0)))) :named P67))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P68))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P69))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P70))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P71))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_19$0)) (not (in$0 curr_3$0 sk_?X_19$0)))) :named P72))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_19$0))
        (not (in$0 prv_2$0 sk_?X_19$0)))) :named P73))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_19$0)) (not (in$0 prv_2$0 sk_?X_19$0)))) :named P74))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_19$0)) (not (in$0 prv_2$0 sk_?X_19$0)))) :named P75))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_19$0)) (not (in$0 prv_2$0 sk_?X_19$0)))) :named P76))

(assert (! (or (not Axiom_10$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_19$0))
        (not (in$0 prv_2$0 sk_?X_19$0)))) :named P77))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_17$0)) (not (in$0 c_1$0 sk_?X_17$0)))) :named P78))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_17$0)) (not (in$0 c_1$0 sk_?X_17$0)))) :named P79))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_17$0)) (not (in$0 c_1$0 sk_?X_17$0)))) :named P80))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_17$0)) (not (in$0 c_1$0 sk_?X_17$0)))) :named P81))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_17$0)) (not (in$0 c_1$0 sk_?X_17$0)))) :named P82))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_17$0)) (not (in$0 curr_3$0 sk_?X_17$0)))) :named P83))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_17$0)) (not (in$0 curr_3$0 sk_?X_17$0)))) :named P84))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_17$0)) (not (in$0 curr_3$0 sk_?X_17$0)))) :named P85))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_17$0)) (not (in$0 curr_3$0 sk_?X_17$0)))) :named P86))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_17$0)) (not (in$0 curr_3$0 sk_?X_17$0)))) :named P87))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_17$0))
        (not (in$0 prv_2$0 sk_?X_17$0)))) :named P88))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_17$0)) (not (in$0 prv_2$0 sk_?X_17$0)))) :named P89))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_17$0)) (not (in$0 prv_2$0 sk_?X_17$0)))) :named P90))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_17$0)) (not (in$0 prv_2$0 sk_?X_17$0)))) :named P91))

(assert (! (or (not Axiom_8$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_17$0))
        (not (in$0 prv_2$0 sk_?X_17$0)))) :named P92))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_28$0)) (not (in$0 c_1$0 sk_?X_28$0)))) :named P93))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_28$0)) (not (in$0 c_1$0 sk_?X_28$0)))) :named P94))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_28$0)) (not (in$0 c_1$0 sk_?X_28$0)))) :named P95))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_28$0)) (not (in$0 c_1$0 sk_?X_28$0)))) :named P96))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_28$0)) (not (in$0 c_1$0 sk_?X_28$0)))) :named P97))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_28$0)) (not (in$0 curr_3$0 sk_?X_28$0)))) :named P98))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_28$0)) (not (in$0 curr_3$0 sk_?X_28$0)))) :named P99))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_28$0)) (not (in$0 curr_3$0 sk_?X_28$0)))) :named P100))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_28$0)) (not (in$0 curr_3$0 sk_?X_28$0)))) :named P101))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_28$0)) (not (in$0 curr_3$0 sk_?X_28$0)))) :named P102))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_28$0))
        (not (in$0 prv_2$0 sk_?X_28$0)))) :named P103))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_28$0)) (not (in$0 prv_2$0 sk_?X_28$0)))) :named P104))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_28$0)) (not (in$0 prv_2$0 sk_?X_28$0)))) :named P105))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_28$0)) (not (in$0 prv_2$0 sk_?X_28$0)))) :named P106))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_28$0))
        (not (in$0 prv_2$0 sk_?X_28$0)))) :named P107))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P108))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P109))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_22$0 sk_?X_26$0))
                 (or (in$0 x sk_?X_22$0) (in$0 x sk_?X_26$0)))
            (and (not (in$0 x sk_?X_22$0)) (not (in$0 x sk_?X_26$0))
                 (not (in$0 x (union$0 sk_?X_22$0 sk_?X_26$0)))))) :named P110))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_21$0 FP$0))
                 (or (in$0 x sk_?X_21$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_21$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_21$0 FP$0)))))) :named P111))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_20$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_20$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_20$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_20$0)))))) :named P112))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P113))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_17$0 sk_?X_19$0))
                 (or (in$0 x sk_?X_17$0) (in$0 x sk_?X_19$0)))
            (and (not (in$0 x sk_?X_17$0)) (not (in$0 x sk_?X_19$0))
                 (not (in$0 x (union$0 sk_?X_17$0 sk_?X_19$0)))))) :named P114))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P115))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_24$0 sk_?X_22$0))
                 (or (in$0 x sk_?X_24$0) (in$0 x sk_?X_22$0)))
            (and (not (in$0 x sk_?X_24$0)) (not (in$0 x sk_?X_22$0))
                 (not (in$0 x (union$0 sk_?X_24$0 sk_?X_22$0)))))) :named P116))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_24$0) (in$0 x sk_?X_22$0)
                 (in$0 x (intersection$0 sk_?X_24$0 sk_?X_22$0)))
            (and (or (not (in$0 x sk_?X_24$0)) (not (in$0 x sk_?X_22$0)))
                 (not (in$0 x (intersection$0 sk_?X_24$0 sk_?X_22$0)))))) :named P117))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_22$0) (in$0 x sk_?X_26$0)
                 (in$0 x (intersection$0 sk_?X_22$0 sk_?X_26$0)))
            (and (or (not (in$0 x sk_?X_22$0)) (not (in$0 x sk_?X_26$0)))
                 (not (in$0 x (intersection$0 sk_?X_22$0 sk_?X_26$0)))))) :named P118))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_17$0) (in$0 x sk_?X_19$0)
                 (in$0 x (intersection$0 sk_?X_17$0 sk_?X_19$0)))
            (and (or (not (in$0 x sk_?X_17$0)) (not (in$0 x sk_?X_19$0)))
                 (not (in$0 x (intersection$0 sk_?X_17$0 sk_?X_19$0)))))) :named P119))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_21$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_21$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_21$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_21$0)))))) :named P120))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P121))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_21$0))
                 (not (in$0 x sk_?X_21$0)))
            (and (or (in$0 x sk_?X_21$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_21$0)))))) :named P122))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P123))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P124))

(assert (! (= (read$0 next$0 null$0) null$0) :named P125))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P126))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P127))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P128))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_24$0)))
         Axiom_7$0)
    (not
         (dlseg_struct$0 sk_?X_24$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P129))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_22$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_9$0)
    (not
         (dlseg_struct$0 sk_?X_22$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P130))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P131))

(assert (! (= c_1$0 a$0) :named P132))

(assert (! (= curr_2$0 c_1$0) :named P133))

(assert (! (= d_2$0 d_1$0) :named P134))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P135))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P136))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P137))

(assert (! (= emptyset$0 (intersection$0 sk_?X_28$0 sk_?X_26$0)) :named P138))

(assert (! (= sk_?X_25$0 FP$0) :named P139))

(assert (! (= sk_?X_27$0 (setenum$0 elt$0)) :named P140))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P141))

(assert (! (= emptyset$0 emptyset$0) :named P142))

(assert (! (= sk_?X_17$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)) :named P143))

(assert (! (= sk_?X_19$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)) :named P144))

(assert (! (= sk_?X_20$0 (union$0 sk_?X_18$0 sk_?X_19$0)) :named P145))

(assert (! (dlseg_struct$0 sk_?X_19$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0) :named P146))

(assert (! (= emptyset$0 emptyset$0) :named P147))

(assert (! (= sk_?X_21$0 (union$0 sk_?X_23$0 sk_?X_22$0)) :named P148))

(assert (! (= sk_?X_22$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P149))

(assert (! (= sk_?X_24$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P150))

(assert (! (dlseg_struct$0 sk_?X_22$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0) :named P151))

(assert (! (not (= curr_2$0 null$0)) :named P152))

(assert (! (not (in$0 null$0 Alloc$0)) :named P153))

(assert (! (not (in$0 elt$0 FP_2$0)) :named P154))

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
                          prv_2$0)))))) :named P155))

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
                          d_1$0)))))) :named P156))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_28$0)))
         Axiom_6$0)
    (not (dlseg_struct$0 sk_?X_28$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P157))

(assert (! (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_17$0)))
         Axiom_8$0)
    (not
         (dlseg_struct$0 sk_?X_17$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))) :named P158))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_19$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_10$0)
    (not
         (dlseg_struct$0 sk_?X_19$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))) :named P159))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P160))

(assert (! (= c_2$0 c_1$0) :named P161))

(assert (! (= d_1$0 b$0) :named P162))

(assert (! (= prv_2$0 null$0) :named P163))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P164))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P165))

(assert (! (= emptyset$0 emptyset$0) :named P166))

(assert (! (= sk_?X_25$0 (union$0 sk_?X_28$0 sk_?X_26$0)) :named P167))

(assert (! (= sk_?X_26$0 sk_?X_27$0) :named P168))

(assert (! (= sk_?X_28$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P169))

(assert (! (dlseg_struct$0 sk_?X_28$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P170))

(assert (! (= emptyset$0 (intersection$0 sk_?X_18$0 sk_?X_19$0)) :named P171))

(assert (! (= sk_?X_18$0 sk_?X_17$0) :named P172))

(assert (! (= sk_?X_20$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P173))

(assert (! (dlseg_struct$0 sk_?X_17$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0) :named P174))

(assert (! (not (= curr_3$0 null$0)) :named P175))

(assert (! (= emptyset$0 (intersection$0 sk_?X_23$0 sk_?X_22$0)) :named P176))

(assert (! (= sk_?X_21$0 FP_1$0) :named P177))

(assert (! (= sk_?X_23$0 sk_?X_24$0) :named P178))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P179))

(assert (! (dlseg_struct$0 sk_?X_24$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0) :named P180))

(assert (! (not (= a$0 null$0)) :named P181))

(assert (! (not (in$0 null$0 Alloc$0)) :named P182))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P183))

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
                          prv_3$0)))))) :named P184))

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
                          d_2$0)))))) :named P185))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P186))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P187))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P188))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P189))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P190))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P191))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P192))

(check-sat)

(get-interpolants (and P147 P57 P39 P148 P184 P55 P119 P103 P52 P56 P181 P26 P178 P116 P10 P81 P67 P121 P140 P32 P94 P104 P130 P171 P175 P35 P139 P87 P82 P165 P33 P128 P170 P24 P58 P155 P64 P65 P109 P191 P188 P161 P127 P96 P143 P29 P34 P85 P162 P99 P98 P114 P15 P111 P146 P17 P131 P126 P145 P44 P113 P118 P159 P108 P46 P1 P49 P179 P182 P189 P70 P183 P149 P4 P164 P75 P8 P18 P9 P110 P129 P89 P166 P77 P74 P40 P16 P14 P152 P190 P105 P123 P62 P12 P48 P120 P122) (and P101 P43 P135 P20 P83 P68 P28 P45 P42 P6 P97 P59 P158 P180 P19 P72 P38 P88 P7 P95 P86 P167 P169 P134 P192 P25 P112 P138 P157 P153 P69 P0 P71 P142 P133 P22 P91 P5 P30 P102 P144 P79 P13 P156 P2 P63 P27 P137 P117 P92 P80 P21 P106 P73 P168 P31 P60 P107 P47 P163 P61 P53 P115 P78 P66 P160 P174 P76 P3 P132 P23 P11 P177 P176 P172 P37 P51 P125 P154 P141 P124 P173 P187 P186 P41 P90 P150 P100 P54 P185 P93 P50 P36 P136 P84 P151))

(exit)