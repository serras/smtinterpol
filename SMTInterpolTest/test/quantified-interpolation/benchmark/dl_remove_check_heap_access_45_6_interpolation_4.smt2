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
  tests/spl/dl/dl_remove.spl:45:6-22:Possible heap access through null or dangling reference
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
(declare-fun Axiom_23$0 () Bool)
(declare-fun Axiom_24$0 () Bool)
(declare-fun Axiom_25$0 () Bool)
(declare-fun Axiom_26$0 () Bool)
(declare-fun Axiom_27$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun c_1$0 () Loc)
(declare-fun c_2$0 () Loc)
(declare-fun c_3$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun d_1$0 () Loc)
(declare-fun d_2$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_37$0 () SetLoc)
(declare-fun sk_?X_38$0 () SetLoc)
(declare-fun sk_?X_39$0 () SetLoc)
(declare-fun sk_?X_40$0 () SetLoc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun sk_?X_42$0 () SetLoc)
(declare-fun sk_?X_43$0 () SetLoc)
(declare-fun sk_?X_44$0 () SetLoc)
(declare-fun sk_?X_45$0 () SetLoc)
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
        (or (not (Btwn$0 next_1$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next_1$0 prv_2$0 (read$0 next_1$0 prv_2$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_1$0) d_1$0))
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_3$0) prv_3$0))
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (= prv_3$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next_1$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P9))

(assert (! (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) (read$0 next$0 d_1$0)) :named P10))

(assert (! (Btwn$0 next$0 prv_3$0 (read$0 next$0 prv_3$0) (read$0 next$0 prv_3$0)) :named P11))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P12))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P13))

(assert (! (Btwn$0 next_1$0 prv_2$0 (read$0 next_1$0 prv_2$0) (read$0 next_1$0 prv_2$0)) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_41$0 c_1$0) ?y)
            (not (Btwn$0 next$0 c_1$0 ?y ?y)) (not (in$0 ?y sk_?X_41$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_41$0 d_1$0) ?y)
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (not (in$0 ?y sk_?X_41$0)))) :named P16))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_41$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_41$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_41$0 prv_2$0) ?y)
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (not (in$0 ?y sk_?X_41$0)))) :named P18))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_41$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y sk_?X_41$0)))) :named P19))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 tmp_2$0 (ep$0 next$0 sk_?X_41$0 tmp_2$0) ?y)
            (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (not (in$0 ?y sk_?X_41$0)))) :named P20))

(assert (! (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_41$0 c_1$0)
  (ep$0 next$0 sk_?X_41$0 c_1$0)) :named P21))

(assert (! (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_41$0 d_1$0)
  (ep$0 next$0 sk_?X_41$0 d_1$0)) :named P22))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_41$0 curr_3$0)
  (ep$0 next$0 sk_?X_41$0 curr_3$0)) :named P23))

(assert (! (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_41$0 prv_2$0)
  (ep$0 next$0 sk_?X_41$0 prv_2$0)) :named P24))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_41$0 prv_3$0)
  (ep$0 next$0 sk_?X_41$0 prv_3$0)) :named P25))

(assert (! (Btwn$0 next$0 tmp_2$0 (ep$0 next$0 sk_?X_41$0 tmp_2$0)
  (ep$0 next$0 sk_?X_41$0 tmp_2$0)) :named P26))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_42$0)) (not (in$0 c_1$0 sk_?X_42$0)))) :named P27))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_42$0)) (not (in$0 c_1$0 sk_?X_42$0)))) :named P28))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_42$0)) (not (in$0 c_1$0 sk_?X_42$0)))) :named P29))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_42$0)) (not (in$0 c_1$0 sk_?X_42$0)))) :named P30))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_42$0)) (not (in$0 curr_3$0 sk_?X_42$0)))) :named P31))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_42$0)) (not (in$0 curr_3$0 sk_?X_42$0)))) :named P32))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_42$0)) (not (in$0 curr_3$0 sk_?X_42$0)))) :named P33))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_42$0)) (not (in$0 curr_3$0 sk_?X_42$0)))) :named P34))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_42$0))
        (not (in$0 prv_2$0 sk_?X_42$0)))) :named P35))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_42$0)) (not (in$0 prv_2$0 sk_?X_42$0)))) :named P36))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_42$0)) (not (in$0 prv_2$0 sk_?X_42$0)))) :named P37))

(assert (! (or (not Axiom_26$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_42$0)) (not (in$0 prv_2$0 sk_?X_42$0)))) :named P38))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_44$0)) (not (in$0 c_1$0 sk_?X_44$0)))) :named P39))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_44$0)) (not (in$0 c_1$0 sk_?X_44$0)))) :named P40))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_44$0)) (not (in$0 c_1$0 sk_?X_44$0)))) :named P41))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_44$0)) (not (in$0 c_1$0 sk_?X_44$0)))) :named P42))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_44$0)) (not (in$0 curr_3$0 sk_?X_44$0)))) :named P43))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_44$0)) (not (in$0 curr_3$0 sk_?X_44$0)))) :named P44))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_44$0)) (not (in$0 curr_3$0 sk_?X_44$0)))) :named P45))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_44$0)) (not (in$0 curr_3$0 sk_?X_44$0)))) :named P46))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_44$0))
        (not (in$0 prv_2$0 sk_?X_44$0)))) :named P47))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_44$0)) (not (in$0 prv_2$0 sk_?X_44$0)))) :named P48))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_44$0)) (not (in$0 prv_2$0 sk_?X_44$0)))) :named P49))

(assert (! (or (not Axiom_24$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_44$0)) (not (in$0 prv_2$0 sk_?X_44$0)))) :named P50))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_41$0 c_1$0) sk_?X_41$0)
    (= c_1$0 (ep$0 next$0 sk_?X_41$0 c_1$0))) :named P51))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_41$0 d_1$0) sk_?X_41$0)
    (= d_1$0 (ep$0 next$0 sk_?X_41$0 d_1$0))) :named P52))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_41$0 curr_3$0) sk_?X_41$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_41$0 curr_3$0))) :named P53))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_41$0 prv_2$0) sk_?X_41$0)
    (= prv_2$0 (ep$0 next$0 sk_?X_41$0 prv_2$0))) :named P54))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_41$0 prv_3$0) sk_?X_41$0)
    (= prv_3$0 (ep$0 next$0 sk_?X_41$0 prv_3$0))) :named P55))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_41$0 tmp_2$0) sk_?X_41$0)
    (= tmp_2$0 (ep$0 next$0 sk_?X_41$0 tmp_2$0))) :named P56))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_39$0)) (not (in$0 c_1$0 sk_?X_39$0)))) :named P57))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_39$0)) (not (in$0 c_1$0 sk_?X_39$0)))) :named P58))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_39$0)) (not (in$0 c_1$0 sk_?X_39$0)))) :named P59))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_39$0)) (not (in$0 c_1$0 sk_?X_39$0)))) :named P60))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_39$0)) (not (in$0 curr_3$0 sk_?X_39$0)))) :named P61))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_39$0)) (not (in$0 curr_3$0 sk_?X_39$0)))) :named P62))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_39$0)) (not (in$0 curr_3$0 sk_?X_39$0)))) :named P63))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_39$0)) (not (in$0 curr_3$0 sk_?X_39$0)))) :named P64))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_39$0))
        (not (in$0 prv_2$0 sk_?X_39$0)))) :named P65))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_39$0)) (not (in$0 prv_2$0 sk_?X_39$0)))) :named P66))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_39$0)) (not (in$0 prv_2$0 sk_?X_39$0)))) :named P67))

(assert (! (or (not Axiom_27$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_39$0)) (not (in$0 prv_2$0 sk_?X_39$0)))) :named P68))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_37$0)) (not (in$0 c_1$0 sk_?X_37$0)))) :named P69))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_37$0)) (not (in$0 c_1$0 sk_?X_37$0)))) :named P70))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_37$0)) (not (in$0 c_1$0 sk_?X_37$0)))) :named P71))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_37$0)) (not (in$0 c_1$0 sk_?X_37$0)))) :named P72))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_37$0)) (not (in$0 curr_3$0 sk_?X_37$0)))) :named P73))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_37$0)) (not (in$0 curr_3$0 sk_?X_37$0)))) :named P74))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_37$0)) (not (in$0 curr_3$0 sk_?X_37$0)))) :named P75))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_37$0)) (not (in$0 curr_3$0 sk_?X_37$0)))) :named P76))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_37$0))
        (not (in$0 prv_2$0 sk_?X_37$0)))) :named P77))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_37$0)) (not (in$0 prv_2$0 sk_?X_37$0)))) :named P78))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_37$0)) (not (in$0 prv_2$0 sk_?X_37$0)))) :named P79))

(assert (! (or (not Axiom_25$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_37$0)) (not (in$0 prv_2$0 sk_?X_37$0)))) :named P80))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_45$0)) (not (in$0 c_1$0 sk_?X_45$0)))) :named P81))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_45$0)) (not (in$0 c_1$0 sk_?X_45$0)))) :named P82))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_45$0)) (not (in$0 c_1$0 sk_?X_45$0)))) :named P83))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_45$0)) (not (in$0 c_1$0 sk_?X_45$0)))) :named P84))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_45$0)) (not (in$0 curr_3$0 sk_?X_45$0)))) :named P85))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_45$0)) (not (in$0 curr_3$0 sk_?X_45$0)))) :named P86))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_45$0)) (not (in$0 curr_3$0 sk_?X_45$0)))) :named P87))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_45$0)) (not (in$0 curr_3$0 sk_?X_45$0)))) :named P88))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_45$0))
        (not (in$0 prv_2$0 sk_?X_45$0)))) :named P89))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_45$0)) (not (in$0 prv_2$0 sk_?X_45$0)))) :named P90))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_45$0)) (not (in$0 prv_2$0 sk_?X_45$0)))) :named P91))

(assert (! (or (not Axiom_23$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_45$0)) (not (in$0 prv_2$0 sk_?X_45$0)))) :named P92))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P93))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P94))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_41$0 FP$0))
                 (or (in$0 x sk_?X_41$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_41$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_41$0 FP$0)))))) :named P95))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_40$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_40$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_40$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_40$0)))))) :named P96))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P97))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_37$0 sk_?X_39$0))
                 (or (in$0 x sk_?X_37$0) (in$0 x sk_?X_39$0)))
            (and (not (in$0 x sk_?X_37$0)) (not (in$0 x sk_?X_39$0))
                 (not (in$0 x (union$0 sk_?X_37$0 sk_?X_39$0)))))) :named P98))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P99))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_43$0 FP$0))
                 (or (in$0 x sk_?X_43$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_43$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_43$0 FP$0)))))) :named P100))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_43$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_43$0 FP$0)))
            (and (or (not (in$0 x sk_?X_43$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_43$0 FP$0)))))) :named P101))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_37$0) (in$0 x sk_?X_39$0)
                 (in$0 x (intersection$0 sk_?X_37$0 sk_?X_39$0)))
            (and (or (not (in$0 x sk_?X_37$0)) (not (in$0 x sk_?X_39$0)))
                 (not (in$0 x (intersection$0 sk_?X_37$0 sk_?X_39$0)))))) :named P102))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_41$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_41$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_41$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_41$0)))))) :named P103))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P104))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_41$0))
                 (not (in$0 x sk_?X_41$0)))
            (and (or (in$0 x sk_?X_41$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_41$0)))))) :named P105))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P106))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P107))

(assert (! (= (read$0 (write$0 next$0 prv_3$0 tmp_2$0) prv_3$0) tmp_2$0) :named P108))

(assert (! (or (= d_1$0 prv_3$0)
    (= (read$0 next$0 d_1$0) (read$0 (write$0 next$0 prv_3$0 tmp_2$0) d_1$0))) :named P109))

(assert (! (or (= prv_3$0 prv_3$0)
    (= (read$0 next$0 prv_3$0)
      (read$0 (write$0 next$0 prv_3$0 tmp_2$0) prv_3$0))) :named P110))

(assert (! (or (= prv_2$0 prv_3$0)
    (= (read$0 next$0 prv_2$0)
      (read$0 (write$0 next$0 prv_3$0 tmp_2$0) prv_2$0))) :named P111))

(assert (! (or (= curr_3$0 prv_3$0)
    (= (read$0 next$0 curr_3$0)
      (read$0 (write$0 next$0 prv_3$0 tmp_2$0) curr_3$0))) :named P112))

(assert (! (= (read$0 next$0 null$0) null$0) :named P113))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P114))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P115))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P116))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P117))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_44$0)))
         Axiom_24$0)
    (not
         (dlseg_struct$0 sk_?X_44$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P118))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_42$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_26$0)
    (not
         (dlseg_struct$0 sk_?X_42$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P119))

(assert (! (or
    (and (= c_2$0 c_3$0) (= c_3$0 tmp_2$0) (= next_1$0 next$0)
         (= prv_3$0 null$0))
    (and (= next_1$0 (write$0 next$0 prv_3$0 (read$0 next$0 curr_3$0)))
         (not (= prv_3$0 null$0)))) :named P120))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P121))

(assert (! (= c_2$0 c_1$0) :named P122))

(assert (! (= d_1$0 b$0) :named P123))

(assert (! (= prv_2$0 null$0) :named P124))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P125))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P126))

(assert (! (= emptyset$0 emptyset$0) :named P127))

(assert (! (= sk_?X_37$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)) :named P128))

(assert (! (= sk_?X_39$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)) :named P129))

(assert (! (= sk_?X_40$0 (union$0 sk_?X_38$0 sk_?X_39$0)) :named P130))

(assert (! (dlseg_struct$0 sk_?X_39$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0) :named P131))

(assert (! (= emptyset$0 emptyset$0) :named P132))

(assert (! (= sk_?X_41$0 (union$0 sk_?X_43$0 sk_?X_42$0)) :named P133))

(assert (! (= sk_?X_42$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P134))

(assert (! (= sk_?X_44$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P135))

(assert (! (dlseg_struct$0 sk_?X_42$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0) :named P136))

(assert (! (not (= curr_2$0 null$0)) :named P137))

(assert (! (= sk_?X_45$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P138))

(assert (! (dlseg_struct$0 sk_?X_45$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P139))

(assert (! (not (= a$0 b$0)) :named P140))

(assert (! (not (in$0 null$0 Alloc$0)) :named P141))

(assert (! (not (in$0 tmp_2$0 FP_2$0)) :named P142))

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
                          prv_2$0)))))) :named P143))

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
                          d_1$0)))))) :named P144))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_45$0)))
         Axiom_23$0)
    (not (dlseg_struct$0 sk_?X_45$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P145))

(assert (! (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_37$0)))
         Axiom_25$0)
    (not
         (dlseg_struct$0 sk_?X_37$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))) :named P146))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_39$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_27$0)
    (not
         (dlseg_struct$0 sk_?X_39$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))) :named P147))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P148))

(assert (! (= c_1$0 a$0) :named P149))

(assert (! (= curr_2$0 c_1$0) :named P150))

(assert (! (= d_2$0 d_1$0) :named P151))

(assert (! (= tmp_2$0 (read$0 next$0 curr_3$0)) :named P152))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P153))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P154))

(assert (! (= emptyset$0 (intersection$0 sk_?X_38$0 sk_?X_39$0)) :named P155))

(assert (! (= sk_?X_38$0 sk_?X_37$0) :named P156))

(assert (! (= sk_?X_40$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P157))

(assert (! (dlseg_struct$0 sk_?X_37$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0) :named P158))

(assert (! (not (= curr_3$0 null$0)) :named P159))

(assert (! (= emptyset$0 (intersection$0 sk_?X_43$0 sk_?X_42$0)) :named P160))

(assert (! (= sk_?X_41$0 FP_1$0) :named P161))

(assert (! (= sk_?X_43$0 sk_?X_44$0) :named P162))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P163))

(assert (! (dlseg_struct$0 sk_?X_44$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0) :named P164))

(assert (! (= sk_?X_45$0 FP$0) :named P165))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P166))

(assert (! (not (= a$0 null$0)) :named P167))

(assert (! (not (= tmp_2$0 null$0)) :named P168))

(assert (! (not (in$0 null$0 Alloc$0)) :named P169))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P170))

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
                          prv_3$0)))))) :named P171))

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
                          d_2$0)))))) :named P172))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or
                 (Btwn$0 (write$0 next$0 prv_3$0 (read$0 next$0 curr_3$0)) ?z
                   ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v prv_3$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z prv_3$0
                                               prv_3$0)))))
                          (and (not (= prv_3$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u prv_3$0)
                               (or
                                   (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v
                                     prv_3$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 curr_3$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 curr_3$0)
                                               prv_3$0 prv_3$0)))))
                          (and (not (= prv_3$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?u ?v)
                               (or
                                   (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v
                                     prv_3$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 curr_3$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 curr_3$0)
                                               prv_3$0 prv_3$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v prv_3$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z prv_3$0 prv_3$0)))))
                 (and (not (= prv_3$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u prv_3$0)
                      (or (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v prv_3$0)
                          (and (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v ?v)
                               (not
                                    (Btwn$0 next$0 (read$0 next$0 curr_3$0)
                                      prv_3$0 prv_3$0)))))
                 (and (not (= prv_3$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_3$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_3$0 prv_3$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?u ?v)
                      (or (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v prv_3$0)
                          (and (Btwn$0 next$0 (read$0 next$0 curr_3$0) ?v ?v)
                               (not
                                    (Btwn$0 next$0 (read$0 next$0 curr_3$0)
                                      prv_3$0 prv_3$0)))))
                 (not
                      (Btwn$0
                        (write$0 next$0 prv_3$0 (read$0 next$0 curr_3$0)) ?z
                        ?u ?v))))) :named P173))

(assert (! (forall ((?x Loc)) (Btwn$0 next_1$0 ?x ?x ?x)) :named P174))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P175))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_1$0 ?x ?y ?x)) (= ?x ?y))) :named P176))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P177))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?x ?z ?z))
            (Btwn$0 next_1$0 ?x ?y ?z) (Btwn$0 next_1$0 ?x ?z ?y))) :named P178))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P179))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?y) (Btwn$0 next_1$0 ?y ?z ?z)))) :named P180))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P181))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?y ?z ?z))
            (Btwn$0 next_1$0 ?x ?z ?z))) :named P182))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P183))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?y ?u ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?u) (Btwn$0 next_1$0 ?x ?u ?z)))) :named P184))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P185))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?x ?u ?y))
            (and (Btwn$0 next_1$0 ?x ?u ?z) (Btwn$0 next_1$0 ?u ?y ?z)))) :named P186))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P187))

(check-sat)

(get-interpolants (and P32 P60 P36 P136 P95 P77 P50 P12 P19 P5 P160 P171 P61 P75 P82 P43 P129 P106 P121 P97 P3 P85 P183 P124 P170 P69 P89 P70 P114 P63 P21 P101 P116 P9 P127 P40 P71 P108 P154 P150 P90 P34 P39 P135 P113 P176 P178 P142 P132 P51 P8 P140 P88 P147 P103 P173 P186 P47 P111 P119 P53 P117 P179 P184 P91 P93 P7 P104 P118 P167 P181 P155 P162 P59 P123 P57 P149 P58 P52 P187 P134 P26 P141 P172 P169 P33 P83 P182 P15 P177 P110 P145 P35 P11) (and P122 P41 P66 P18 P175 P143 P92 P165 P67 P6 P109 P1 P146 P138 P28 P4 P98 P96 P130 P164 P79 P37 P17 P139 P112 P27 P115 P153 P168 P22 P20 P151 P152 P105 P125 P180 P107 P148 P128 P0 P78 P46 P166 P65 P54 P100 P44 P185 P120 P157 P45 P86 P64 P102 P30 P133 P62 P159 P94 P25 P81 P158 P2 P174 P137 P74 P76 P31 P80 P144 P48 P16 P13 P29 P163 P156 P126 P87 P68 P131 P38 P42 P84 P10 P73 P14 P161 P99 P55 P72 P23 P56 P24 P49))

(exit)