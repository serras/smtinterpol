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
  tests/spl/dl/dl_insert.spl:32:4-21:Possible heap access through null or dangling reference
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
(declare-fun Axiom_11$0 () Bool)
(declare-fun Axiom_12$0 () Bool)
(declare-fun Axiom_13$0 () Bool)
(declare-fun Axiom_14$0 () Bool)
(declare-fun Axiom_15$0 () Bool)
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
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?X_33$0 () SetLoc)
(declare-fun sk_?X_34$0 () SetLoc)
(declare-fun sk_?X_35$0 () SetLoc)
(declare-fun sk_?X_36$0 () SetLoc)
(declare-fun sk_?X_37$0 () SetLoc)
(declare-fun sk_?X_38$0 () SetLoc)
(declare-fun sk_?X_39$0 () SetLoc)
(declare-fun sk_?X_40$0 () SetLoc)

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

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_34$0)) (not (in$0 c_1$0 sk_?X_34$0)))) :named P15))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_34$0)) (not (in$0 c_1$0 sk_?X_34$0)))) :named P16))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_34$0)) (not (in$0 c_1$0 sk_?X_34$0)))) :named P17))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_34$0)) (not (in$0 c_1$0 sk_?X_34$0)))) :named P18))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_34$0)) (not (in$0 c_1$0 sk_?X_34$0)))) :named P19))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_34$0)) (not (in$0 curr_3$0 sk_?X_34$0)))) :named P20))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_34$0)) (not (in$0 curr_3$0 sk_?X_34$0)))) :named P21))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_34$0)) (not (in$0 curr_3$0 sk_?X_34$0)))) :named P22))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_34$0)) (not (in$0 curr_3$0 sk_?X_34$0)))) :named P23))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_34$0)) (not (in$0 curr_3$0 sk_?X_34$0)))) :named P24))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_34$0))
        (not (in$0 prv_2$0 sk_?X_34$0)))) :named P25))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_34$0)) (not (in$0 prv_2$0 sk_?X_34$0)))) :named P26))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_34$0)) (not (in$0 prv_2$0 sk_?X_34$0)))) :named P27))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_34$0)) (not (in$0 prv_2$0 sk_?X_34$0)))) :named P28))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_34$0))
        (not (in$0 prv_2$0 sk_?X_34$0)))) :named P29))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_36$0)) (not (in$0 c_1$0 sk_?X_36$0)))) :named P30))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_36$0)) (not (in$0 c_1$0 sk_?X_36$0)))) :named P31))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_36$0)) (not (in$0 c_1$0 sk_?X_36$0)))) :named P32))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_36$0)) (not (in$0 c_1$0 sk_?X_36$0)))) :named P33))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_36$0)) (not (in$0 c_1$0 sk_?X_36$0)))) :named P34))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_36$0)) (not (in$0 curr_3$0 sk_?X_36$0)))) :named P35))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_36$0)) (not (in$0 curr_3$0 sk_?X_36$0)))) :named P36))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_36$0)) (not (in$0 curr_3$0 sk_?X_36$0)))) :named P37))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_36$0)) (not (in$0 curr_3$0 sk_?X_36$0)))) :named P38))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_36$0)) (not (in$0 curr_3$0 sk_?X_36$0)))) :named P39))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_36$0))
        (not (in$0 prv_2$0 sk_?X_36$0)))) :named P40))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_36$0)) (not (in$0 prv_2$0 sk_?X_36$0)))) :named P41))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_36$0)) (not (in$0 prv_2$0 sk_?X_36$0)))) :named P42))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_36$0)) (not (in$0 prv_2$0 sk_?X_36$0)))) :named P43))

(assert (! (or (not Axiom_12$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_36$0))
        (not (in$0 prv_2$0 sk_?X_36$0)))) :named P44))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_33$0 c_1$0) ?y)
            (not (Btwn$0 next$0 c_1$0 ?y ?y)) (not (in$0 ?y sk_?X_33$0)))) :named P45))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_33$0 d_1$0) ?y)
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (not (in$0 ?y sk_?X_33$0)))) :named P46))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_33$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_33$0)))) :named P47))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_33$0 prv_2$0) ?y)
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (not (in$0 ?y sk_?X_33$0)))) :named P48))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_33$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y sk_?X_33$0)))) :named P49))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_33$0 c_1$0) sk_?X_33$0)
    (= c_1$0 (ep$0 next$0 sk_?X_33$0 c_1$0))) :named P50))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_33$0 d_1$0) sk_?X_33$0)
    (= d_1$0 (ep$0 next$0 sk_?X_33$0 d_1$0))) :named P51))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_33$0 curr_3$0) sk_?X_33$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_33$0 curr_3$0))) :named P52))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_33$0 prv_2$0) sk_?X_33$0)
    (= prv_2$0 (ep$0 next$0 sk_?X_33$0 prv_2$0))) :named P53))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_33$0 prv_3$0) sk_?X_33$0)
    (= prv_3$0 (ep$0 next$0 sk_?X_33$0 prv_3$0))) :named P54))

(assert (! (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_33$0 c_1$0)
  (ep$0 next$0 sk_?X_33$0 c_1$0)) :named P55))

(assert (! (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_33$0 d_1$0)
  (ep$0 next$0 sk_?X_33$0 d_1$0)) :named P56))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_33$0 curr_3$0)
  (ep$0 next$0 sk_?X_33$0 curr_3$0)) :named P57))

(assert (! (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_33$0 prv_2$0)
  (ep$0 next$0 sk_?X_33$0 prv_2$0)) :named P58))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_33$0 prv_3$0)
  (ep$0 next$0 sk_?X_33$0 prv_3$0)) :named P59))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_31$0)) (not (in$0 c_1$0 sk_?X_31$0)))) :named P60))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_31$0)) (not (in$0 c_1$0 sk_?X_31$0)))) :named P61))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_31$0)) (not (in$0 c_1$0 sk_?X_31$0)))) :named P62))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_31$0)) (not (in$0 c_1$0 sk_?X_31$0)))) :named P63))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_31$0)) (not (in$0 c_1$0 sk_?X_31$0)))) :named P64))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_31$0)) (not (in$0 curr_3$0 sk_?X_31$0)))) :named P65))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_31$0)) (not (in$0 curr_3$0 sk_?X_31$0)))) :named P66))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_31$0)) (not (in$0 curr_3$0 sk_?X_31$0)))) :named P67))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_31$0)) (not (in$0 curr_3$0 sk_?X_31$0)))) :named P68))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_31$0)) (not (in$0 curr_3$0 sk_?X_31$0)))) :named P69))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_31$0))
        (not (in$0 prv_2$0 sk_?X_31$0)))) :named P70))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_31$0)) (not (in$0 prv_2$0 sk_?X_31$0)))) :named P71))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_31$0)) (not (in$0 prv_2$0 sk_?X_31$0)))) :named P72))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_31$0)) (not (in$0 prv_2$0 sk_?X_31$0)))) :named P73))

(assert (! (or (not Axiom_15$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_31$0))
        (not (in$0 prv_2$0 sk_?X_31$0)))) :named P74))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_29$0)) (not (in$0 c_1$0 sk_?X_29$0)))) :named P75))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_29$0)) (not (in$0 c_1$0 sk_?X_29$0)))) :named P76))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_29$0)) (not (in$0 c_1$0 sk_?X_29$0)))) :named P77))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_29$0)) (not (in$0 c_1$0 sk_?X_29$0)))) :named P78))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_29$0)) (not (in$0 c_1$0 sk_?X_29$0)))) :named P79))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_29$0)) (not (in$0 curr_3$0 sk_?X_29$0)))) :named P80))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_29$0)) (not (in$0 curr_3$0 sk_?X_29$0)))) :named P81))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_29$0)) (not (in$0 curr_3$0 sk_?X_29$0)))) :named P82))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_29$0)) (not (in$0 curr_3$0 sk_?X_29$0)))) :named P83))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_29$0)) (not (in$0 curr_3$0 sk_?X_29$0)))) :named P84))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_29$0))
        (not (in$0 prv_2$0 sk_?X_29$0)))) :named P85))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_29$0)) (not (in$0 prv_2$0 sk_?X_29$0)))) :named P86))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_29$0)) (not (in$0 prv_2$0 sk_?X_29$0)))) :named P87))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_29$0)) (not (in$0 prv_2$0 sk_?X_29$0)))) :named P88))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_29$0))
        (not (in$0 prv_2$0 sk_?X_29$0)))) :named P89))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_40$0)) (not (in$0 c_1$0 sk_?X_40$0)))) :named P90))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_40$0)) (not (in$0 c_1$0 sk_?X_40$0)))) :named P91))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_40$0)) (not (in$0 c_1$0 sk_?X_40$0)))) :named P92))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_40$0)) (not (in$0 c_1$0 sk_?X_40$0)))) :named P93))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_40$0)) (not (in$0 c_1$0 sk_?X_40$0)))) :named P94))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_40$0)) (not (in$0 curr_3$0 sk_?X_40$0)))) :named P95))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_40$0)) (not (in$0 curr_3$0 sk_?X_40$0)))) :named P96))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_40$0)) (not (in$0 curr_3$0 sk_?X_40$0)))) :named P97))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_40$0)) (not (in$0 curr_3$0 sk_?X_40$0)))) :named P98))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_40$0)) (not (in$0 curr_3$0 sk_?X_40$0)))) :named P99))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_40$0))
        (not (in$0 prv_2$0 sk_?X_40$0)))) :named P100))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_40$0)) (not (in$0 prv_2$0 sk_?X_40$0)))) :named P101))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_40$0)) (not (in$0 prv_2$0 sk_?X_40$0)))) :named P102))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_40$0)) (not (in$0 prv_2$0 sk_?X_40$0)))) :named P103))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_40$0))
        (not (in$0 prv_2$0 sk_?X_40$0)))) :named P104))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P105))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P106))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_40$0 sk_?X_39$0))
                 (or (in$0 x sk_?X_40$0) (in$0 x sk_?X_39$0)))
            (and (not (in$0 x sk_?X_40$0)) (not (in$0 x sk_?X_39$0))
                 (not (in$0 x (union$0 sk_?X_40$0 sk_?X_39$0)))))) :named P107))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_33$0 FP$0))
                 (or (in$0 x sk_?X_33$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_33$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_33$0 FP$0)))))) :named P108))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_32$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_32$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_32$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_32$0)))))) :named P109))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P110))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_29$0 sk_?X_31$0))
                 (or (in$0 x sk_?X_29$0) (in$0 x sk_?X_31$0)))
            (and (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_31$0))
                 (not (in$0 x (union$0 sk_?X_29$0 sk_?X_31$0)))))) :named P111))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P112))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_36$0 sk_?X_40$0))
                 (or (in$0 x sk_?X_36$0) (in$0 x sk_?X_40$0)))
            (and (not (in$0 x sk_?X_36$0)) (not (in$0 x sk_?X_40$0))
                 (not (in$0 x (union$0 sk_?X_36$0 sk_?X_40$0)))))) :named P113))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_40$0) (in$0 x sk_?X_39$0)
                 (in$0 x (intersection$0 sk_?X_40$0 sk_?X_39$0)))
            (and (or (not (in$0 x sk_?X_40$0)) (not (in$0 x sk_?X_39$0)))
                 (not (in$0 x (intersection$0 sk_?X_40$0 sk_?X_39$0)))))) :named P114))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_36$0) (in$0 x sk_?X_40$0)
                 (in$0 x (intersection$0 sk_?X_36$0 sk_?X_40$0)))
            (and (or (not (in$0 x sk_?X_36$0)) (not (in$0 x sk_?X_40$0)))
                 (not (in$0 x (intersection$0 sk_?X_36$0 sk_?X_40$0)))))) :named P115))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_29$0) (in$0 x sk_?X_31$0)
                 (in$0 x (intersection$0 sk_?X_29$0 sk_?X_31$0)))
            (and (or (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_31$0)))
                 (not (in$0 x (intersection$0 sk_?X_29$0 sk_?X_31$0)))))) :named P116))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_33$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_33$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_33$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_33$0)))))) :named P117))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P118))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_33$0))
                 (not (in$0 x sk_?X_33$0)))
            (and (or (in$0 x sk_?X_33$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_33$0)))))) :named P119))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P120))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P121))

(assert (! (= (read$0 (write$0 next$0 elt$0 curr_3$0) elt$0) curr_3$0) :named P122))

(assert (! (or (= d_1$0 elt$0)
    (= (read$0 next$0 d_1$0) (read$0 (write$0 next$0 elt$0 curr_3$0) d_1$0))) :named P123))

(assert (! (or (= curr_3$0 elt$0)
    (= (read$0 next$0 curr_3$0)
      (read$0 (write$0 next$0 elt$0 curr_3$0) curr_3$0))) :named P124))

(assert (! (or (= prv_3$0 elt$0)
    (= (read$0 next$0 prv_3$0)
      (read$0 (write$0 next$0 elt$0 curr_3$0) prv_3$0))) :named P125))

(assert (! (or (= prv_2$0 elt$0)
    (= (read$0 next$0 prv_2$0)
      (read$0 (write$0 next$0 elt$0 curr_3$0) prv_2$0))) :named P126))

(assert (! (or (= elt$0 elt$0)
    (= (read$0 next$0 elt$0) (read$0 (write$0 next$0 elt$0 curr_3$0) elt$0))) :named P127))

(assert (! (= (read$0 next$0 null$0) null$0) :named P128))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P129))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P130))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P131))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P132))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_36$0)))
         Axiom_12$0)
    (not
         (dlseg_struct$0 sk_?X_36$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P133))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_34$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_14$0)
    (not
         (dlseg_struct$0 sk_?X_34$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P134))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P135))

(assert (! (= c_1$0 a$0) :named P136))

(assert (! (= curr_2$0 c_1$0) :named P137))

(assert (! (= d_2$0 d_1$0) :named P138))

(assert (! (= prv_2$0 null$0) :named P139))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P140))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P141))

(assert (! (= emptyset$0 emptyset$0) :named P142))

(assert (! (= sk_?X_37$0 (union$0 sk_?X_40$0 sk_?X_38$0)) :named P143))

(assert (! (= sk_?X_38$0 sk_?X_39$0) :named P144))

(assert (! (= sk_?X_40$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P145))

(assert (! (dlseg_struct$0 sk_?X_40$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P146))

(assert (! (= emptyset$0 (intersection$0 sk_?X_30$0 sk_?X_31$0)) :named P147))

(assert (! (= sk_?X_30$0 sk_?X_29$0) :named P148))

(assert (! (= sk_?X_32$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P149))

(assert (! (dlseg_struct$0 sk_?X_29$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0) :named P150))

(assert (! (not (= curr_3$0 null$0)) :named P151))

(assert (! (= emptyset$0 (intersection$0 sk_?X_35$0 sk_?X_34$0)) :named P152))

(assert (! (= sk_?X_33$0 FP_1$0) :named P153))

(assert (! (= sk_?X_35$0 sk_?X_36$0) :named P154))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P155))

(assert (! (dlseg_struct$0 sk_?X_36$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0) :named P156))

(assert (! (not (= a$0 null$0)) :named P157))

(assert (! (not (in$0 null$0 Alloc$0)) :named P158))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P159))

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
                          prv_3$0)))))) :named P160))

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
                          d_2$0)))))) :named P161))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_40$0)))
         Axiom_11$0)
    (not (dlseg_struct$0 sk_?X_40$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P162))

(assert (! (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_29$0)))
         Axiom_13$0)
    (not
         (dlseg_struct$0 sk_?X_29$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))) :named P163))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_31$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_15$0)
    (not
         (dlseg_struct$0 sk_?X_31$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))) :named P164))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P165))

(assert (! (= c_2$0 c_1$0) :named P166))

(assert (! (= d_1$0 b$0) :named P167))

(assert (! (= next_1$0 (write$0 next$0 elt$0 curr_3$0)) :named P168))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P169))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P170))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P171))

(assert (! (= emptyset$0 (intersection$0 sk_?X_40$0 sk_?X_38$0)) :named P172))

(assert (! (= sk_?X_37$0 FP$0) :named P173))

(assert (! (= sk_?X_39$0 (setenum$0 elt$0)) :named P174))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P175))

(assert (! (= emptyset$0 emptyset$0) :named P176))

(assert (! (= sk_?X_29$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)) :named P177))

(assert (! (= sk_?X_31$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)) :named P178))

(assert (! (= sk_?X_32$0 (union$0 sk_?X_30$0 sk_?X_31$0)) :named P179))

(assert (! (dlseg_struct$0 sk_?X_31$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0) :named P180))

(assert (! (= emptyset$0 emptyset$0) :named P181))

(assert (! (= sk_?X_33$0 (union$0 sk_?X_35$0 sk_?X_34$0)) :named P182))

(assert (! (= sk_?X_34$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P183))

(assert (! (= sk_?X_36$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P184))

(assert (! (dlseg_struct$0 sk_?X_34$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0) :named P185))

(assert (! (not (= curr_2$0 null$0)) :named P186))

(assert (! (not (in$0 null$0 Alloc$0)) :named P187))

(assert (! (not (in$0 curr_3$0 FP_2$0)) :named P188))

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
                          prv_2$0)))))) :named P189))

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
                          d_1$0)))))) :named P190))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 elt$0 curr_3$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v elt$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not (Btwn$0 next$0 ?z elt$0 elt$0)))))
                          (and (not (= elt$0 ?v))
                               (or (Btwn$0 next$0 ?z elt$0 ?v)
                                   (and (Btwn$0 next$0 ?z elt$0 elt$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u elt$0)
                               (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                                   (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 curr_3$0 elt$0
                                               elt$0)))))
                          (and (not (= elt$0 ?v))
                               (or (Btwn$0 next$0 ?z elt$0 ?v)
                                   (and (Btwn$0 next$0 ?z elt$0 elt$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 curr_3$0 ?u ?v)
                               (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                                   (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 curr_3$0 elt$0
                                               elt$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v elt$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z elt$0 elt$0)))))
                 (and (not (= elt$0 ?v))
                      (or (Btwn$0 next$0 ?z elt$0 ?v)
                          (and (Btwn$0 next$0 ?z elt$0 elt$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u elt$0)
                      (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                          (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                               (not (Btwn$0 next$0 curr_3$0 elt$0 elt$0)))))
                 (and (not (= elt$0 ?v))
                      (or (Btwn$0 next$0 ?z elt$0 ?v)
                          (and (Btwn$0 next$0 ?z elt$0 elt$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 curr_3$0 ?u ?v)
                      (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                          (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                               (not (Btwn$0 next$0 curr_3$0 elt$0 elt$0)))))
                 (not (Btwn$0 (write$0 next$0 elt$0 curr_3$0) ?z ?u ?v))))) :named P191))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P192))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P193))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P194))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P195))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P196))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P197))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P198))

(check-sat)

(get-interpolants (and P128 P32 P27 P43 P28 P72 P83 P132 P113 P33 P26 P69 P140 P12 P114 P48 P20 P57 P3 P186 P73 P159 P85 P67 P23 P127 P168 P22 P97 P180 P40 P177 P47 P129 P119 P109 P193 P135 P89 P60 P141 P99 P195 P183 P100 P130 P92 P56 P185 P94 P155 P80 P122 P5 P152 P147 P81 P108 P82 P150 P166 P76 P41 P14 P54 P79 P175 P17 P95 P84 P13 P120 P126 P154 P189 P90 P101 P38 P15 P162 P179 P50 P137 P182 P146 P0 P31 P78 P188 P25 P151 P18 P123 P190 P74 P91 P63 P112 P192 P102) (and P170 P174 P24 P29 P46 P37 P75 P35 P77 P131 P11 P68 P21 P134 P8 P142 P96 P181 P117 P144 P178 P116 P62 P98 P30 P4 P39 P187 P171 P93 P198 P173 P49 P138 P45 P153 P115 P19 P136 P157 P124 P65 P125 P71 P158 P194 P169 P148 P106 P161 P9 P10 P160 P143 P110 P139 P167 P16 P1 P66 P176 P51 P184 P172 P44 P36 P104 P7 P133 P197 P118 P105 P86 P196 P34 P111 P121 P58 P163 P2 P145 P88 P6 P107 P149 P70 P55 P42 P53 P87 P164 P156 P61 P59 P191 P64 P103 P165 P52))

(exit)