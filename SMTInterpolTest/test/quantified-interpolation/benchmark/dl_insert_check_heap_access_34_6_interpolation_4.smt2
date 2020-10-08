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
  tests/spl/dl/dl_insert.spl:34:6-22:Possible heap access through null or dangling reference
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
(declare-fun Axiom_16$0 () Bool)
(declare-fun Axiom_17$0 () Bool)
(declare-fun Axiom_18$0 () Bool)
(declare-fun Axiom_19$0 () Bool)
(declare-fun Axiom_20$0 () Bool)
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
(declare-fun prev_1$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun sk_?X_42$0 () SetLoc)
(declare-fun sk_?X_43$0 () SetLoc)
(declare-fun sk_?X_44$0 () SetLoc)
(declare-fun sk_?X_45$0 () SetLoc)
(declare-fun sk_?X_46$0 () SetLoc)
(declare-fun sk_?X_47$0 () SetLoc)
(declare-fun sk_?X_48$0 () SetLoc)
(declare-fun sk_?X_49$0 () SetLoc)
(declare-fun sk_?X_50$0 () SetLoc)
(declare-fun sk_?X_51$0 () SetLoc)
(declare-fun sk_?X_52$0 () SetLoc)

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

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P15))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P16))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P17))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P18))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_46$0)) (not (in$0 c_1$0 sk_?X_46$0)))) :named P19))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P20))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P21))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P22))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P23))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_46$0)) (not (in$0 curr_3$0 sk_?X_46$0)))) :named P24))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_46$0))
        (not (in$0 prv_2$0 sk_?X_46$0)))) :named P25))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_46$0)) (not (in$0 prv_2$0 sk_?X_46$0)))) :named P26))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_46$0)) (not (in$0 prv_2$0 sk_?X_46$0)))) :named P27))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_46$0)) (not (in$0 prv_2$0 sk_?X_46$0)))) :named P28))

(assert (! (or (not Axiom_19$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_46$0))
        (not (in$0 prv_2$0 sk_?X_46$0)))) :named P29))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P30))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P31))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P32))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P33))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_48$0)) (not (in$0 c_1$0 sk_?X_48$0)))) :named P34))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P35))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P36))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P37))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P38))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_48$0)) (not (in$0 curr_3$0 sk_?X_48$0)))) :named P39))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_48$0))
        (not (in$0 prv_2$0 sk_?X_48$0)))) :named P40))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_48$0)) (not (in$0 prv_2$0 sk_?X_48$0)))) :named P41))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_48$0)) (not (in$0 prv_2$0 sk_?X_48$0)))) :named P42))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_48$0)) (not (in$0 prv_2$0 sk_?X_48$0)))) :named P43))

(assert (! (or (not Axiom_17$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_48$0))
        (not (in$0 prv_2$0 sk_?X_48$0)))) :named P44))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_45$0 c_1$0) ?y)
            (not (Btwn$0 next$0 c_1$0 ?y ?y)) (not (in$0 ?y sk_?X_45$0)))) :named P45))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_45$0 d_1$0) ?y)
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (not (in$0 ?y sk_?X_45$0)))) :named P46))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_45$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_45$0)))) :named P47))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_45$0 prv_2$0) ?y)
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (not (in$0 ?y sk_?X_45$0)))) :named P48))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_45$0 prv_3$0) ?y)
            (not (Btwn$0 next$0 prv_3$0 ?y ?y)) (not (in$0 ?y sk_?X_45$0)))) :named P49))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_45$0 c_1$0) sk_?X_45$0)
    (= c_1$0 (ep$0 next$0 sk_?X_45$0 c_1$0))) :named P50))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_45$0 d_1$0) sk_?X_45$0)
    (= d_1$0 (ep$0 next$0 sk_?X_45$0 d_1$0))) :named P51))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_45$0 curr_3$0) sk_?X_45$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_45$0 curr_3$0))) :named P52))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_45$0 prv_2$0) sk_?X_45$0)
    (= prv_2$0 (ep$0 next$0 sk_?X_45$0 prv_2$0))) :named P53))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_45$0 prv_3$0) sk_?X_45$0)
    (= prv_3$0 (ep$0 next$0 sk_?X_45$0 prv_3$0))) :named P54))

(assert (! (Btwn$0 next$0 c_1$0 (ep$0 next$0 sk_?X_45$0 c_1$0)
  (ep$0 next$0 sk_?X_45$0 c_1$0)) :named P55))

(assert (! (Btwn$0 next$0 d_1$0 (ep$0 next$0 sk_?X_45$0 d_1$0)
  (ep$0 next$0 sk_?X_45$0 d_1$0)) :named P56))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_45$0 curr_3$0)
  (ep$0 next$0 sk_?X_45$0 curr_3$0)) :named P57))

(assert (! (Btwn$0 next$0 prv_2$0 (ep$0 next$0 sk_?X_45$0 prv_2$0)
  (ep$0 next$0 sk_?X_45$0 prv_2$0)) :named P58))

(assert (! (Btwn$0 next$0 prv_3$0 (ep$0 next$0 sk_?X_45$0 prv_3$0)
  (ep$0 next$0 sk_?X_45$0 prv_3$0)) :named P59))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_43$0)) (not (in$0 c_1$0 sk_?X_43$0)))) :named P60))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_43$0)) (not (in$0 c_1$0 sk_?X_43$0)))) :named P61))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_43$0)) (not (in$0 c_1$0 sk_?X_43$0)))) :named P62))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_43$0)) (not (in$0 c_1$0 sk_?X_43$0)))) :named P63))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_43$0)) (not (in$0 c_1$0 sk_?X_43$0)))) :named P64))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_43$0)) (not (in$0 curr_3$0 sk_?X_43$0)))) :named P65))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_43$0)) (not (in$0 curr_3$0 sk_?X_43$0)))) :named P66))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_43$0)) (not (in$0 curr_3$0 sk_?X_43$0)))) :named P67))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_43$0)) (not (in$0 curr_3$0 sk_?X_43$0)))) :named P68))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_43$0)) (not (in$0 curr_3$0 sk_?X_43$0)))) :named P69))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_43$0))
        (not (in$0 prv_2$0 sk_?X_43$0)))) :named P70))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_43$0)) (not (in$0 prv_2$0 sk_?X_43$0)))) :named P71))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_43$0)) (not (in$0 prv_2$0 sk_?X_43$0)))) :named P72))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_43$0)) (not (in$0 prv_2$0 sk_?X_43$0)))) :named P73))

(assert (! (or (not Axiom_20$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_43$0))
        (not (in$0 prv_2$0 sk_?X_43$0)))) :named P74))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_41$0)) (not (in$0 c_1$0 sk_?X_41$0)))) :named P75))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_41$0)) (not (in$0 c_1$0 sk_?X_41$0)))) :named P76))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_41$0)) (not (in$0 c_1$0 sk_?X_41$0)))) :named P77))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_41$0)) (not (in$0 c_1$0 sk_?X_41$0)))) :named P78))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_41$0)) (not (in$0 c_1$0 sk_?X_41$0)))) :named P79))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_41$0)) (not (in$0 curr_3$0 sk_?X_41$0)))) :named P80))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_41$0)) (not (in$0 curr_3$0 sk_?X_41$0)))) :named P81))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_41$0)) (not (in$0 curr_3$0 sk_?X_41$0)))) :named P82))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_41$0)) (not (in$0 curr_3$0 sk_?X_41$0)))) :named P83))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_41$0)) (not (in$0 curr_3$0 sk_?X_41$0)))) :named P84))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_41$0))
        (not (in$0 prv_2$0 sk_?X_41$0)))) :named P85))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_41$0)) (not (in$0 prv_2$0 sk_?X_41$0)))) :named P86))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_41$0)) (not (in$0 prv_2$0 sk_?X_41$0)))) :named P87))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_41$0)) (not (in$0 prv_2$0 sk_?X_41$0)))) :named P88))

(assert (! (or (not Axiom_18$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_41$0))
        (not (in$0 prv_2$0 sk_?X_41$0)))) :named P89))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) d_1$0) (not (= (read$0 next$0 d_1$0) c_1$0))
        (not (in$0 d_1$0 sk_?X_52$0)) (not (in$0 c_1$0 sk_?X_52$0)))) :named P90))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) c_1$0))
        (not (in$0 curr_3$0 sk_?X_52$0)) (not (in$0 c_1$0 sk_?X_52$0)))) :named P91))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) c_1$0))
        (not (in$0 prv_3$0 sk_?X_52$0)) (not (in$0 c_1$0 sk_?X_52$0)))) :named P92))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) c_1$0))
        (not (in$0 prv_2$0 sk_?X_52$0)) (not (in$0 c_1$0 sk_?X_52$0)))) :named P93))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 c_1$0) elt$0) (not (= (read$0 next$0 elt$0) c_1$0))
        (not (in$0 elt$0 sk_?X_52$0)) (not (in$0 c_1$0 sk_?X_52$0)))) :named P94))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_3$0))
        (not (in$0 d_1$0 sk_?X_52$0)) (not (in$0 curr_3$0 sk_?X_52$0)))) :named P95))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) curr_3$0))
        (not (in$0 curr_3$0 sk_?X_52$0)) (not (in$0 curr_3$0 sk_?X_52$0)))) :named P96))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) curr_3$0))
        (not (in$0 prv_3$0 sk_?X_52$0)) (not (in$0 curr_3$0 sk_?X_52$0)))) :named P97))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_3$0))
        (not (in$0 prv_2$0 sk_?X_52$0)) (not (in$0 curr_3$0 sk_?X_52$0)))) :named P98))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 curr_3$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_3$0))
        (not (in$0 elt$0 sk_?X_52$0)) (not (in$0 curr_3$0 sk_?X_52$0)))) :named P99))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_52$0))
        (not (in$0 prv_2$0 sk_?X_52$0)))) :named P100))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) curr_3$0)
        (not (= (read$0 next$0 curr_3$0) prv_2$0))
        (not (in$0 curr_3$0 sk_?X_52$0)) (not (in$0 prv_2$0 sk_?X_52$0)))) :named P101))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) prv_3$0)
        (not (= (read$0 next$0 prv_3$0) prv_2$0))
        (not (in$0 prv_3$0 sk_?X_52$0)) (not (in$0 prv_2$0 sk_?X_52$0)))) :named P102))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_52$0)) (not (in$0 prv_2$0 sk_?X_52$0)))) :named P103))

(assert (! (or (not Axiom_16$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_52$0))
        (not (in$0 prv_2$0 sk_?X_52$0)))) :named P104))

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
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_44$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_44$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_44$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_44$0)))))) :named P107))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_49$0 FP_Caller$0))
                 (or (in$0 x sk_?X_49$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_49$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_49$0 FP_Caller$0)))))) :named P108))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_41$0 sk_?X_43$0))
                 (or (in$0 x sk_?X_41$0) (in$0 x sk_?X_43$0)))
            (and (not (in$0 x sk_?X_41$0)) (not (in$0 x sk_?X_43$0))
                 (not (in$0 x (union$0 sk_?X_41$0 sk_?X_43$0)))))) :named P109))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P110))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_48$0 sk_?X_52$0))
                 (or (in$0 x sk_?X_48$0) (in$0 x sk_?X_52$0)))
            (and (not (in$0 x sk_?X_48$0)) (not (in$0 x sk_?X_52$0))
                 (not (in$0 x (union$0 sk_?X_48$0 sk_?X_52$0)))))) :named P111))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_52$0 sk_?X_50$0))
                 (or (in$0 x sk_?X_52$0) (in$0 x sk_?X_50$0)))
            (and (not (in$0 x sk_?X_52$0)) (not (in$0 x sk_?X_50$0))
                 (not (in$0 x (union$0 sk_?X_52$0 sk_?X_50$0)))))) :named P112))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_45$0 sk_?X_49$0))
                 (or (in$0 x sk_?X_45$0) (in$0 x sk_?X_49$0)))
            (and (not (in$0 x sk_?X_45$0)) (not (in$0 x sk_?X_49$0))
                 (not (in$0 x (union$0 sk_?X_45$0 sk_?X_49$0)))))) :named P113))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_52$0) (in$0 x sk_?X_50$0)
                 (in$0 x (intersection$0 sk_?X_52$0 sk_?X_50$0)))
            (and (or (not (in$0 x sk_?X_52$0)) (not (in$0 x sk_?X_50$0)))
                 (not (in$0 x (intersection$0 sk_?X_52$0 sk_?X_50$0)))))) :named P114))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_48$0) (in$0 x sk_?X_52$0)
                 (in$0 x (intersection$0 sk_?X_48$0 sk_?X_52$0)))
            (and (or (not (in$0 x sk_?X_48$0)) (not (in$0 x sk_?X_52$0)))
                 (not (in$0 x (intersection$0 sk_?X_48$0 sk_?X_52$0)))))) :named P115))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_41$0) (in$0 x sk_?X_43$0)
                 (in$0 x (intersection$0 sk_?X_41$0 sk_?X_43$0)))
            (and (or (not (in$0 x sk_?X_41$0)) (not (in$0 x sk_?X_43$0)))
                 (not (in$0 x (intersection$0 sk_?X_41$0 sk_?X_43$0)))))) :named P116))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_45$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_45$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_45$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_45$0)))))) :named P117))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P118))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_49$0)
                 (in$0 x (setminus$0 sk_?X_49$0 sk_?X_45$0))
                 (not (in$0 x sk_?X_45$0)))
            (and (or (in$0 x sk_?X_45$0) (not (in$0 x sk_?X_49$0)))
                 (not (in$0 x (setminus$0 sk_?X_49$0 sk_?X_45$0)))))) :named P119))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_49$0))
                 (not (in$0 x sk_?X_49$0)))
            (and (or (in$0 x sk_?X_49$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_49$0)))))) :named P120))

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

(assert (! (= (read$0 (write$0 prev$0 curr_3$0 elt$0) curr_3$0) elt$0) :named P128))

(assert (! (or (= c_1$0 curr_3$0)
    (= (read$0 prev$0 c_1$0) (read$0 (write$0 prev$0 curr_3$0 elt$0) c_1$0))) :named P129))

(assert (! (or (= curr_3$0 curr_3$0)
    (= (read$0 prev$0 curr_3$0)
      (read$0 (write$0 prev$0 curr_3$0 elt$0) curr_3$0))) :named P130))

(assert (! (or (= prv_2$0 curr_3$0)
    (= (read$0 prev$0 prv_2$0)
      (read$0 (write$0 prev$0 curr_3$0 elt$0) prv_2$0))) :named P131))

(assert (! (= (read$0 next$0 null$0) null$0) :named P132))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P133))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P134))

(assert (! (= (read$0 prev_1$0 null$0) null$0) :named P135))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P136))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P137))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_48$0)))
         Axiom_17$0)
    (not
         (dlseg_struct$0 sk_?X_48$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P138))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_46$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_19$0)
    (not
         (dlseg_struct$0 sk_?X_46$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P139))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P140))

(assert (! (= c_1$0 a$0) :named P141))

(assert (! (= curr_2$0 c_1$0) :named P142))

(assert (! (= d_2$0 d_1$0) :named P143))

(assert (! (= prev_1$0 (write$0 prev$0 curr_3$0 elt$0)) :named P144))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P145))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P146))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P147))

(assert (! (= emptyset$0 (intersection$0 sk_?X_52$0 sk_?X_50$0)) :named P148))

(assert (! (= sk_?X_49$0 FP$0) :named P149))

(assert (! (= sk_?X_51$0 (setenum$0 elt$0)) :named P150))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P151))

(assert (! (= emptyset$0 emptyset$0) :named P152))

(assert (! (= sk_?X_41$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)) :named P153))

(assert (! (= sk_?X_43$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)) :named P154))

(assert (! (= sk_?X_44$0 (union$0 sk_?X_42$0 sk_?X_43$0)) :named P155))

(assert (! (dlseg_struct$0 sk_?X_43$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0) :named P156))

(assert (! (= emptyset$0 emptyset$0) :named P157))

(assert (! (= sk_?X_45$0 (union$0 sk_?X_47$0 sk_?X_46$0)) :named P158))

(assert (! (= sk_?X_46$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P159))

(assert (! (= sk_?X_48$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P160))

(assert (! (dlseg_struct$0 sk_?X_46$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0) :named P161))

(assert (! (not (= curr_2$0 null$0)) :named P162))

(assert (! (not (= prv_3$0 null$0)) :named P163))

(assert (! (not (in$0 null$0 Alloc$0)) :named P164))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P165))

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
                          prv_3$0)))))) :named P166))

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
                          d_2$0)))))) :named P167))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_52$0)))
         Axiom_16$0)
    (not (dlseg_struct$0 sk_?X_52$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P168))

(assert (! (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_41$0)))
         Axiom_18$0)
    (not
         (dlseg_struct$0 sk_?X_41$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))) :named P169))

(assert (! (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_43$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_20$0)
    (not
         (dlseg_struct$0 sk_?X_43$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))) :named P170))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P171))

(assert (! (= c_2$0 c_1$0) :named P172))

(assert (! (= d_1$0 b$0) :named P173))

(assert (! (= next_1$0 (write$0 next$0 elt$0 curr_3$0)) :named P174))

(assert (! (= prv_2$0 null$0) :named P175))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P176))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P177))

(assert (! (= emptyset$0 emptyset$0) :named P178))

(assert (! (= sk_?X_49$0 (union$0 sk_?X_52$0 sk_?X_50$0)) :named P179))

(assert (! (= sk_?X_50$0 sk_?X_51$0) :named P180))

(assert (! (= sk_?X_52$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P181))

(assert (! (dlseg_struct$0 sk_?X_52$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P182))

(assert (! (= emptyset$0 (intersection$0 sk_?X_42$0 sk_?X_43$0)) :named P183))

(assert (! (= sk_?X_42$0 sk_?X_41$0) :named P184))

(assert (! (= sk_?X_44$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P185))

(assert (! (dlseg_struct$0 sk_?X_41$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0) :named P186))

(assert (! (not (= curr_3$0 null$0)) :named P187))

(assert (! (= emptyset$0 (intersection$0 sk_?X_47$0 sk_?X_46$0)) :named P188))

(assert (! (= sk_?X_45$0 FP_1$0) :named P189))

(assert (! (= sk_?X_47$0 sk_?X_48$0) :named P190))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P191))

(assert (! (dlseg_struct$0 sk_?X_48$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0) :named P192))

(assert (! (not (= a$0 null$0)) :named P193))

(assert (! (not (in$0 null$0 Alloc$0)) :named P194))

(assert (! (not (in$0 prv_3$0 FP_2$0)) :named P195))

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
                          prv_2$0)))))) :named P196))

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
                          d_1$0)))))) :named P197))

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
                 (not (Btwn$0 (write$0 next$0 elt$0 curr_3$0) ?z ?u ?v))))) :named P198))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P199))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P200))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P201))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P202))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P203))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P204))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P205))

(check-sat)

(get-interpolants (and P68 P15 P60 P106 P78 P136 P175 P168 P156 P18 P176 P182 P180 P92 P61 P160 P138 P198 P26 P59 P125 P196 P172 P99 P55 P66 P111 P110 P178 P139 P85 P118 P202 P105 P108 P155 P130 P150 P81 P149 P128 P107 P181 P159 P30 P38 P119 P167 P158 P98 P19 P186 P151 P20 P75 P41 P104 P2 P65 P195 P169 P44 P72 P21 P205 P164 P143 P97 P80 P91 P115 P8 P131 P6 P113 P117 P145 P126 P163 P204 P16 P134 P199 P23 P73 P123 P161 P95 P153 P51 P34 P133 P135 P171 P1 P200 P192 P82 P162 P71 P11 P142 P36) (and P58 P76 P83 P203 P189 P173 P9 P170 P25 P54 P43 P24 P191 P69 P28 P121 P190 P37 P27 P124 P122 P148 P201 P33 P193 P13 P94 P90 P10 P165 P188 P88 P67 P177 P53 P140 P50 P14 P12 P70 P17 P84 P63 P109 P152 P32 P116 P96 P197 P49 P56 P101 P7 P42 P45 P57 P129 P46 P194 P144 P100 P3 P166 P120 P137 P35 P87 P103 P179 P52 P187 P141 P174 P48 P22 P64 P102 P146 P114 P47 P39 P31 P157 P40 P93 P62 P29 P183 P112 P5 P0 P132 P4 P74 P184 P89 P77 P185 P127 P86 P79 P147 P154))

(exit)