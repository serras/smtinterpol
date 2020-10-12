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
  tests/spl/dl/dl_insert.spl:24:4:An invariant might not hold before entering a loop in procedure dl_insert
  tests/spl/dl/dl_insert.spl:25:16-88:Related location: This is the loop invariant that might not hold initially
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
(declare-fun Axiom_3$0 () Bool)
(declare-fun Axiom_4$0 () Bool)
(declare-fun Axiom_5$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun c_1$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun d_1$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun elt$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_FP$0 () SetLoc)
(declare-fun sk_l1_1$0 () Loc)
(declare-fun sk_l2_1$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y)
            (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sk_l1_1$0 ?y ?y)) (= sk_l1_1$0 ?y)
            (Btwn$0 next$0 sk_l1_1$0 (read$0 next$0 sk_l1_1$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_1$0) d_1$0))
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 sk_l1_1$0) sk_l1_1$0))
            (not (Btwn$0 next$0 sk_l1_1$0 ?y ?y)) (= sk_l1_1$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 elt$0) elt$0))
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) (read$0 next$0 d_1$0)) :named P8))

(assert (! (Btwn$0 next$0 sk_l1_1$0 (read$0 next$0 sk_l1_1$0) (read$0 next$0 sk_l1_1$0)) :named P9))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P10))

(assert (! (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) (read$0 next$0 elt$0)) :named P11))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_2$0))
        (not (in$0 d_1$0 sk_?X_14$0)) (not (in$0 curr_2$0 sk_?X_14$0)))) :named P12))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_2$0))
        (not (in$0 sk_l1_1$0 sk_?X_14$0)) (not (in$0 curr_2$0 sk_?X_14$0)))) :named P13))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_14$0)) (not (in$0 curr_2$0 sk_?X_14$0)))) :named P14))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_2$0))
        (not (in$0 elt$0 sk_?X_14$0)) (not (in$0 curr_2$0 sk_?X_14$0)))) :named P15))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) sk_l2_1$0))
        (not (in$0 d_1$0 sk_?X_14$0)) (not (in$0 sk_l2_1$0 sk_?X_14$0)))) :named P16))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_14$0)) (not (in$0 sk_l2_1$0 sk_?X_14$0)))) :named P17))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2_1$0))
        (not (in$0 prv_2$0 sk_?X_14$0)) (not (in$0 sk_l2_1$0 sk_?X_14$0)))) :named P18))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_1$0) elt$0)
        (not (= (read$0 next$0 elt$0) sk_l2_1$0))
        (not (in$0 elt$0 sk_?X_14$0)) (not (in$0 sk_l2_1$0 sk_?X_14$0)))) :named P19))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_14$0))
        (not (in$0 prv_2$0 sk_?X_14$0)))) :named P20))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) prv_2$0))
        (not (in$0 sk_l1_1$0 sk_?X_14$0)) (not (in$0 prv_2$0 sk_?X_14$0)))) :named P21))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_14$0)) (not (in$0 prv_2$0 sk_?X_14$0)))) :named P22))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_14$0))
        (not (in$0 prv_2$0 sk_?X_14$0)))) :named P23))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_2$0))
        (not (in$0 d_1$0 sk_?X_12$0)) (not (in$0 curr_2$0 sk_?X_12$0)))) :named P24))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_2$0))
        (not (in$0 sk_l1_1$0 sk_?X_12$0)) (not (in$0 curr_2$0 sk_?X_12$0)))) :named P25))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_12$0)) (not (in$0 curr_2$0 sk_?X_12$0)))) :named P26))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 curr_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_2$0))
        (not (in$0 elt$0 sk_?X_12$0)) (not (in$0 curr_2$0 sk_?X_12$0)))) :named P27))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) sk_l2_1$0))
        (not (in$0 d_1$0 sk_?X_12$0)) (not (in$0 sk_l2_1$0 sk_?X_12$0)))) :named P28))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_12$0)) (not (in$0 sk_l2_1$0 sk_?X_12$0)))) :named P29))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2_1$0))
        (not (in$0 prv_2$0 sk_?X_12$0)) (not (in$0 sk_l2_1$0 sk_?X_12$0)))) :named P30))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 sk_l2_1$0) elt$0)
        (not (= (read$0 next$0 elt$0) sk_l2_1$0))
        (not (in$0 elt$0 sk_?X_12$0)) (not (in$0 sk_l2_1$0 sk_?X_12$0)))) :named P31))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_12$0))
        (not (in$0 prv_2$0 sk_?X_12$0)))) :named P32))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) prv_2$0))
        (not (in$0 sk_l1_1$0 sk_?X_12$0)) (not (in$0 prv_2$0 sk_?X_12$0)))) :named P33))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_12$0)) (not (in$0 prv_2$0 sk_?X_12$0)))) :named P34))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_12$0))
        (not (in$0 prv_2$0 sk_?X_12$0)))) :named P35))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_2$0))
        (not (in$0 d_1$0 sk_?X_16$0)) (not (in$0 curr_2$0 sk_?X_16$0)))) :named P36))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) curr_2$0))
        (not (in$0 sk_l1_1$0 sk_?X_16$0)) (not (in$0 curr_2$0 sk_?X_16$0)))) :named P37))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_16$0)) (not (in$0 curr_2$0 sk_?X_16$0)))) :named P38))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 curr_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) curr_2$0))
        (not (in$0 elt$0 sk_?X_16$0)) (not (in$0 curr_2$0 sk_?X_16$0)))) :named P39))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) sk_l2_1$0))
        (not (in$0 d_1$0 sk_?X_16$0)) (not (in$0 sk_l2_1$0 sk_?X_16$0)))) :named P40))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0))
        (not (in$0 sk_l1_1$0 sk_?X_16$0)) (not (in$0 sk_l2_1$0 sk_?X_16$0)))) :named P41))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2_1$0))
        (not (in$0 prv_2$0 sk_?X_16$0)) (not (in$0 sk_l2_1$0 sk_?X_16$0)))) :named P42))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 sk_l2_1$0) elt$0)
        (not (= (read$0 next$0 elt$0) sk_l2_1$0))
        (not (in$0 elt$0 sk_?X_16$0)) (not (in$0 sk_l2_1$0 sk_?X_16$0)))) :named P43))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_16$0))
        (not (in$0 prv_2$0 sk_?X_16$0)))) :named P44))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1_1$0)
        (not (= (read$0 next$0 sk_l1_1$0) prv_2$0))
        (not (in$0 sk_l1_1$0 sk_?X_16$0)) (not (in$0 prv_2$0 sk_?X_16$0)))) :named P45))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_16$0)) (not (in$0 prv_2$0 sk_?X_16$0)))) :named P46))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 prv_2$0) elt$0)
        (not (= (read$0 next$0 elt$0) prv_2$0)) (not (in$0 elt$0 sk_?X_16$0))
        (not (in$0 prv_2$0 sk_?X_16$0)))) :named P47))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P48))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_14$0 sk_?X_10$0))
                 (or (in$0 x sk_?X_14$0) (in$0 x sk_?X_10$0)))
            (and (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_10$0))
                 (not (in$0 x (union$0 sk_?X_14$0 sk_?X_10$0)))))) :named P49))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P50))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_15$0 sk_?X_14$0))
                 (or (in$0 x sk_?X_15$0) (in$0 x sk_?X_14$0)))
            (and (not (in$0 x sk_?X_15$0)) (not (in$0 x sk_?X_14$0))
                 (not (in$0 x (union$0 sk_?X_15$0 sk_?X_14$0)))))) :named P51))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_14$0) (in$0 x sk_?X_10$0)
                 (in$0 x (intersection$0 sk_?X_14$0 sk_?X_10$0)))
            (and (or (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_10$0)))
                 (not (in$0 x (intersection$0 sk_?X_14$0 sk_?X_10$0)))))) :named P52))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_15$0) (in$0 x sk_?X_14$0)
                 (in$0 x (intersection$0 sk_?X_15$0 sk_?X_14$0)))
            (and (or (not (in$0 x sk_?X_15$0)) (not (in$0 x sk_?X_14$0)))
                 (not (in$0 x (intersection$0 sk_?X_15$0 sk_?X_14$0)))))) :named P53))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P54))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P55))

(assert (! (= (read$0 next$0 null$0) null$0) :named P56))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P57))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P58))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_12$0)))
         Axiom_3$0)
    (not (dlseg_struct$0 sk_?X_12$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P59))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_14$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_5$0)
    (not
         (dlseg_struct$0 sk_?X_14$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P60))

(assert (! (= c_1$0 a$0) :named P61))

(assert (! (= d_1$0 b$0) :named P62))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P63))

(assert (! (= emptyset$0 emptyset$0) :named P64))

(assert (! (= sk_?X_9$0 (union$0 sk_?X_12$0 sk_?X_10$0)) :named P65))

(assert (! (= sk_?X_10$0 sk_?X_11$0) :named P66))

(assert (! (= sk_?X_12$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P67))

(assert (! (dlseg_struct$0 sk_?X_12$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P68))

(assert (! (= sk_?X_14$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P69))

(assert (! (= sk_?X_16$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P70))

(assert (! (or (= curr_2$0 null$0)
    (in$0 sk_l2_1$0 (intersection$0 sk_?X_15$0 sk_?X_14$0))
    (and (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0) (in$0 sk_l1_1$0 sk_?X_14$0)
         (in$0 sk_l2_1$0 sk_?X_14$0)
         (not (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)))
    (and (= (read$0 next$0 sk_l1_1$0) sk_l2_1$0) (in$0 sk_l1_1$0 sk_?X_16$0)
         (in$0 sk_l2_1$0 sk_?X_16$0)
         (not (= (read$0 prev$0 sk_l2_1$0) sk_l1_1$0)))
    (and (in$0 sk_l1_1$0 sk_FP$0) (not (in$0 sk_l1_1$0 FP$0)))
    (and (or (not (= null$0 prv_2$0)) (not (= c_1$0 curr_2$0)))
         (or (not (= (read$0 next$0 prv_2$0) curr_2$0))
             (not (= (read$0 prev$0 c_1$0) null$0))
             (not (in$0 prv_2$0 sk_?X_16$0))))
    (and
         (or (not (= (read$0 next$0 d_1$0) null$0))
             (not (= (read$0 prev$0 curr_2$0) prv_2$0))
             (not (in$0 d_1$0 sk_?X_14$0)))
         (or (not (= curr_2$0 null$0)) (not (= prv_2$0 d_1$0))))
    (not (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0))
    (not (Btwn$0 next$0 curr_2$0 null$0 null$0))) :named P71))

(assert (! (not (in$0 null$0 Alloc$0)) :named P72))

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
                          prv_2$0)))))) :named P73))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_16$0)))
         Axiom_4$0)
    (not
         (dlseg_struct$0 sk_?X_16$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P74))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P75))

(assert (! (= curr_2$0 c_1$0) :named P76))

(assert (! (= prv_2$0 null$0) :named P77))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P78))

(assert (! (= emptyset$0 (intersection$0 sk_?X_12$0 sk_?X_10$0)) :named P79))

(assert (! (= sk_?X_9$0 FP$0) :named P80))

(assert (! (= sk_?X_11$0 (setenum$0 elt$0)) :named P81))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P82))

(assert (! (= sk_?X_13$0 (union$0 sk_?X_15$0 sk_?X_14$0)) :named P83))

(assert (! (= sk_?X_15$0 sk_?X_16$0) :named P84))

(assert (! (= sk_FP$0 sk_?X_13$0) :named P85))

(assert (! (not (= a$0 null$0)) :named P86))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P87))

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
                          d_1$0)))))) :named P88))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P89))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P90))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P91))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P92))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P93))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P94))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P95))

(check-sat)

(get-interpolants (and P4 P44 P40 P26 P85 P6 P51 P66 P86 P33 P10 P65 P53 P84 P16 P72 P71 P49 P75 P67 P94 P52 P74 P20 P69 P31 P24 P0 P78 P17 P59 P91 P38 P64 P2 P80 P90 P48 P32 P9 P15 P87 P37 P95 P36 P93 P46 P50) (and P63 P11 P77 P25 P30 P5 P13 P22 P1 P14 P19 P7 P18 P43 P28 P34 P79 P45 P58 P68 P61 P41 P12 P27 P89 P55 P92 P23 P47 P29 P42 P60 P35 P56 P81 P57 P70 P62 P8 P76 P21 P3 P82 P39 P88 P73 P54 P83))

(exit)