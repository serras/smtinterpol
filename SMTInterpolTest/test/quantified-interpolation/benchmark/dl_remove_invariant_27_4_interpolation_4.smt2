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
  tests/spl/dl/dl_remove.spl:27:4:An invariant might not hold before entering a loop in procedure dl_remove
  tests/spl/dl/dl_remove.spl:28:16:Related location: This is the loop invariant that might not hold initially
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
(declare-fun Axiom_5$0 () Bool)
(declare-fun Axiom_6$0 () Bool)
(declare-fun Axiom_7$0 () Bool)
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
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_FP$0 () SetLoc)
(declare-fun sk_l1_2$0 () Loc)
(declare-fun sk_l2_2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y)
            (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sk_l1_2$0 ?y ?y)) (= sk_l1_2$0 ?y)
            (Btwn$0 next$0 sk_l1_2$0 (read$0 next$0 sk_l1_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 d_1$0) d_1$0))
            (not (Btwn$0 next$0 d_1$0 ?y ?y)) (= d_1$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 sk_l1_2$0) sk_l1_2$0))
            (not (Btwn$0 next$0 sk_l1_2$0 ?y ?y)) (= sk_l1_2$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 d_1$0 (read$0 next$0 d_1$0) (read$0 next$0 d_1$0)) :named P6))

(assert (! (Btwn$0 next$0 sk_l1_2$0 (read$0 next$0 sk_l1_2$0) (read$0 next$0 sk_l1_2$0)) :named P7))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P8))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_2$0)) (not (in$0 d_1$0 sk_?X_9$0))
        (not (in$0 curr_2$0 sk_?X_9$0)))) :named P9))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) curr_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_9$0)) (not (in$0 curr_2$0 sk_?X_9$0)))) :named P10))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_9$0)) (not (in$0 curr_2$0 sk_?X_9$0)))) :named P11))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) sk_l2_2$0))
        (not (in$0 d_1$0 sk_?X_9$0)) (not (in$0 sk_l2_2$0 sk_?X_9$0)))) :named P12))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) sk_l2_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_9$0)) (not (in$0 sk_l2_2$0 sk_?X_9$0)))) :named P13))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 sk_l2_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2_2$0))
        (not (in$0 prv_2$0 sk_?X_9$0)) (not (in$0 sk_l2_2$0 sk_?X_9$0)))) :named P14))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_9$0))
        (not (in$0 prv_2$0 sk_?X_9$0)))) :named P15))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) prv_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_9$0)) (not (in$0 prv_2$0 sk_?X_9$0)))) :named P16))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_9$0)) (not (in$0 prv_2$0 sk_?X_9$0)))) :named P17))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_2$0)) (not (in$0 d_1$0 sk_?X_7$0))
        (not (in$0 curr_2$0 sk_?X_7$0)))) :named P18))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) curr_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_7$0)) (not (in$0 curr_2$0 sk_?X_7$0)))) :named P19))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_7$0)) (not (in$0 curr_2$0 sk_?X_7$0)))) :named P20))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) sk_l2_2$0))
        (not (in$0 d_1$0 sk_?X_7$0)) (not (in$0 sk_l2_2$0 sk_?X_7$0)))) :named P21))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) sk_l2_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_7$0)) (not (in$0 sk_l2_2$0 sk_?X_7$0)))) :named P22))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 sk_l2_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2_2$0))
        (not (in$0 prv_2$0 sk_?X_7$0)) (not (in$0 sk_l2_2$0 sk_?X_7$0)))) :named P23))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_7$0))
        (not (in$0 prv_2$0 sk_?X_7$0)))) :named P24))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) prv_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_7$0)) (not (in$0 prv_2$0 sk_?X_7$0)))) :named P25))

(assert (! (or (not Axiom_7$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_7$0)) (not (in$0 prv_2$0 sk_?X_7$0)))) :named P26))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) curr_2$0)) (not (in$0 d_1$0 sk_?X_5$0))
        (not (in$0 curr_2$0 sk_?X_5$0)))) :named P27))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) curr_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_5$0)) (not (in$0 curr_2$0 sk_?X_5$0)))) :named P28))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_5$0)) (not (in$0 curr_2$0 sk_?X_5$0)))) :named P29))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) sk_l2_2$0))
        (not (in$0 d_1$0 sk_?X_5$0)) (not (in$0 sk_l2_2$0 sk_?X_5$0)))) :named P30))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) sk_l2_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_5$0)) (not (in$0 sk_l2_2$0 sk_?X_5$0)))) :named P31))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 sk_l2_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2_2$0))
        (not (in$0 prv_2$0 sk_?X_5$0)) (not (in$0 sk_l2_2$0 sk_?X_5$0)))) :named P32))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) d_1$0)
        (not (= (read$0 next$0 d_1$0) prv_2$0)) (not (in$0 d_1$0 sk_?X_5$0))
        (not (in$0 prv_2$0 sk_?X_5$0)))) :named P33))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1_2$0)
        (not (= (read$0 next$0 sk_l1_2$0) prv_2$0))
        (not (in$0 sk_l1_2$0 sk_?X_5$0)) (not (in$0 prv_2$0 sk_?X_5$0)))) :named P34))

(assert (! (or (not Axiom_5$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_5$0)) (not (in$0 prv_2$0 sk_?X_5$0)))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_8$0 FP$0))
                 (or (in$0 x sk_?X_8$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_8$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_8$0 FP$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_8$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_8$0 FP$0)))
            (and (or (not (in$0 x sk_?X_8$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_8$0 FP$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P40))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P41))

(assert (! (= (read$0 next$0 null$0) null$0) :named P42))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P43))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P44))

(assert (! (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_9$0)))
         Axiom_6$0)
    (not
         (dlseg_struct$0 sk_?X_9$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))) :named P45))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P46))

(assert (! (= curr_2$0 c_1$0) :named P47))

(assert (! (= prv_2$0 null$0) :named P48))

(assert (! (= sk_?X_5$0 FP$0) :named P49))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P50))

(assert (! (= sk_?X_6$0 (union$0 sk_?X_8$0 sk_?X_7$0)) :named P51))

(assert (! (= sk_?X_8$0 sk_?X_9$0) :named P52))

(assert (! (= sk_FP$0 sk_?X_6$0) :named P53))

(assert (! (not (= a$0 null$0)) :named P54))

(assert (! (not (in$0 null$0 Alloc$0)) :named P55))

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
                          prv_2$0)))))) :named P56))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_5$0)))
         Axiom_5$0)
    (not (dlseg_struct$0 sk_?X_5$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P57))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_7$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_7$0)
    (not
         (dlseg_struct$0 sk_?X_7$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))) :named P58))

(assert (! (= c_1$0 a$0) :named P59))

(assert (! (= d_1$0 b$0) :named P60))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P61))

(assert (! (= sk_?X_5$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P62))

(assert (! (dlseg_struct$0 sk_?X_5$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P63))

(assert (! (= sk_?X_7$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)) :named P64))

(assert (! (= sk_?X_9$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)) :named P65))

(assert (! (or (= curr_2$0 null$0) (in$0 sk_l2_2$0 (intersection$0 sk_?X_8$0 sk_?X_7$0))
    (and (= (read$0 next$0 sk_l1_2$0) sk_l2_2$0) (in$0 sk_l1_2$0 sk_?X_7$0)
         (in$0 sk_l2_2$0 sk_?X_7$0)
         (not (= (read$0 prev$0 sk_l2_2$0) sk_l1_2$0)))
    (and (= (read$0 next$0 sk_l1_2$0) sk_l2_2$0) (in$0 sk_l1_2$0 sk_?X_9$0)
         (in$0 sk_l2_2$0 sk_?X_9$0)
         (not (= (read$0 prev$0 sk_l2_2$0) sk_l1_2$0)))
    (and (in$0 sk_l1_2$0 sk_FP$0) (not (in$0 sk_l1_2$0 FP$0)))
    (and (or (not (= null$0 prv_2$0)) (not (= c_1$0 curr_2$0)))
         (or (not (= (read$0 next$0 prv_2$0) curr_2$0))
             (not (= (read$0 prev$0 c_1$0) null$0))
             (not (in$0 prv_2$0 sk_?X_9$0))))
    (and
         (or (not (= (read$0 next$0 d_1$0) null$0))
             (not (= (read$0 prev$0 curr_2$0) prv_2$0))
             (not (in$0 d_1$0 sk_?X_7$0)))
         (or (not (= curr_2$0 null$0)) (not (= prv_2$0 d_1$0))))
    (not (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0))
    (not (Btwn$0 next$0 curr_2$0 null$0 null$0))) :named P66))

(assert (! (not (= a$0 b$0)) :named P67))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P68))

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
                          d_1$0)))))) :named P69))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P70))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P71))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P72))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P73))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P74))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P75))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P76))

(check-sat)

(get-interpolants (and P56 P31 P73 P21 P4 P6 P23 P34 P29 P63 P75 P3 P67 P32 P19 P68 P45 P38 P49 P27 P39 P36 P52 P24 P66 P59 P74 P26 P20 P9 P65 P58 P72 P12 P71 P1 P7 P22 P47) (and P70 P57 P62 P28 P54 P43 P42 P11 P18 P44 P50 P35 P48 P14 P15 P60 P10 P13 P30 P69 P46 P37 P17 P76 P53 P0 P16 P61 P5 P8 P33 P64 P51 P41 P25 P55 P2 P40))

(exit)