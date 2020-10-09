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
  tests/spl/dl/dl_traverse.spl:18:2:An invariant might not hold before entering a loop in procedure dl_traverse
  tests/spl/dl/dl_traverse.spl:19:14-68:Related location: This is the loop invariant that might not hold initially
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
(declare-fun Axiom$0 () Bool)
(declare-fun Axiom_1$0 () Bool)
(declare-fun Axiom_2$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun sk_?X$0 () SetLoc)
(declare-fun sk_?X_1$0 () SetLoc)
(declare-fun sk_?X_2$0 () SetLoc)
(declare-fun sk_?X_3$0 () SetLoc)
(declare-fun sk_FP$0 () SetLoc)
(declare-fun sk_l1$0 () Loc)
(declare-fun sk_l2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b$0 ?y ?y)) (= b$0 ?y)
            (Btwn$0 next$0 b$0 (read$0 next$0 b$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sk_l1$0 ?y ?y)) (= sk_l1$0 ?y)
            (Btwn$0 next$0 sk_l1$0 (read$0 next$0 sk_l1$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b$0) b$0)) (not (Btwn$0 next$0 b$0 ?y ?y))
            (= b$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 sk_l1$0) sk_l1$0))
            (not (Btwn$0 next$0 sk_l1$0 ?y ?y)) (= sk_l1$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P8))

(assert (! (Btwn$0 next$0 b$0 (read$0 next$0 b$0) (read$0 next$0 b$0)) :named P9))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P10))

(assert (! (Btwn$0 next$0 sk_l1$0 (read$0 next$0 sk_l1$0) (read$0 next$0 sk_l1$0)) :named P11))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0)) (not (in$0 null$0 sk_?X_3$0))
        (not (in$0 null$0 sk_?X_3$0)))) :named P12))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 null$0) b$0) (not (= (read$0 next$0 b$0) null$0))
        (not (in$0 b$0 sk_?X_3$0)) (not (in$0 null$0 sk_?X_3$0)))) :named P13))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 null$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) null$0))
        (not (in$0 prv_2$0 sk_?X_3$0)) (not (in$0 null$0 sk_?X_3$0)))) :named P14))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 null$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) null$0))
        (not (in$0 sk_l1$0 sk_?X_3$0)) (not (in$0 null$0 sk_?X_3$0)))) :named P15))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 curr_2$0) null$0)
        (not (= (read$0 next$0 null$0) curr_2$0))
        (not (in$0 null$0 sk_?X_3$0)) (not (in$0 curr_2$0 sk_?X_3$0)))) :named P16))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 curr_2$0) b$0)
        (not (= (read$0 next$0 b$0) curr_2$0)) (not (in$0 b$0 sk_?X_3$0))
        (not (in$0 curr_2$0 sk_?X_3$0)))) :named P17))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_3$0)) (not (in$0 curr_2$0 sk_?X_3$0)))) :named P18))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) curr_2$0))
        (not (in$0 sk_l1$0 sk_?X_3$0)) (not (in$0 curr_2$0 sk_?X_3$0)))) :named P19))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 sk_l2$0) null$0)
        (not (= (read$0 next$0 null$0) sk_l2$0))
        (not (in$0 null$0 sk_?X_3$0)) (not (in$0 sk_l2$0 sk_?X_3$0)))) :named P20))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 sk_l2$0) b$0) (not (= (read$0 next$0 b$0) sk_l2$0))
        (not (in$0 b$0 sk_?X_3$0)) (not (in$0 sk_l2$0 sk_?X_3$0)))) :named P21))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 sk_l2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2$0))
        (not (in$0 prv_2$0 sk_?X_3$0)) (not (in$0 sk_l2$0 sk_?X_3$0)))) :named P22))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 sk_l2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) sk_l2$0))
        (not (in$0 sk_l1$0 sk_?X_3$0)) (not (in$0 sk_l2$0 sk_?X_3$0)))) :named P23))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0)) (not (in$0 null$0 sk_?X_2$0))
        (not (in$0 null$0 sk_?X_2$0)))) :named P24))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) b$0) (not (= (read$0 next$0 b$0) null$0))
        (not (in$0 b$0 sk_?X_2$0)) (not (in$0 null$0 sk_?X_2$0)))) :named P25))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) null$0))
        (not (in$0 prv_2$0 sk_?X_2$0)) (not (in$0 null$0 sk_?X_2$0)))) :named P26))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) null$0))
        (not (in$0 sk_l1$0 sk_?X_2$0)) (not (in$0 null$0 sk_?X_2$0)))) :named P27))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 curr_2$0) null$0)
        (not (= (read$0 next$0 null$0) curr_2$0))
        (not (in$0 null$0 sk_?X_2$0)) (not (in$0 curr_2$0 sk_?X_2$0)))) :named P28))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 curr_2$0) b$0)
        (not (= (read$0 next$0 b$0) curr_2$0)) (not (in$0 b$0 sk_?X_2$0))
        (not (in$0 curr_2$0 sk_?X_2$0)))) :named P29))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X_2$0)) (not (in$0 curr_2$0 sk_?X_2$0)))) :named P30))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) curr_2$0))
        (not (in$0 sk_l1$0 sk_?X_2$0)) (not (in$0 curr_2$0 sk_?X_2$0)))) :named P31))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) null$0)
        (not (= (read$0 next$0 null$0) sk_l2$0))
        (not (in$0 null$0 sk_?X_2$0)) (not (in$0 sk_l2$0 sk_?X_2$0)))) :named P32))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) b$0) (not (= (read$0 next$0 b$0) sk_l2$0))
        (not (in$0 b$0 sk_?X_2$0)) (not (in$0 sk_l2$0 sk_?X_2$0)))) :named P33))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2$0))
        (not (in$0 prv_2$0 sk_?X_2$0)) (not (in$0 sk_l2$0 sk_?X_2$0)))) :named P34))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) sk_l2$0))
        (not (in$0 sk_l1$0 sk_?X_2$0)) (not (in$0 sk_l2$0 sk_?X_2$0)))) :named P35))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0)) (not (in$0 null$0 sk_?X$0))
        (not (in$0 null$0 sk_?X$0)))) :named P36))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 null$0) b$0) (not (= (read$0 next$0 b$0) null$0))
        (not (in$0 b$0 sk_?X$0)) (not (in$0 null$0 sk_?X$0)))) :named P37))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 null$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) null$0)) (not (in$0 prv_2$0 sk_?X$0))
        (not (in$0 null$0 sk_?X$0)))) :named P38))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 null$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) null$0)) (not (in$0 sk_l1$0 sk_?X$0))
        (not (in$0 null$0 sk_?X$0)))) :named P39))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 curr_2$0) null$0)
        (not (= (read$0 next$0 null$0) curr_2$0)) (not (in$0 null$0 sk_?X$0))
        (not (in$0 curr_2$0 sk_?X$0)))) :named P40))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 curr_2$0) b$0)
        (not (= (read$0 next$0 b$0) curr_2$0)) (not (in$0 b$0 sk_?X$0))
        (not (in$0 curr_2$0 sk_?X$0)))) :named P41))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 curr_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) curr_2$0))
        (not (in$0 prv_2$0 sk_?X$0)) (not (in$0 curr_2$0 sk_?X$0)))) :named P42))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 curr_2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) curr_2$0))
        (not (in$0 sk_l1$0 sk_?X$0)) (not (in$0 curr_2$0 sk_?X$0)))) :named P43))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) null$0)
        (not (= (read$0 next$0 null$0) sk_l2$0)) (not (in$0 null$0 sk_?X$0))
        (not (in$0 sk_l2$0 sk_?X$0)))) :named P44))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) b$0) (not (= (read$0 next$0 b$0) sk_l2$0))
        (not (in$0 b$0 sk_?X$0)) (not (in$0 sk_l2$0 sk_?X$0)))) :named P45))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2$0))
        (not (in$0 prv_2$0 sk_?X$0)) (not (in$0 sk_l2$0 sk_?X$0)))) :named P46))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) sk_l2$0))
        (not (in$0 sk_l1$0 sk_?X$0)) (not (in$0 sk_l2$0 sk_?X$0)))) :named P47))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P48))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P49))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_3$0 FP$0))
                 (or (in$0 x sk_?X_3$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_3$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_3$0 FP$0)))))) :named P50))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_3$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_3$0 FP$0)))
            (and (or (not (in$0 x sk_?X_3$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_3$0 FP$0)))))) :named P51))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P52))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P53))

(assert (! (= (read$0 next$0 null$0) null$0) :named P54))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P55))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P56))

(assert (! (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0) (in$0 b$0 sk_?X_2$0))
             (and (= curr_2$0 null$0) (= prv_2$0 b$0)))
         Axiom$0)
    (not
         (dlseg_struct$0 sk_?X_2$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0))) :named P57))

(assert (! (or
    (and (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0)
         (or
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 lst$0) a$0) (in$0 prv_2$0 sk_?X_3$0))
             (and (= a$0 prv_2$0) (= lst$0 curr_2$0)))
         Axiom_2$0)
    (not (dlseg_struct$0 sk_?X_3$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0))) :named P58))

(assert (! (= curr_2$0 lst$0) :named P59))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P60))

(assert (! (= sk_?X$0 (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0)) :named P61))

(assert (! (dlseg_struct$0 sk_?X$0 next$0 prev$0 lst$0 a$0 null$0 b$0) :named P62))

(assert (! (= sk_?X_2$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0)) :named P63))

(assert (! (= sk_FP$0 sk_?X_1$0) :named P64))

(assert (! (not (in$0 null$0 Alloc$0)) :named P65))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 lst$0 a$0 null$0 b$0)))))) :named P66))

(assert (! (or
    (and (Btwn$0 next$0 lst$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 lst$0) a$0) (in$0 b$0 sk_?X$0))
             (and (= a$0 b$0) (= lst$0 null$0)))
         Axiom_1$0)
    (not (dlseg_struct$0 sk_?X$0 next$0 prev$0 lst$0 a$0 null$0 b$0))) :named P67))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P68))

(assert (! (= prv_2$0 a$0) :named P69))

(assert (! (= sk_?X$0 FP$0) :named P70))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P71))

(assert (! (= sk_?X_1$0 (union$0 sk_?X_3$0 sk_?X_2$0)) :named P72))

(assert (! (= sk_?X_3$0 (dlseg_domain$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0)) :named P73))

(assert (! (or (in$0 sk_l2$0 (intersection$0 sk_?X_3$0 sk_?X_2$0))
    (and (= (read$0 next$0 sk_l1$0) sk_l2$0) (in$0 sk_l1$0 sk_?X_2$0)
         (in$0 sk_l2$0 sk_?X_2$0) (not (= (read$0 prev$0 sk_l2$0) sk_l1$0)))
    (and (= (read$0 next$0 sk_l1$0) sk_l2$0) (in$0 sk_l1$0 sk_?X_3$0)
         (in$0 sk_l2$0 sk_?X_3$0) (not (= (read$0 prev$0 sk_l2$0) sk_l1$0)))
    (and (in$0 sk_l1$0 sk_FP$0) (not (in$0 sk_l1$0 FP$0)))
    (and
         (or (not (= (read$0 next$0 b$0) null$0))
             (not (= (read$0 prev$0 curr_2$0) prv_2$0))
             (not (in$0 b$0 sk_?X_2$0)))
         (or (not (= curr_2$0 null$0)) (not (= prv_2$0 b$0))))
    (and
         (or (not (= (read$0 next$0 prv_2$0) curr_2$0))
             (not (= (read$0 prev$0 lst$0) a$0))
             (not (in$0 prv_2$0 sk_?X_3$0)))
         (or (not (= a$0 prv_2$0)) (not (= lst$0 curr_2$0))))
    (not (Btwn$0 next$0 curr_2$0 null$0 null$0))
    (not (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0))) :named P74))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                          b$0)))))) :named P75))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 lst$0 a$0 curr_2$0 prv_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 lst$0 a$0 curr_2$0
                          prv_2$0)))))) :named P76))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P77))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P78))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P79))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P80))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P81))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P82))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P83))

(check-sat)

(get-interpolants (and P2 P16 P17 P23 P47 P5 P43 P73 P12 P27 P10 P7 P14 P8 P48 P36 P54 P58 P9 P55 P76 P40 P29 P18 P25 P32 P59 P78 P11 P28 P38 P70 P57 P66 P61 P31 P71 P80 P33 P15 P6 P42) (and P19 P49 P50 P22 P45 P46 P77 P56 P3 P74 P1 P30 P37 P52 P4 P81 P24 P53 P83 P26 P21 P75 P34 P67 P79 P62 P51 P63 P68 P13 P65 P82 P0 P39 P35 P41 P44 P64 P20 P69 P60 P72))

(exit)