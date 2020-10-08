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
  tests/spl/dl/dl_dispose.spl:17:2:An invariant might not hold before entering a loop in procedure dl_dispose
  tests/spl/dl/dl_dispose.spl:18:14-36:Related location: This is the loop invariant that might not hold initially
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
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom$0 () Bool)
(declare-fun Axiom_1$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun sk_?X$0 () SetLoc)
(declare-fun sk_?X_1$0 () SetLoc)
(declare-fun sk_FP$0 () SetLoc)
(declare-fun sk_l1$0 () Loc)
(declare-fun sk_l2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b$0 ?y ?y)) (= b$0 ?y)
            (Btwn$0 next$0 b$0 (read$0 next$0 b$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sk_l1$0 ?y ?y)) (= sk_l1$0 ?y)
            (Btwn$0 next$0 sk_l1$0 (read$0 next$0 sk_l1$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y)
            (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b$0) b$0)) (not (Btwn$0 next$0 b$0 ?y ?y))
            (= b$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 sk_l1$0) sk_l1$0))
            (not (Btwn$0 next$0 sk_l1$0 ?y ?y)) (= sk_l1$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_2$0) prv_2$0))
            (not (Btwn$0 next$0 prv_2$0 ?y ?y)) (= prv_2$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 b$0 (read$0 next$0 b$0) (read$0 next$0 b$0)) :named P6))

(assert (! (Btwn$0 next$0 sk_l1$0 (read$0 next$0 sk_l1$0) (read$0 next$0 sk_l1$0)) :named P7))

(assert (! (Btwn$0 next$0 prv_2$0 (read$0 next$0 prv_2$0) (read$0 next$0 prv_2$0)) :named P8))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 a$0) b$0) (not (= (read$0 next$0 b$0) a$0))
        (not (in$0 b$0 sk_?X_1$0)) (not (in$0 a$0 sk_?X_1$0)))) :named P9))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 a$0) sk_l1$0) (not (= (read$0 next$0 sk_l1$0) a$0))
        (not (in$0 sk_l1$0 sk_?X_1$0)) (not (in$0 a$0 sk_?X_1$0)))) :named P10))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 a$0) prv_2$0) (not (= (read$0 next$0 prv_2$0) a$0))
        (not (in$0 prv_2$0 sk_?X_1$0)) (not (in$0 a$0 sk_?X_1$0)))) :named P11))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) b$0) (not (= (read$0 next$0 b$0) sk_l2$0))
        (not (in$0 b$0 sk_?X_1$0)) (not (in$0 sk_l2$0 sk_?X_1$0)))) :named P12))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) sk_l2$0))
        (not (in$0 sk_l1$0 sk_?X_1$0)) (not (in$0 sk_l2$0 sk_?X_1$0)))) :named P13))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 sk_l2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2$0))
        (not (in$0 prv_2$0 sk_?X_1$0)) (not (in$0 sk_l2$0 sk_?X_1$0)))) :named P14))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 prv_2$0) b$0) (not (= (read$0 next$0 b$0) prv_2$0))
        (not (in$0 b$0 sk_?X_1$0)) (not (in$0 prv_2$0 sk_?X_1$0)))) :named P15))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) prv_2$0))
        (not (in$0 sk_l1$0 sk_?X_1$0)) (not (in$0 prv_2$0 sk_?X_1$0)))) :named P16))

(assert (! (or (not Axiom_1$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X_1$0)) (not (in$0 prv_2$0 sk_?X_1$0)))) :named P17))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 a$0) b$0) (not (= (read$0 next$0 b$0) a$0))
        (not (in$0 b$0 sk_?X$0)) (not (in$0 a$0 sk_?X$0)))) :named P18))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 a$0) sk_l1$0) (not (= (read$0 next$0 sk_l1$0) a$0))
        (not (in$0 sk_l1$0 sk_?X$0)) (not (in$0 a$0 sk_?X$0)))) :named P19))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 a$0) prv_2$0) (not (= (read$0 next$0 prv_2$0) a$0))
        (not (in$0 prv_2$0 sk_?X$0)) (not (in$0 a$0 sk_?X$0)))) :named P20))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) b$0) (not (= (read$0 next$0 b$0) sk_l2$0))
        (not (in$0 b$0 sk_?X$0)) (not (in$0 sk_l2$0 sk_?X$0)))) :named P21))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) sk_l2$0))
        (not (in$0 sk_l1$0 sk_?X$0)) (not (in$0 sk_l2$0 sk_?X$0)))) :named P22))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 sk_l2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) sk_l2$0))
        (not (in$0 prv_2$0 sk_?X$0)) (not (in$0 sk_l2$0 sk_?X$0)))) :named P23))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 prv_2$0) b$0) (not (= (read$0 next$0 b$0) prv_2$0))
        (not (in$0 b$0 sk_?X$0)) (not (in$0 prv_2$0 sk_?X$0)))) :named P24))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 prv_2$0) sk_l1$0)
        (not (= (read$0 next$0 sk_l1$0) prv_2$0))
        (not (in$0 sk_l1$0 sk_?X$0)) (not (in$0 prv_2$0 sk_?X$0)))) :named P25))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 prv_2$0) prv_2$0)
        (not (= (read$0 next$0 prv_2$0) prv_2$0))
        (not (in$0 prv_2$0 sk_?X$0)) (not (in$0 prv_2$0 sk_?X$0)))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P29))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P30))

(assert (! (= (read$0 next$0 null$0) null$0) :named P31))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P32))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P33))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) prv_2$0) (in$0 b$0 sk_?X_1$0))
             (and (= a$0 null$0) (= prv_2$0 b$0)))
         Axiom_1$0)
    (not (dlseg_struct$0 sk_?X_1$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0))) :named P34))

(assert (! (= prv_2$0 null$0) :named P35))

(assert (! (= sk_?X$0 FP$0) :named P36))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P37))

(assert (! (= sk_?X_1$0 (dlseg_domain$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0)) :named P38))

(assert (! (or
    (and (= (read$0 next$0 sk_l1$0) sk_l2$0) (in$0 sk_l1$0 sk_?X_1$0)
         (in$0 sk_l2$0 sk_?X_1$0) (not (= (read$0 prev$0 sk_l2$0) sk_l1$0)))
    (and (in$0 sk_l2$0 sk_FP$0) (not (in$0 sk_l2$0 FP$0)))
    (and
         (or (not (= (read$0 next$0 b$0) null$0))
             (not (= (read$0 prev$0 a$0) prv_2$0))
             (not (in$0 b$0 sk_?X_1$0)))
         (or (not (= a$0 null$0)) (not (= prv_2$0 b$0))))
    (not (Btwn$0 next$0 a$0 null$0 null$0))) :named P39))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P40))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X$0)))
         Axiom$0)
    (not (dlseg_struct$0 sk_?X$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P41))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P42))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P43))

(assert (! (= sk_?X$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P44))

(assert (! (dlseg_struct$0 sk_?X$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P45))

(assert (! (= sk_FP$0 sk_?X_1$0) :named P46))

(assert (! (not (in$0 null$0 Alloc$0)) :named P47))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0)))))) :named P48))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P49))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P50))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P51))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P52))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P53))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P54))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P55))

(check-sat)

(get-interpolants (and P2 P10 P26 P47 P42 P31 P19 P45 P24 P9 P14 P50 P39 P51 P35 P5 P7 P17 P53 P3 P41 P43 P49 P32 P40 P6 P55 P11) (and P38 P46 P23 P30 P34 P27 P1 P8 P37 P21 P28 P0 P20 P54 P36 P44 P13 P25 P15 P4 P33 P48 P29 P18 P22 P16 P12 P52))

(exit)