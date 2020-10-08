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
  tests/spl/dl/dl_dispose.spl:22:4-13:This deallocation might be unsafe
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
(declare-fun Axiom_6$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_2$0 () Loc)
(declare-fun a_3$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun b_2$0 () Loc)
(declare-fun b_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_5$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun sk_?X_6$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y)
            (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_5$0 ?y ?y)) (= prv_5$0 ?y)
            (Btwn$0 next$0 prv_5$0 (read$0 next$0 prv_5$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b_init$0) b_init$0))
            (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_5$0) prv_5$0))
            (not (Btwn$0 next$0 prv_5$0 ?y ?y)) (= prv_5$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P6))

(assert (! (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) (read$0 next$0 b_init$0)) :named P7))

(assert (! (Btwn$0 next$0 prv_5$0 (read$0 next$0 prv_5$0) (read$0 next$0 prv_5$0)) :named P8))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0)) (not (in$0 null$0 sk_?X_6$0))
        (not (in$0 null$0 sk_?X_6$0)))) :named P9))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_6$0)) (not (in$0 null$0 sk_?X_6$0)))) :named P10))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 null$0) prv_5$0)
        (not (= (read$0 next$0 prv_5$0) null$0))
        (not (in$0 prv_5$0 sk_?X_6$0)) (not (in$0 null$0 sk_?X_6$0)))) :named P11))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_5$0) null$0)
        (not (= (read$0 next$0 null$0) prv_5$0))
        (not (in$0 null$0 sk_?X_6$0)) (not (in$0 prv_5$0 sk_?X_6$0)))) :named P12))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_5$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) prv_5$0))
        (not (in$0 b_init$0 sk_?X_6$0)) (not (in$0 prv_5$0 sk_?X_6$0)))) :named P13))

(assert (! (or (not Axiom_6$0)
    (or (= (read$0 prev$0 prv_5$0) prv_5$0)
        (not (= (read$0 next$0 prv_5$0) prv_5$0))
        (not (in$0 prv_5$0 sk_?X_6$0)) (not (in$0 prv_5$0 sk_?X_6$0)))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P15))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P16))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P17))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P18))

(assert (! (= (read$0 next$0 null$0) null$0) :named P19))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P20))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P21))

(assert (! (or
    (and (Btwn$0 next$0 a_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_init$0) null$0)
                  (= (read$0 prev$0 a_init$0) prv_init$0)
                  (in$0 b_init$0 sk_?X_6$0))
             (and (= a_init$0 null$0) (= prv_init$0 b_init$0)))
         Axiom_6$0)
    (not
         (dlseg_struct$0 sk_?X_6$0 next$0 prev$0 a_init$0 prv_init$0 null$0
           b_init$0))) :named P22))

(assert (! (= a_2$0 a_init$0) :named P23))

(assert (! (= b_2$0 b_init$0) :named P24))

(assert (! (= prv_5$0 a_2$0) :named P25))

(assert (! (= sk_?X_6$0 FP$0) :named P26))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P27))

(assert (! (not (= a_2$0 null$0)) :named P28))

(assert (! (not (in$0 prv_5$0 FP$0)) :named P29))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P30))

(assert (! (= a_3$0 (read$0 next$0 a_2$0)) :named P31))

(assert (! (= prv_4$0 prv_init$0) :named P32))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P33))

(assert (! (= sk_?X_6$0
  (dlseg_domain$0 next$0 prev$0 a_init$0 prv_init$0 null$0 b_init$0)) :named P34))

(assert (! (dlseg_struct$0 sk_?X_6$0 next$0 prev$0 a_init$0 prv_init$0 null$0 b_init$0) :named P35))

(assert (! (not (in$0 null$0 Alloc$0)) :named P36))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a_init$0 prv_init$0 null$0
                     b_init$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a_init$0 prv_init$0
                          null$0 b_init$0)))))) :named P37))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P38))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P39))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P40))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P41))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P42))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P43))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P44))

(check-sat)

(get-interpolants (and P25 P30 P31 P36 P5 P1 P21 P16 P37 P40 P8 P28 P15 P13 P3 P18 P24 P41 P26 P0 P2 P22 P39) (and P7 P11 P32 P44 P20 P34 P43 P17 P42 P12 P38 P19 P33 P27 P4 P9 P10 P6 P35 P23 P14 P29))

(exit)