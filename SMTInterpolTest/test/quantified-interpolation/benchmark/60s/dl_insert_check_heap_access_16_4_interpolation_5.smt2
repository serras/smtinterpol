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
  tests/spl/dl/dl_insert.spl:16:4-21:Possible heap access through null or dangling reference
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
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun elt$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun sk_?X$0 () SetLoc)
(declare-fun sk_?X_1$0 () SetLoc)
(declare-fun sk_?X_2$0 () SetLoc)
(declare-fun sk_?X_3$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b$0 ?y ?y)) (= b$0 ?y)
            (Btwn$0 next$0 b$0 (read$0 next$0 b$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 elt$0) elt$0))
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b$0) b$0)) (not (Btwn$0 next$0 b$0 ?y ?y))
            (= b$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) (read$0 next$0 elt$0)) :named P6))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P7))

(assert (! (Btwn$0 next$0 b$0 (read$0 next$0 b$0) (read$0 next$0 b$0)) :named P8))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) elt$0)
        (not (= (read$0 next$0 elt$0) null$0)) (not (in$0 elt$0 sk_?X_3$0))
        (not (in$0 null$0 sk_?X_3$0)))) :named P9))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0)) (not (in$0 null$0 sk_?X_3$0))
        (not (in$0 null$0 sk_?X_3$0)))) :named P10))

(assert (! (or (not Axiom$0)
    (or (= (read$0 prev$0 null$0) b$0) (not (= (read$0 next$0 b$0) null$0))
        (not (in$0 b$0 sk_?X_3$0)) (not (in$0 null$0 sk_?X_3$0)))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_3$0 sk_?X_1$0))
                 (or (in$0 x sk_?X_3$0) (in$0 x sk_?X_1$0)))
            (and (not (in$0 x sk_?X_3$0)) (not (in$0 x sk_?X_1$0))
                 (not (in$0 x (union$0 sk_?X_3$0 sk_?X_1$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_3$0) (in$0 x sk_?X_1$0)
                 (in$0 x (intersection$0 sk_?X_3$0 sk_?X_1$0)))
            (and (or (not (in$0 x sk_?X_3$0)) (not (in$0 x sk_?X_1$0)))
                 (not (in$0 x (intersection$0 sk_?X_3$0 sk_?X_1$0)))))) :named P15))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P16))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P17))

(assert (! (= (read$0 next$0 null$0) null$0) :named P18))

(assert (! (= (read$0 prev$0 null$0) null$0) :named P19))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P20))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P21))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P22))

(assert (! (= emptyset$0 emptyset$0) :named P23))

(assert (! (= sk_?X$0 (union$0 sk_?X_3$0 sk_?X_1$0)) :named P24))

(assert (! (= sk_?X_1$0 sk_?X_2$0) :named P25))

(assert (! (= sk_?X_3$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P26))

(assert (! (dlseg_struct$0 sk_?X_3$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P27))

(assert (! (not (in$0 elt$0 FP$0)) :named P28))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_3$0)))
         Axiom$0)
    (not (dlseg_struct$0 sk_?X_3$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P29))

(assert (! (= a$0 null$0) :named P30))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P31))

(assert (! (= emptyset$0 (intersection$0 sk_?X_3$0 sk_?X_1$0)) :named P32))

(assert (! (= sk_?X$0 FP$0) :named P33))

(assert (! (= sk_?X_2$0 (setenum$0 elt$0)) :named P34))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P35))

(assert (! (not (in$0 null$0 Alloc$0)) :named P36))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P37))

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

(get-interpolants (and P20 P36 P27 P11 P4 P40 P30 P37 P9 P16 P1 P29 P35 P25 P44 P19 P10 P23 P33 P7 P34 P21 P15) (and P38 P3 P18 P14 P12 P42 P17 P0 P41 P24 P32 P43 P6 P26 P5 P39 P28 P2 P22 P31 P8 P13))

(exit)