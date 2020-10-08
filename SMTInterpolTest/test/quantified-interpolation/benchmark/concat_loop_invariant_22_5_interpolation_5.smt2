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
  tests/spl/sl/sl_concat.spl:22:5-6:An invariant might not be maintained by a loop in procedure concat
  tests/spl/sl/sl_concat.spl:19:16-67:Related location: This is the loop invariant that might not be maintained
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
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_2$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_50$0 () SetLoc)
(declare-fun sk_?X_51$0 () SetLoc)
(declare-fun sk_?X_52$0 () SetLoc)
(declare-fun sk_?X_53$0 () SetLoc)
(declare-fun sk_?X_54$0 () SetLoc)
(declare-fun sk_?X_55$0 () SetLoc)
(declare-fun sk_?X_56$0 () SetLoc)
(declare-fun sk_?X_57$0 () SetLoc)
(declare-fun sk_?e_3$0 () Loc)
(declare-fun sk_FP_1$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y)
            (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_init$0) curr_init$0))
            (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0)
  (read$0 next$0 curr_init$0)) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_52$0 sk_?X_51$0))
                 (or (in$0 x sk_?X_52$0) (in$0 x sk_?X_51$0)))
            (and (not (in$0 x sk_?X_52$0)) (not (in$0 x sk_?X_51$0))
                 (not (in$0 x (union$0 sk_?X_52$0 sk_?X_51$0)))))) :named P7))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_57$0 sk_?X_55$0))
                 (or (in$0 x sk_?X_57$0) (in$0 x sk_?X_55$0)))
            (and (not (in$0 x sk_?X_57$0)) (not (in$0 x sk_?X_55$0))
                 (not (in$0 x (union$0 sk_?X_57$0 sk_?X_55$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_52$0) (in$0 x sk_?X_51$0)
                 (in$0 x (intersection$0 sk_?X_52$0 sk_?X_51$0)))
            (and (or (not (in$0 x sk_?X_52$0)) (not (in$0 x sk_?X_51$0)))
                 (not (in$0 x (intersection$0 sk_?X_52$0 sk_?X_51$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_57$0) (in$0 x sk_?X_55$0)
                 (in$0 x (intersection$0 sk_?X_57$0 sk_?X_55$0)))
            (and (or (not (in$0 x sk_?X_57$0)) (not (in$0 x sk_?X_55$0)))
                 (not (in$0 x (intersection$0 sk_?X_57$0 sk_?X_55$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P12))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P13))

(assert (! (= (read$0 next$0 null$0) null$0) :named P14))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P15))

(assert (! (or (Btwn$0 next$0 a_2$0 curr_5$0 curr_5$0)
    (not (lseg_struct$0 sk_?X_57$0 next$0 a_2$0 curr_5$0))) :named P16))

(assert (! (or (Btwn$0 next$0 curr_5$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_55$0 next$0 curr_5$0 null$0))) :named P17))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P18))

(assert (! (= curr_4$0 curr_init$0) :named P19))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P20))

(assert (! (= emptyset$0 (intersection$0 sk_?X_52$0 sk_?X_51$0)) :named P21))

(assert (! (= sk_?X_50$0 FP$0) :named P22))

(assert (! (= sk_?X_52$0 sk_?X_53$0) :named P23))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P24))

(assert (! (lseg_struct$0 sk_?X_53$0 next$0 a_init$0 curr_init$0) :named P25))

(assert (! (= sk_?X_54$0 (union$0 sk_?X_56$0 sk_?X_55$0)) :named P26))

(assert (! (= sk_?X_56$0 sk_?X_57$0) :named P27))

(assert (! (= sk_FP_1$0 sk_?X_54$0) :named P28))

(assert (! (not (= (read$0 next$0 curr_4$0) null$0)) :named P29))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_2$0 l1 curr_5$0)
                 (in$0 l1 (lseg_domain$0 next$0 a_2$0 curr_5$0))
                 (not (= l1 curr_5$0)))
            (and (or (= l1 curr_5$0) (not (Btwn$0 next$0 a_2$0 l1 curr_5$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a_2$0 curr_5$0)))))) :named P30))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_5$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_5$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_5$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_5$0 null$0)))))) :named P31))

(assert (! (or (Btwn$0 next$0 a_init$0 curr_init$0 curr_init$0)
    (not (lseg_struct$0 sk_?X_53$0 next$0 a_init$0 curr_init$0))) :named P32))

(assert (! (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_51$0 next$0 curr_init$0 null$0))) :named P33))

(assert (! (= a_2$0 a_init$0) :named P34))

(assert (! (= curr_5$0 (read$0 next$0 curr_4$0)) :named P35))

(assert (! (= emptyset$0 emptyset$0) :named P36))

(assert (! (= sk_?X_50$0 (union$0 sk_?X_52$0 sk_?X_51$0)) :named P37))

(assert (! (= sk_?X_51$0 (lseg_domain$0 next$0 curr_init$0 null$0)) :named P38))

(assert (! (= sk_?X_53$0 (lseg_domain$0 next$0 a_init$0 curr_init$0)) :named P39))

(assert (! (lseg_struct$0 sk_?X_51$0 next$0 curr_init$0 null$0) :named P40))

(assert (! (not (= curr_init$0 null$0)) :named P41))

(assert (! (= sk_?X_55$0 (lseg_domain$0 next$0 curr_5$0 null$0)) :named P42))

(assert (! (= sk_?X_57$0 (lseg_domain$0 next$0 a_2$0 curr_5$0)) :named P43))

(assert (! (or (= curr_5$0 null$0)
    (in$0 sk_?e_3$0 (intersection$0 sk_?X_56$0 sk_?X_55$0))
    (and (in$0 sk_?e_3$0 sk_FP_1$0) (not (in$0 sk_?e_3$0 FP$0)))
    (not (Btwn$0 next$0 a_2$0 curr_5$0 curr_5$0))
    (not (Btwn$0 next$0 curr_5$0 null$0 null$0))) :named P44))

(assert (! (not (in$0 null$0 Alloc$0)) :named P45))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_init$0 l1 curr_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 a_init$0 curr_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 a_init$0 l1 curr_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a_init$0 curr_init$0)))))) :named P46))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))) :named P47))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P48))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P49))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P50))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P51))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P52))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P53))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P54))

(check-sat)

(get-interpolants (and P51 P43 P14 P30 P21 P7 P10 P15 P2 P49 P46 P24 P6 P53 P47 P25 P48 P35 P40 P1 P41 P22 P54 P37 P19 P0 P29 P17) (and P13 P42 P32 P4 P45 P34 P3 P16 P8 P36 P50 P23 P12 P52 P31 P18 P33 P11 P39 P9 P27 P44 P28 P26 P5 P38 P20))

(exit)