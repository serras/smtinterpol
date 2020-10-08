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
  tests/spl/sl/sl_filter.spl:27:8-34:Possible heap access through null or dangling reference
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
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun nondet_3$0 () Bool)
(declare-fun nondet_init$0 () Bool)
(declare-fun old_curr_2$0 () Loc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun res_3$0 () Loc)
(declare-fun res_init$0 () Loc)
(declare-fun sk_?X_35$0 () SetLoc)
(declare-fun sk_?X_36$0 () SetLoc)
(declare-fun sk_?X_37$0 () SetLoc)
(declare-fun sk_?X_38$0 () SetLoc)
(declare-fun sk_?X_39$0 () SetLoc)
(declare-fun sk_?X_40$0 () SetLoc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun sk_?X_42$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y)
            (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P6))

(assert (! (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0)
  (read$0 next$0 prv_init$0)) :named P7))

(assert (! (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0)
  (read$0 next$0 old_curr_4$0)) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_39$0 sk_?X_37$0))
                 (or (in$0 x sk_?X_39$0) (in$0 x sk_?X_37$0)))
            (and (not (in$0 x sk_?X_39$0)) (not (in$0 x sk_?X_37$0))
                 (not (in$0 x (union$0 sk_?X_39$0 sk_?X_37$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_38$0 sk_?X_37$0))
                 (or (in$0 x sk_?X_38$0) (in$0 x sk_?X_37$0)))
            (and (not (in$0 x sk_?X_38$0)) (not (in$0 x sk_?X_37$0))
                 (not (in$0 x (union$0 sk_?X_38$0 sk_?X_37$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_42$0 sk_?X_41$0))
                 (or (in$0 x sk_?X_42$0) (in$0 x sk_?X_41$0)))
            (and (not (in$0 x sk_?X_42$0)) (not (in$0 x sk_?X_41$0))
                 (not (in$0 x (union$0 sk_?X_42$0 sk_?X_41$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_38$0) (in$0 x sk_?X_37$0)
                 (in$0 x (intersection$0 sk_?X_38$0 sk_?X_37$0)))
            (and (or (not (in$0 x sk_?X_38$0)) (not (in$0 x sk_?X_37$0)))
                 (not (in$0 x (intersection$0 sk_?X_38$0 sk_?X_37$0)))))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_39$0) (in$0 x sk_?X_37$0)
                 (in$0 x (intersection$0 sk_?X_39$0 sk_?X_37$0)))
            (and (or (not (in$0 x sk_?X_39$0)) (not (in$0 x sk_?X_37$0)))
                 (not (in$0 x (intersection$0 sk_?X_39$0 sk_?X_37$0)))))) :named P15))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_42$0) (in$0 x sk_?X_41$0)
                 (in$0 x (intersection$0 sk_?X_42$0 sk_?X_41$0)))
            (and (or (not (in$0 x sk_?X_42$0)) (not (in$0 x sk_?X_41$0)))
                 (not (in$0 x (intersection$0 sk_?X_42$0 sk_?X_41$0)))))) :named P16))

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

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P20))

(assert (! (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_37$0 next$0 curr_init$0 null$0))) :named P21))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P22))

(assert (! (= curr_5$0 (read$0 next$0 curr_4$0)) :named P23))

(assert (! (= old_curr_2$0 old_curr_init$0) :named P24))

(assert (! (= prv_4$0 prv_init$0) :named P25))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P26))

(assert (! (= sk_?X_35$0 (union$0 sk_?X_39$0 sk_?X_37$0)) :named P27))

(assert (! (= sk_?X_37$0 (lseg_domain$0 next$0 curr_init$0 null$0)) :named P28))

(assert (! (= sk_?X_39$0 (union$0 sk_?X_42$0 sk_?X_40$0)) :named P29))

(assert (! (= sk_?X_41$0 (setenum$0 prv_init$0)) :named P30))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P31))

(assert (! (not (= curr_4$0 null$0)) :named P32))

(assert (! (not (in$0 null$0 Alloc$0)) :named P33))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))) :named P34))

(assert (! (or (Btwn$0 next$0 res_init$0 prv_init$0 prv_init$0)
    (not (lseg_struct$0 sk_?X_42$0 next$0 res_init$0 prv_init$0))) :named P35))

(assert (! (= curr_4$0 curr_init$0) :named P36))

(assert (! (= nondet_2$0 nondet_init$0) :named P37))

(assert (! (= old_curr_4$0 curr_4$0) :named P38))

(assert (! (= res_3$0 res_init$0) :named P39))

(assert (! nondet_3$0 :named P40))

(assert (! (= sk_?X_36$0 (union$0 sk_?X_38$0 sk_?X_37$0)) :named P41))

(assert (! (= sk_?X_38$0 emptyset$0) :named P42))

(assert (! (= sk_?X_40$0 sk_?X_41$0) :named P43))

(assert (! (= sk_?X_42$0 (lseg_domain$0 next$0 res_init$0 prv_init$0)) :named P44))

(assert (! (or
    (and (= (read$0 next$0 prv_init$0) curr_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_39$0 sk_?X_37$0))
         (= emptyset$0 (intersection$0 sk_?X_42$0 sk_?X_40$0))
         (= sk_?X_35$0 FP$0)
         (lseg_struct$0 sk_?X_37$0 next$0 curr_init$0 null$0)
         (lseg_struct$0 sk_?X_42$0 next$0 res_init$0 prv_init$0))
    (and (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_38$0 sk_?X_37$0))
         (= prv_init$0 null$0) (= res_init$0 curr_init$0) (= sk_?X_36$0 FP$0)
         (lseg_struct$0 sk_?X_37$0 next$0 curr_init$0 null$0))) :named P45))

(assert (! (not (= prv_4$0 null$0)) :named P46))

(assert (! (not (in$0 prv_4$0 FP$0)) :named P47))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 res_init$0 l1 prv_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 res_init$0 prv_init$0))
                 (not (= l1 prv_init$0)))
            (and
                 (or (= l1 prv_init$0)
                     (not (Btwn$0 next$0 res_init$0 l1 prv_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 res_init$0 prv_init$0)))))) :named P48))

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

(get-interpolants (and P30 P14 P5 P41 P25 P0 P51 P43 P52 P10 P37 P9 P21 P18 P19 P38 P45 P50 P27 P54 P23 P17 P31 P2 P39 P11 P42 P15) (and P33 P26 P55 P32 P36 P29 P1 P35 P20 P8 P12 P44 P47 P49 P53 P4 P16 P7 P24 P46 P3 P40 P6 P13 P34 P48 P22 P28))

(exit)