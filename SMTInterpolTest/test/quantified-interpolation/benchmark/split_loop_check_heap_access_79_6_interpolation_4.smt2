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
  tests/spl/sls/sls_merge_sort.spl:79:6-24:Possible heap access through null or dangling reference
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
(declare-fun FP_Caller_5$0 () SetLoc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_276$0 () SetLoc)
(declare-fun sk_?X_277$0 () SetLoc)
(declare-fun sk_?X_278$0 () SetLoc)
(declare-fun sk_?X_279$0 () SetLoc)
(declare-fun sk_?X_280$0 () SetLoc)
(declare-fun y_8$0 () Loc)
(declare-fun y_init$0 () Loc)
(declare-fun z_4$0 () Loc)
(declare-fun z_5$0 () Loc)
(declare-fun z_init$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y)
            (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 z_init$0 ?y ?y)) (= z_init$0 ?y)
            (Btwn$0 next$0 z_init$0 (read$0 next$0 z_init$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_init$0) curr_init$0))
            (not (Btwn$0 next$0 curr_init$0 ?y ?y)) (= curr_init$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 z_init$0) z_init$0))
            (not (Btwn$0 next$0 z_init$0 ?y ?y)) (= z_init$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P6))

(assert (! (Btwn$0 next$0 curr_init$0 (read$0 next$0 curr_init$0)
  (read$0 next$0 curr_init$0)) :named P7))

(assert (! (Btwn$0 next$0 z_init$0 (read$0 next$0 z_init$0) (read$0 next$0 z_init$0)) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_278$0 sk_?X_277$0))
                 (or (in$0 x sk_?X_278$0) (in$0 x sk_?X_277$0)))
            (and (not (in$0 x sk_?X_278$0)) (not (in$0 x sk_?X_277$0))
                 (not (in$0 x (union$0 sk_?X_278$0 sk_?X_277$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_280$0 sk_?X_279$0))
                 (or (in$0 x sk_?X_280$0) (in$0 x sk_?X_279$0)))
            (and (not (in$0 x sk_?X_280$0)) (not (in$0 x sk_?X_279$0))
                 (not (in$0 x (union$0 sk_?X_280$0 sk_?X_279$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_280$0) (in$0 x sk_?X_279$0)
                 (in$0 x (intersection$0 sk_?X_280$0 sk_?X_279$0)))
            (and (or (not (in$0 x sk_?X_280$0)) (not (in$0 x sk_?X_279$0)))
                 (not (in$0 x (intersection$0 sk_?X_280$0 sk_?X_279$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_278$0) (in$0 x sk_?X_277$0)
                 (in$0 x (intersection$0 sk_?X_278$0 sk_?X_277$0)))
            (and (or (not (in$0 x sk_?X_278$0)) (not (in$0 x sk_?X_277$0)))
                 (not (in$0 x (intersection$0 sk_?X_278$0 sk_?X_277$0)))))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P15))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P16))

(assert (! (= (read$0 next$0 null$0) null$0) :named P17))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P18))

(assert (! (or (Btwn$0 next$0 y_init$0 z_init$0 z_init$0)
    (not (lseg_struct$0 sk_?X_280$0 next$0 y_init$0 z_init$0))) :named P19))

(assert (! (= FP_Caller_5$0 (setminus$0 FP_Caller$0 FP$0)) :named P20))

(assert (! (= curr_5$0 (read$0 next$0 curr_4$0)) :named P21))

(assert (! (= z_4$0 z_init$0) :named P22))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P23))

(assert (! (= emptyset$0 (intersection$0 sk_?X_280$0 sk_?X_279$0)) :named P24))

(assert (! (= sk_?X_276$0 FP$0) :named P25))

(assert (! (= sk_?X_278$0 (union$0 sk_?X_280$0 sk_?X_279$0)) :named P26))

(assert (! (= sk_?X_280$0 (lseg_domain$0 next$0 y_init$0 z_init$0)) :named P27))

(assert (! (lseg_struct$0 sk_?X_277$0 next$0 curr_init$0 null$0) :named P28))

(assert (! (lseg_struct$0 sk_?X_280$0 next$0 y_init$0 z_init$0) :named P29))

(assert (! (not (= curr_5$0 null$0)) :named P30))

(assert (! (not (in$0 curr_5$0 FP$0)) :named P31))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y_init$0 l1 z_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 y_init$0 z_init$0))
                 (not (= l1 z_init$0)))
            (and
                 (or (= l1 z_init$0)
                     (not (Btwn$0 next$0 y_init$0 l1 z_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 y_init$0 z_init$0)))))) :named P32))

(assert (! (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_277$0 next$0 curr_init$0 null$0))) :named P33))

(assert (! (or (Btwn$0 next$0 z_init$0 curr_init$0 curr_init$0)
    (not (lseg_struct$0 sk_?X_279$0 next$0 z_init$0 curr_init$0))) :named P34))

(assert (! (= curr_4$0 curr_init$0) :named P35))

(assert (! (= y_8$0 y_init$0) :named P36))

(assert (! (= z_5$0 (read$0 next$0 z_4$0)) :named P37))

(assert (! (= emptyset$0 (intersection$0 sk_?X_278$0 sk_?X_277$0)) :named P38))

(assert (! (= sk_?X_276$0 (union$0 sk_?X_278$0 sk_?X_277$0)) :named P39))

(assert (! (= sk_?X_277$0 (lseg_domain$0 next$0 curr_init$0 null$0)) :named P40))

(assert (! (= sk_?X_279$0 (lseg_domain$0 next$0 z_init$0 curr_init$0)) :named P41))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P42))

(assert (! (lseg_struct$0 sk_?X_279$0 next$0 z_init$0 curr_init$0) :named P43))

(assert (! (not (= curr_4$0 null$0)) :named P44))

(assert (! (not (in$0 null$0 Alloc$0)) :named P45))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))) :named P46))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 z_init$0 l1 curr_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 z_init$0 curr_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 z_init$0 l1 curr_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 z_init$0 curr_init$0)))))) :named P47))

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

(get-interpolants (and P9 P18 P43 P50 P39 P34 P33 P46 P23 P14 P17 P7 P13 P28 P49 P47 P54 P8 P12 P11 P42 P53 P15 P30 P20 P22 P51 P35) (and P41 P24 P40 P37 P26 P31 P29 P38 P6 P27 P19 P48 P5 P0 P16 P25 P52 P45 P1 P2 P21 P4 P3 P36 P44 P10 P32))

(exit)