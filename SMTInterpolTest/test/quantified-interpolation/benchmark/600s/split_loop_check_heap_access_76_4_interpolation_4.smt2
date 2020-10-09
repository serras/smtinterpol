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
  tests/spl/sls/sls_merge_sort.spl:76:4-16:Possible heap access through null or dangling reference
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
(declare-fun curr_init$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_266$0 () SetLoc)
(declare-fun sk_?X_267$0 () SetLoc)
(declare-fun sk_?X_268$0 () SetLoc)
(declare-fun sk_?X_269$0 () SetLoc)
(declare-fun sk_?X_270$0 () SetLoc)
(declare-fun y_8$0 () Loc)
(declare-fun y_init$0 () Loc)
(declare-fun z_4$0 () Loc)
(declare-fun z_init$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P1))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P2))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P3))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_268$0 sk_?X_267$0))
                 (or (in$0 x sk_?X_268$0) (in$0 x sk_?X_267$0)))
            (and (not (in$0 x sk_?X_268$0)) (not (in$0 x sk_?X_267$0))
                 (not (in$0 x (union$0 sk_?X_268$0 sk_?X_267$0)))))) :named P4))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_270$0 sk_?X_269$0))
                 (or (in$0 x sk_?X_270$0) (in$0 x sk_?X_269$0)))
            (and (not (in$0 x sk_?X_270$0)) (not (in$0 x sk_?X_269$0))
                 (not (in$0 x (union$0 sk_?X_270$0 sk_?X_269$0)))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_270$0) (in$0 x sk_?X_269$0)
                 (in$0 x (intersection$0 sk_?X_270$0 sk_?X_269$0)))
            (and (or (not (in$0 x sk_?X_270$0)) (not (in$0 x sk_?X_269$0)))
                 (not (in$0 x (intersection$0 sk_?X_270$0 sk_?X_269$0)))))) :named P7))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_268$0) (in$0 x sk_?X_267$0)
                 (in$0 x (intersection$0 sk_?X_268$0 sk_?X_267$0)))
            (and (or (not (in$0 x sk_?X_268$0)) (not (in$0 x sk_?X_267$0)))
                 (not (in$0 x (intersection$0 sk_?X_268$0 sk_?X_267$0)))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P9))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P10))

(assert (! (= (read$0 next$0 null$0) null$0) :named P11))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P12))

(assert (! (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_267$0 next$0 curr_init$0 null$0))) :named P13))

(assert (! (or (Btwn$0 next$0 z_init$0 curr_init$0 curr_init$0)
    (not (lseg_struct$0 sk_?X_269$0 next$0 z_init$0 curr_init$0))) :named P14))

(assert (! (= curr_4$0 curr_init$0) :named P15))

(assert (! (= z_4$0 z_init$0) :named P16))

(assert (! (= emptyset$0 (intersection$0 sk_?X_268$0 sk_?X_267$0)) :named P17))

(assert (! (= sk_?X_266$0 (union$0 sk_?X_268$0 sk_?X_267$0)) :named P18))

(assert (! (= sk_?X_267$0 (lseg_domain$0 next$0 curr_init$0 null$0)) :named P19))

(assert (! (= sk_?X_269$0 (lseg_domain$0 next$0 z_init$0 curr_init$0)) :named P20))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P21))

(assert (! (lseg_struct$0 sk_?X_269$0 next$0 z_init$0 curr_init$0) :named P22))

(assert (! (not (= curr_4$0 null$0)) :named P23))

(assert (! (not (in$0 z_4$0 FP$0)) :named P24))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y_init$0 l1 z_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 y_init$0 z_init$0))
                 (not (= l1 z_init$0)))
            (and
                 (or (= l1 z_init$0)
                     (not (Btwn$0 next$0 y_init$0 l1 z_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 y_init$0 z_init$0)))))) :named P25))

(assert (! (or (Btwn$0 next$0 y_init$0 z_init$0 z_init$0)
    (not (lseg_struct$0 sk_?X_270$0 next$0 y_init$0 z_init$0))) :named P26))

(assert (! (= FP_Caller_5$0 (setminus$0 FP_Caller$0 FP$0)) :named P27))

(assert (! (= y_8$0 y_init$0) :named P28))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P29))

(assert (! (= emptyset$0 (intersection$0 sk_?X_270$0 sk_?X_269$0)) :named P30))

(assert (! (= sk_?X_266$0 FP$0) :named P31))

(assert (! (= sk_?X_268$0 (union$0 sk_?X_270$0 sk_?X_269$0)) :named P32))

(assert (! (= sk_?X_270$0 (lseg_domain$0 next$0 y_init$0 z_init$0)) :named P33))

(assert (! (lseg_struct$0 sk_?X_267$0 next$0 curr_init$0 null$0) :named P34))

(assert (! (lseg_struct$0 sk_?X_270$0 next$0 y_init$0 z_init$0) :named P35))

(assert (! (not (in$0 null$0 Alloc$0)) :named P36))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))) :named P37))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 z_init$0 l1 curr_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 z_init$0 curr_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 z_init$0 l1 curr_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 z_init$0 curr_init$0)))))) :named P38))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P39))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P40))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P41))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P42))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P43))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P44))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P45))

(check-sat)

(get-interpolants (and P20 P15 P22 P12 P26 P31 P14 P18 P24 P21 P23 P40 P0 P27 P32 P11 P41 P43 P7 P5 P29 P9 P28) (and P25 P2 P37 P30 P45 P44 P3 P39 P36 P13 P4 P16 P38 P6 P1 P35 P17 P8 P33 P42 P34 P10 P19))

(exit)