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
  tests/spl/sl/rec_concat.spl:20:4-13:A postcondition of procedure find_last might not hold at this return point
  tests/spl/sl/rec_concat.spl:11:10-40:Related location: This is the postcondition that might not hold
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
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun l_2$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun n_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?e_2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 n_2$0 ?y ?y)) (= n_2$0 ?y)
            (Btwn$0 next$0 n_2$0 (read$0 next$0 n_2$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 l_2$0 ?y ?y)) (= l_2$0 ?y)
            (Btwn$0 next$0 l_2$0 (read$0 next$0 l_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 n_2$0) n_2$0))
            (not (Btwn$0 next$0 n_2$0 ?y ?y)) (= n_2$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 l_2$0) l_2$0))
            (not (Btwn$0 next$0 l_2$0 ?y ?y)) (= l_2$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 n_2$0 (read$0 next$0 n_2$0) (read$0 next$0 n_2$0)) :named P4))

(assert (! (Btwn$0 next$0 l_2$0 (read$0 next$0 l_2$0) (read$0 next$0 l_2$0)) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P7))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_20$0 sk_?X_22$0))
                 (or (in$0 x sk_?X_20$0) (in$0 x sk_?X_22$0)))
            (and (not (in$0 x sk_?X_20$0)) (not (in$0 x sk_?X_22$0))
                 (not (in$0 x (union$0 sk_?X_20$0 sk_?X_22$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_20$0) (in$0 x sk_?X_22$0)
                 (in$0 x (intersection$0 sk_?X_20$0 sk_?X_22$0)))
            (and (or (not (in$0 x sk_?X_20$0)) (not (in$0 x sk_?X_22$0)))
                 (not (in$0 x (intersection$0 sk_?X_20$0 sk_?X_22$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P14))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P15))

(assert (! (= (read$0 next$0 null$0) null$0) :named P16))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P17))

(assert (! (or (Btwn$0 next$0 a$0 l_2$0 l_2$0)
    (not (lseg_struct$0 sk_?X_20$0 next$0 a$0 l_2$0))) :named P18))

(assert (! (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP$0)) :named P19))

(assert (! (= n_2$0 null$0) :named P20))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P21))

(assert (! (= sk_?X_18$0 sk_?X_19$0) :named P22))

(assert (! (= sk_?X_19$0 (lseg_domain$0 next$0 a$0 null$0)) :named P23))

(assert (! (lseg_struct$0 sk_?X_19$0 next$0 a$0 null$0) :named P24))

(assert (! (= sk_?X_20$0 (lseg_domain$0 next$0 a$0 l_2$0)) :named P25))

(assert (! (= sk_?X_22$0 sk_?X_21$0) :named P26))

(assert (! (or (in$0 sk_?e_2$0 (intersection$0 sk_?X_20$0 sk_?X_22$0))
    (and
         (in$0 sk_?e_2$0
           (union$0 (intersection$0 Alloc$0 FP$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (not (in$0 sk_?e_2$0 sk_?X_23$0)))
    (and (in$0 sk_?e_2$0 sk_?X_23$0)
         (not
              (in$0 sk_?e_2$0
                (union$0 (intersection$0 Alloc$0 FP$0)
                  (setminus$0 Alloc$0 Alloc$0)))))
    (not (= (read$0 next$0 l_2$0) null$0))
    (not (Btwn$0 next$0 a$0 l_2$0 l_2$0))) :named P27))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 a$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a$0 null$0)))))) :named P28))

(assert (! (or (Btwn$0 next$0 a$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_19$0 next$0 a$0 null$0))) :named P29))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P30))

(assert (! (= l_2$0 a$0) :named P31))

(assert (! (= n_2$0 (read$0 next$0 a$0)) :named P32))

(assert (! (= emptyset$0 emptyset$0) :named P33))

(assert (! (= sk_?X_18$0 FP$0) :named P34))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P35))

(assert (! (not (= a$0 null$0)) :named P36))

(assert (! (= sk_?X_21$0 (setenum$0 l_2$0)) :named P37))

(assert (! (= sk_?X_23$0 (union$0 sk_?X_20$0 sk_?X_22$0)) :named P38))

(assert (! (not (in$0 null$0 Alloc$0)) :named P39))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 l_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 a$0 l_2$0))
                 (not (= l1 l_2$0)))
            (and (or (= l1 l_2$0) (not (Btwn$0 next$0 a$0 l1 l_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a$0 l_2$0)))))) :named P40))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P41))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P42))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P43))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P44))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P45))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P46))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P47))

(check-sat)

(get-interpolants (and P22 P17 P24 P12 P37 P10 P30 P26 P13 P45 P47 P6 P0 P16 P4 P42 P21 P5 P33 P18 P39 P43 P23 P2) (and P41 P8 P46 P38 P25 P15 P7 P29 P14 P28 P31 P40 P3 P11 P9 P19 P27 P34 P32 P35 P44 P20 P1 P36))

(exit)