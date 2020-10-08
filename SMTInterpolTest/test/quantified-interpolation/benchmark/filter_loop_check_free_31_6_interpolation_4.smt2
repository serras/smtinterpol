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
  tests/spl/sl/sl_filter.spl:31:6-20:This deallocation might be unsafe
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
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
(declare-fun next_2$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun nondet_3$0 () Bool)
(declare-fun nondet_init$0 () Bool)
(declare-fun old_curr_2$0 () Loc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun res_3$0 () Loc)
(declare-fun res_4$0 () Loc)
(declare-fun res_init$0 () Loc)
(declare-fun sk_?X_59$0 () SetLoc)
(declare-fun sk_?X_60$0 () SetLoc)
(declare-fun sk_?X_61$0 () SetLoc)
(declare-fun sk_?X_62$0 () SetLoc)
(declare-fun sk_?X_63$0 () SetLoc)
(declare-fun sk_?X_64$0 () SetLoc)
(declare-fun sk_?X_65$0 () SetLoc)
(declare-fun sk_?X_66$0 () SetLoc)

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
        (or (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 prv_init$0) prv_init$0))
            (not (Btwn$0 next$0 prv_init$0 ?y ?y)) (= prv_init$0 ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 null$0) null$0))
            (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y))) :named P7))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P8))

(assert (! (Btwn$0 next$0 prv_init$0 (read$0 next$0 prv_init$0)
  (read$0 next$0 prv_init$0)) :named P9))

(assert (! (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0)
  (read$0 next$0 old_curr_4$0)) :named P10))

(assert (! (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) (read$0 next_2$0 null$0)) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_63$0 sk_?X_61$0))
                 (or (in$0 x sk_?X_63$0) (in$0 x sk_?X_61$0)))
            (and (not (in$0 x sk_?X_63$0)) (not (in$0 x sk_?X_61$0))
                 (not (in$0 x (union$0 sk_?X_63$0 sk_?X_61$0)))))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_62$0 sk_?X_61$0))
                 (or (in$0 x sk_?X_62$0) (in$0 x sk_?X_61$0)))
            (and (not (in$0 x sk_?X_62$0)) (not (in$0 x sk_?X_61$0))
                 (not (in$0 x (union$0 sk_?X_62$0 sk_?X_61$0)))))) :named P15))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_66$0 sk_?X_64$0))
                 (or (in$0 x sk_?X_66$0) (in$0 x sk_?X_64$0)))
            (and (not (in$0 x sk_?X_66$0)) (not (in$0 x sk_?X_64$0))
                 (not (in$0 x (union$0 sk_?X_66$0 sk_?X_64$0)))))) :named P16))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_62$0) (in$0 x sk_?X_61$0)
                 (in$0 x (intersection$0 sk_?X_62$0 sk_?X_61$0)))
            (and (or (not (in$0 x sk_?X_62$0)) (not (in$0 x sk_?X_61$0)))
                 (not (in$0 x (intersection$0 sk_?X_62$0 sk_?X_61$0)))))) :named P17))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_63$0) (in$0 x sk_?X_61$0)
                 (in$0 x (intersection$0 sk_?X_63$0 sk_?X_61$0)))
            (and (or (not (in$0 x sk_?X_63$0)) (not (in$0 x sk_?X_61$0)))
                 (not (in$0 x (intersection$0 sk_?X_63$0 sk_?X_61$0)))))) :named P18))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_66$0) (in$0 x sk_?X_64$0)
                 (in$0 x (intersection$0 sk_?X_66$0 sk_?X_64$0)))
            (and (or (not (in$0 x sk_?X_66$0)) (not (in$0 x sk_?X_64$0)))
                 (not (in$0 x (intersection$0 sk_?X_66$0 sk_?X_64$0)))))) :named P19))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P20))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P21))

(assert (! (= (read$0 (write$0 next$0 prv_init$0 curr_5$0) prv_init$0) curr_5$0) :named P22))

(assert (! (or (= null$0 prv_init$0)
    (= (read$0 next$0 null$0)
      (read$0 (write$0 next$0 prv_init$0 curr_5$0) null$0))) :named P23))

(assert (! (or (= prv_init$0 prv_init$0)
    (= (read$0 next$0 prv_init$0)
      (read$0 (write$0 next$0 prv_init$0 curr_5$0) prv_init$0))) :named P24))

(assert (! (or (= old_curr_4$0 prv_init$0)
    (= (read$0 next$0 old_curr_4$0)
      (read$0 (write$0 next$0 prv_init$0 curr_5$0) old_curr_4$0))) :named P25))

(assert (! (= (read$0 next$0 null$0) null$0) :named P26))

(assert (! (= (read$0 next_2$0 null$0) null$0) :named P27))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P28))

(assert (! (or (Btwn$0 next$0 curr_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_61$0 next$0 curr_init$0 null$0))) :named P29))

(assert (! (or
    (and (= next_2$0 (write$0 next$0 prv_4$0 (read$0 next$0 old_curr_4$0)))
         (not (= prv_4$0 null$0)))
    (and (= next_2$0 next$0) (= prv_4$0 null$0) (= res_3$0 res_4$0)
         (= res_4$0 (read$0 next$0 old_curr_4$0)))) :named P30))

(assert (! (= curr_4$0 curr_init$0) :named P31))

(assert (! (= nondet_2$0 nondet_init$0) :named P32))

(assert (! (= old_curr_4$0 curr_4$0) :named P33))

(assert (! (= res_3$0 res_init$0) :named P34))

(assert (! nondet_3$0 :named P35))

(assert (! (= sk_?X_60$0 (union$0 sk_?X_62$0 sk_?X_61$0)) :named P36))

(assert (! (= sk_?X_62$0 emptyset$0) :named P37))

(assert (! (= sk_?X_64$0 sk_?X_65$0) :named P38))

(assert (! (= sk_?X_66$0 (lseg_domain$0 next$0 res_init$0 prv_init$0)) :named P39))

(assert (! (or
    (and (= (read$0 next$0 prv_init$0) curr_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_63$0 sk_?X_61$0))
         (= emptyset$0 (intersection$0 sk_?X_66$0 sk_?X_64$0))
         (= sk_?X_59$0 FP$0)
         (lseg_struct$0 sk_?X_61$0 next$0 curr_init$0 null$0)
         (lseg_struct$0 sk_?X_66$0 next$0 res_init$0 prv_init$0))
    (and (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_62$0 sk_?X_61$0))
         (= prv_init$0 null$0) (= res_init$0 curr_init$0) (= sk_?X_60$0 FP$0)
         (lseg_struct$0 sk_?X_61$0 next$0 curr_init$0 null$0))) :named P40))

(assert (! (not (in$0 null$0 Alloc$0)) :named P41))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_init$0 null$0)))))) :named P42))

(assert (! (or (Btwn$0 next$0 res_init$0 prv_init$0 prv_init$0)
    (not (lseg_struct$0 sk_?X_66$0 next$0 res_init$0 prv_init$0))) :named P43))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P44))

(assert (! (= curr_5$0 (read$0 next$0 curr_4$0)) :named P45))

(assert (! (= old_curr_2$0 old_curr_init$0) :named P46))

(assert (! (= prv_4$0 prv_init$0) :named P47))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P48))

(assert (! (= sk_?X_59$0 (union$0 sk_?X_63$0 sk_?X_61$0)) :named P49))

(assert (! (= sk_?X_61$0 (lseg_domain$0 next$0 curr_init$0 null$0)) :named P50))

(assert (! (= sk_?X_63$0 (union$0 sk_?X_66$0 sk_?X_64$0)) :named P51))

(assert (! (= sk_?X_65$0 (setenum$0 prv_init$0)) :named P52))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P53))

(assert (! (not (= curr_4$0 null$0)) :named P54))

(assert (! (not (in$0 old_curr_4$0 FP$0)) :named P55))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 res_init$0 l1 prv_init$0)
                 (in$0 l1 (lseg_domain$0 next$0 res_init$0 prv_init$0))
                 (not (= l1 prv_init$0)))
            (and
                 (or (= l1 prv_init$0)
                     (not (Btwn$0 next$0 res_init$0 l1 prv_init$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 res_init$0 prv_init$0)))))) :named P56))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or
                 (Btwn$0
                   (write$0 next$0 prv_4$0 (read$0 next$0 old_curr_4$0)) ?z
                   ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v prv_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z prv_4$0
                                               prv_4$0)))))
                          (and (not (= prv_4$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u prv_4$0)
                               (or
                                   (Btwn$0 next$0
                                     (read$0 next$0 old_curr_4$0) ?v prv_4$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 old_curr_4$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 old_curr_4$0)
                                               prv_4$0 prv_4$0)))))
                          (and (not (= prv_4$0 ?v))
                               (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?u
                                 ?v)
                               (or
                                   (Btwn$0 next$0
                                     (read$0 next$0 old_curr_4$0) ?v prv_4$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 old_curr_4$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 old_curr_4$0)
                                               prv_4$0 prv_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v prv_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z prv_4$0 prv_4$0)))))
                 (and (not (= prv_4$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u prv_4$0)
                      (or
                          (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                            prv_4$0)
                          (and
                               (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                                 ?v)
                               (not
                                    (Btwn$0 next$0
                                      (read$0 next$0 old_curr_4$0) prv_4$0
                                      prv_4$0)))))
                 (and (not (= prv_4$0 ?v))
                      (or (Btwn$0 next$0 ?z prv_4$0 ?v)
                          (and (Btwn$0 next$0 ?z prv_4$0 prv_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?u ?v)
                      (or
                          (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                            prv_4$0)
                          (and
                               (Btwn$0 next$0 (read$0 next$0 old_curr_4$0) ?v
                                 ?v)
                               (not
                                    (Btwn$0 next$0
                                      (read$0 next$0 old_curr_4$0) prv_4$0
                                      prv_4$0)))))
                 (not
                      (Btwn$0
                        (write$0 next$0 prv_4$0 (read$0 next$0 old_curr_4$0))
                        ?z ?u ?v))))) :named P57))

(assert (! (forall ((?x Loc)) (Btwn$0 next_2$0 ?x ?x ?x)) :named P58))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P59))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_2$0 ?x ?y ?x)) (= ?x ?y))) :named P60))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P61))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?x ?z ?z))
            (Btwn$0 next_2$0 ?x ?y ?z) (Btwn$0 next_2$0 ?x ?z ?y))) :named P62))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P63))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?y) (Btwn$0 next_2$0 ?y ?z ?z)))) :named P64))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P65))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?y ?z ?z))
            (Btwn$0 next_2$0 ?x ?z ?z))) :named P66))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P67))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?y ?u ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?u) (Btwn$0 next_2$0 ?x ?u ?z)))) :named P68))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P69))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?x ?u ?y))
            (and (Btwn$0 next_2$0 ?x ?u ?z) (Btwn$0 next_2$0 ?u ?y ?z)))) :named P70))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P71))

(check-sat)

(get-interpolants (and P45 P66 P36 P23 P7 P1 P48 P12 P53 P32 P61 P18 P58 P31 P44 P57 P4 P67 P43 P6 P64 P55 P27 P11 P24 P19 P51 P41 P70 P46 P34 P71 P20 P2 P63 P40) (and P21 P25 P60 P15 P49 P10 P29 P38 P52 P62 P35 P56 P69 P17 P68 P22 P59 P14 P28 P26 P16 P65 P39 P3 P9 P5 P33 P54 P13 P30 P47 P0 P50 P8 P37 P42))

(exit)