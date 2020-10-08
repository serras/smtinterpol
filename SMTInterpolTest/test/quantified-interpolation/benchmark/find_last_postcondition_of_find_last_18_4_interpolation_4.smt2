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
  tests/spl/sl/rec_concat.spl:18:4-14:A postcondition of procedure find_last might not hold at this return point
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
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_2$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun l_3$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun n_2$0 () Loc)
(declare-fun n2_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?e_1$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 n2_2$0 ?y ?y)) (= n2_2$0 ?y)
            (Btwn$0 next$0 n2_2$0 (read$0 next$0 n2_2$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 a$0 ?y ?y)) (= a$0 ?y)
            (Btwn$0 next$0 a$0 (read$0 next$0 a$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 n2_2$0) n2_2$0))
            (not (Btwn$0 next$0 n2_2$0 ?y ?y)) (= n2_2$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 a$0) a$0)) (not (Btwn$0 next$0 a$0 ?y ?y))
            (= a$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 n2_2$0 (read$0 next$0 n2_2$0) (read$0 next$0 n2_2$0)) :named P6))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P7))

(assert (! (Btwn$0 next$0 a$0 (read$0 next$0 a$0) (read$0 next$0 a$0)) :named P8))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_10$0 null$0) sk_?X_10$0)
    (= null$0 (ep$0 next$0 sk_?X_10$0 null$0))) :named P9))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_10$0 a$0) sk_?X_10$0)
    (= a$0 (ep$0 next$0 sk_?X_10$0 a$0))) :named P10))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_10$0 n_2$0) sk_?X_10$0)
    (= n_2$0 (ep$0 next$0 sk_?X_10$0 n_2$0))) :named P11))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_10$0 sk_?e_1$0) sk_?X_10$0)
    (= sk_?e_1$0 (ep$0 next$0 sk_?X_10$0 sk_?e_1$0))) :named P12))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_10$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_10$0)))) :named P13))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 a$0 (ep$0 next$0 sk_?X_10$0 a$0) ?y)
            (not (Btwn$0 next$0 a$0 ?y ?y)) (not (in$0 ?y sk_?X_10$0)))) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 n_2$0 (ep$0 next$0 sk_?X_10$0 n_2$0) ?y)
            (not (Btwn$0 next$0 n_2$0 ?y ?y)) (not (in$0 ?y sk_?X_10$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 sk_?X_10$0 sk_?e_1$0) ?y)
            (not (Btwn$0 next$0 sk_?e_1$0 ?y ?y)) (not (in$0 ?y sk_?X_10$0)))) :named P16))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_10$0 null$0)
  (ep$0 next$0 sk_?X_10$0 null$0)) :named P17))

(assert (! (Btwn$0 next$0 a$0 (ep$0 next$0 sk_?X_10$0 a$0) (ep$0 next$0 sk_?X_10$0 a$0)) :named P18))

(assert (! (Btwn$0 next$0 n_2$0 (ep$0 next$0 sk_?X_10$0 n_2$0)
  (ep$0 next$0 sk_?X_10$0 n_2$0)) :named P19))

(assert (! (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 sk_?X_10$0 sk_?e_1$0)
  (ep$0 next$0 sk_?X_10$0 sk_?e_1$0)) :named P20))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P21))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P22))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_10$0 FP$0))
                 (or (in$0 x sk_?X_10$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_10$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_10$0 FP$0)))))) :named P24))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_9$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_9$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_9$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_9$0)))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP_2$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP_2$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP_2$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP_2$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_6$0 sk_?X_8$0))
                 (or (in$0 x sk_?X_6$0) (in$0 x sk_?X_8$0)))
            (and (not (in$0 x sk_?X_6$0)) (not (in$0 x sk_?X_8$0))
                 (not (in$0 x (union$0 sk_?X_6$0 sk_?X_8$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_1$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_1$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_1$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_14$0 sk_?X_8$0))
                 (or (in$0 x sk_?X_14$0) (in$0 x sk_?X_8$0)))
            (and (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_8$0))
                 (not (in$0 x (union$0 sk_?X_14$0 sk_?X_8$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_6$0) (in$0 x sk_?X_8$0)
                 (in$0 x (intersection$0 sk_?X_6$0 sk_?X_8$0)))
            (and (or (not (in$0 x sk_?X_6$0)) (not (in$0 x sk_?X_8$0)))
                 (not (in$0 x (intersection$0 sk_?X_6$0 sk_?X_8$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_10$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_10$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_10$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_10$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_14$0) (in$0 x sk_?X_8$0)
                 (in$0 x (intersection$0 sk_?X_14$0 sk_?X_8$0)))
            (and (or (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_8$0)))
                 (not (in$0 x (intersection$0 sk_?X_14$0 sk_?X_8$0)))))) :named P34))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_10$0))
                 (not (in$0 x sk_?X_10$0)))
            (and (or (in$0 x sk_?X_10$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_10$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P37))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P38))

(assert (! (= (read$0 next$0 null$0) null$0) :named P39))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P40))

(assert (! (or (Btwn$0 next$0 a$0 l_3$0 l_3$0)
    (not (lseg_struct$0 sk_?X_14$0 next$0 a$0 l_3$0))) :named P41))

(assert (! (or (Btwn$0 next$0 n_2$0 n2_2$0 n2_2$0)
    (not (lseg_struct$0 sk_?X_6$0 next$0 n_2$0 n2_2$0))) :named P42))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P43))

(assert (! (= l_3$0 n2_2$0) :named P44))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P45))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P46))

(assert (! (= emptyset$0 emptyset$0) :named P47))

(assert (! (= sk_?X_6$0 (lseg_domain$0 next$0 n_2$0 n2_2$0)) :named P48))

(assert (! (= sk_?X_8$0 sk_?X_7$0) :named P49))

(assert (! (= sk_?X_9$0 (union$0 sk_?X_6$0 sk_?X_8$0)) :named P50))

(assert (! (= emptyset$0 emptyset$0) :named P51))

(assert (! (= sk_?X_10$0 FP_1$0) :named P52))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P53))

(assert (! (not (= n_2$0 null$0)) :named P54))

(assert (! (= sk_?X_12$0 sk_?X_13$0) :named P55))

(assert (! (= sk_?X_13$0 (lseg_domain$0 next$0 a$0 null$0)) :named P56))

(assert (! (lseg_struct$0 sk_?X_13$0 next$0 a$0 null$0) :named P57))

(assert (! (= sk_?X_14$0 (lseg_domain$0 next$0 a$0 l_3$0)) :named P58))

(assert (! (= sk_?X_16$0 sk_?X_15$0) :named P59))

(assert (! (or (in$0 sk_?e_1$0 (intersection$0 sk_?X_14$0 sk_?X_16$0))
    (and
         (in$0 sk_?e_1$0
           (union$0 (intersection$0 Alloc$0 FP$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (not (in$0 sk_?e_1$0 sk_?X_17$0)))
    (and (in$0 sk_?e_1$0 sk_?X_17$0)
         (not
              (in$0 sk_?e_1$0
                (union$0 (intersection$0 Alloc$0 FP$0)
                  (setminus$0 Alloc$0 Alloc$0)))))
    (not (= (read$0 next$0 l_3$0) null$0))
    (not (Btwn$0 next$0 a$0 l_3$0 l_3$0))) :named P60))

(assert (! (not (in$0 null$0 Alloc$0)) :named P61))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 a$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a$0 null$0)))))) :named P62))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 n_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 n_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 n_2$0 null$0)))))) :named P63))

(assert (! (or (Btwn$0 next$0 a$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_13$0 next$0 a$0 null$0))) :named P64))

(assert (! (or (Btwn$0 next$0 n_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_11$0 next$0 n_2$0 null$0))) :named P65))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P66))

(assert (! (= FP_Caller_final_2$0 (union$0 FP_Caller_1$0 FP_2$0)) :named P67))

(assert (! (= n_2$0 (read$0 next$0 a$0)) :named P68))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P69))

(assert (! (= (read$0 next$0 n2_2$0) null$0) :named P70))

(assert (! (= emptyset$0 (intersection$0 sk_?X_6$0 sk_?X_8$0)) :named P71))

(assert (! (= sk_?X_7$0 (setenum$0 n2_2$0)) :named P72))

(assert (! (= sk_?X_9$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P73))

(assert (! (lseg_struct$0 sk_?X_6$0 next$0 n_2$0 n2_2$0) :named P74))

(assert (! (= sk_?X_10$0 sk_?X_11$0) :named P75))

(assert (! (= sk_?X_11$0 (lseg_domain$0 next$0 n_2$0 null$0)) :named P76))

(assert (! (lseg_struct$0 sk_?X_11$0 next$0 n_2$0 null$0) :named P77))

(assert (! (= emptyset$0 emptyset$0) :named P78))

(assert (! (= sk_?X_12$0 FP$0) :named P79))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P80))

(assert (! (not (= a$0 null$0)) :named P81))

(assert (! (= sk_?X_15$0 (setenum$0 l_3$0)) :named P82))

(assert (! (= sk_?X_17$0 (union$0 sk_?X_14$0 sk_?X_16$0)) :named P83))

(assert (! (not (= n_2$0 null$0)) :named P84))

(assert (! (not (in$0 null$0 Alloc$0)) :named P85))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 l_3$0)
                 (in$0 l1 (lseg_domain$0 next$0 a$0 l_3$0))
                 (not (= l1 l_3$0)))
            (and (or (= l1 l_3$0) (not (Btwn$0 next$0 a$0 l1 l_3$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a$0 l_3$0)))))) :named P86))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n_2$0 l1 n2_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 n_2$0 n2_2$0))
                 (not (= l1 n2_2$0)))
            (and (or (= l1 n2_2$0) (not (Btwn$0 next$0 n_2$0 l1 n2_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 n_2$0 n2_2$0)))))) :named P87))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P88))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P89))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P90))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P91))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P92))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P93))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P94))

(check-sat)

(get-interpolants (and P56 P69 P91 P30 P87 P41 P55 P44 P81 P80 P9 P83 P40 P48 P3 P29 P26 P24 P27 P46 P10 P60 P34 P71 P65 P88 P33 P90 P61 P75 P52 P85 P2 P35 P4 P23 P63 P7 P1 P62 P54 P72 P37 P53 P5 P57 P68 P59) (and P51 P82 P70 P73 P19 P14 P11 P50 P12 P39 P43 P94 P38 P20 P31 P0 P93 P16 P77 P15 P67 P58 P86 P92 P76 P17 P8 P89 P66 P22 P42 P47 P79 P49 P18 P25 P84 P6 P28 P21 P36 P78 P74 P45 P13 P32 P64))

(exit)