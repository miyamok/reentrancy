;(set-option :produce-models true)
(set-option :produce-proofs true)
(set-logic HORN)

(define-sort A () (_ BitVec 256)) ;address
(define-sort BUINT () (_ BitVec 256)) ; bounded 256bit unsigned integer
(define-sort M () (Array A BUINT)) ;mapping from address to Int
(declare-fun P_alpha (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun P_1 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun P_omega (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_alpha (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_0 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_1 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_2 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_3 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_4 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_5 (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun Q_omega (M Bool A BUINT BUINT M Bool A BUINT BUINT Int) Bool)
(declare-fun S (M Bool BUINT A BUINT M Bool BUINT Int) Bool)
(declare-fun T (M Bool BUINT A BUINT M Bool BUINT Int) Bool)
(declare-fun Ext (M Bool BUINT M Bool BUINT) Bool)
(declare-fun Jar (M Bool BUINT) Bool)
(declare-fun Init (M Bool BUINT) Bool)

(define-fun buint0 () BUINT ((_ int2bv 256) 0))
(define-fun zeros () M ((as const M) buint0))

;; deposit()
(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= lock l_lock) (= s l_s) (= v l_v) (bvule buint0 v) (= l_r 0)
		  (= l_tb (bvadd tb l_v)) (bvule tb l_tb) (bvule l_v l_tb))
	     (P_alpha b lock s v tb l_b l_lock l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (P_alpha b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (not l_lock))
	     (P_1 b lock s v tb l_b^ l_lock l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (P_1 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s (bvadd (select l_b l_s) l_v)))
		  (bvule (select l_b l_s) (select l_b^ l_s))
		  (bvule l_v (select l_b^ l_s)))
	     (P_omega b lock s v tb l_b^ l_lock l_s l_v l_tb l_r))))

;; Summary deposit()
(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT) (b^ M) (lock^ Bool) (tb^ BUINT) (r Int))
	 (=> (and (P_omega b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= lock^ lock) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= lock^ l_lock) (= tb^ l_tb)))
		  (= r l_r))
	     (S b lock tb s v b^ lock^ tb^ r))))

;; withdraw()
(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= lock l_lock) (= s l_s) (= v l_v) (= l_r 0) (= l_tb tb))
	     (Q_alpha b lock s v tb l_b l_lock l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_alpha b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (not l_lock))
	     (Q_0 b lock s v tb l_b l_lock l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (l_lock^ Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_0 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (= l_lock^ true))
	     (Q_1 b lock s v tb l_b l_lock^ l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_1 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (not (= (select l_b l_s) buint0)))
	     (Q_2 b lock s v tb l_b l_lock l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int) (tb BUINT) (l_tb BUINT) (l_tb^ BUINT))
	 (=> (and (Q_2 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (= l_tb^ (bvsub l_tb (select l_b l_s)))
		  (bvule (select l_b l_s) l_tb))
	     (Q_3 b lock s v tb l_b l_lock l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (l_b^ M)
	  (lock Bool) (l_lock Bool)
	  (s A) (l_s A)
	  (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT) (b^ M) (lock^ Bool) (tb^ BUINT) (b^^ M) (lock^^ Bool) (tb^^ BUINT) (l_lock^ Bool))
	 (=> (and (Q_3 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (and (Ext b^ lock^ tb^ b^^ lock^^ tb^^)
		       (= b^ l_b) (= b^^ l_b^)
		       (= lock^ l_lock) (= lock^^ l_lock^)
		       (= tb^ l_tb) (= tb^^ l_tb^)))
	     (Q_4 b lock s v tb l_b^ l_lock^ l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (lock Bool) (l_lock Bool)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (Q_4 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s buint0)))
	     (Q_5 b lock s v tb l_b^ l_lock l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (lock Bool) (l_lock Bool) (l_lock^ Bool)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_5 b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (= l_lock^ false))
	     (Q_omega b lock s v tb l_b l_lock^ l_s l_v l_tb l_r))))

;; Summary withdraw()
(assert
 (forall ((b M) (l_b M) (lock Bool) (l_lock Bool) (s A) (l_s A) (v BUINT) (l_v BUINT)
	  (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (lock^ Bool) (tb^ BUINT) (r Int))
	 (=> (and (Q_omega b lock s v tb l_b l_lock l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= lock^ lock) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= lock^ l_lock) (= tb^ l_tb)))
		  (= r l_r))
	     (T b lock tb s v b^ lock^ tb^ r))))

;; Init
(assert (forall ((b M) (tb BUINT)) (Init b false tb)))

;; (assert (forall ((b M) (tb BUINT) (a A) (v BUINT))
;; 		(=> (and (Init b tb)
;; 			 (bvule tb (bvadd tb v))
;; 			 (bvule v (bvadd tb v))
;; 			 (bvule (select b a) (bvadd (select b a) v))
;; 			 (bvule v (bvadd (select b a) v)))
;; 		    (Init (store b a (bvadd (select b a) v)) (bvadd tb v)))))

;; Jar
(assert (forall ((b M) (lock Bool) (tb BUINT))
		(=> (Init b lock tb) (Jar b lock tb))))

(assert
 (forall ((b M) (lock Bool) (s A) (v BUINT) (tb BUINT)
	  (b^ M) (lock^ Bool) (tb^ BUINT) (r Int))
	 (=> (and (Jar b lock tb)
		  (T b lock tb s v b^ lock^ tb^ r)
		  (= r 0))
	     (Jar b^ lock^ tb^))))

(assert
 (forall ((b M) (lock Bool) (s A) (v BUINT) (tb BUINT) (b^ M) (lock^ Bool)
	  (tb^ BUINT) (r Int))
	 (=> (and (Jar b lock tb)
		  (S b lock tb s v b^ lock^ tb^ r)
		  (= r 0))
	     (Jar b^ lock^ tb^))))

;; Ext
(assert (forall ((b M) (lock Bool) (tb BUINT)) (Ext b lock tb b lock tb)))

(assert (forall ((b M) (lock Bool) (s A) (v BUINT) (r Int) (tb BUINT)
		 (b^ M) (lock^ Bool) (tb^ BUINT) (b^^ M) (lock^^ Bool) (tb^^ BUINT))
		(=> (and (Ext b lock tb b^ lock^ tb^)
			 (S b^ lock^ tb^ s v b^^ lock^^ tb^^ r)
			 (= r 0))
		    (Ext b lock tb b^^ lock^^ tb^^))))

(assert (forall ((b M) (lock Bool) (s A) (v BUINT) (r Int) (tb BUINT)
		 (b^ M) (lock^ Bool) (tb^ BUINT) (b^^ M) (lock^^ Bool) (tb^^ BUINT))
		(=> (and (Ext b lock tb b^ lock^ tb^)
			 (T b^ lock^ tb^ s v b^^ lock^^ tb^^ r)
			 (= r 0))
		    (Ext b lock tb b^^ lock^^ tb^^))))

;; Safety property

;; (assert (forall ((b M) (lock Bool) (tb BUINT))
;; 		(not (=> (Jar b lock tb)
;; 			 (not (= lock false))))))

;; (assert
;;   (forall ((b M) (lock Bool) (tb BUINT) (s A) (v BUINT)
;;  	   (b^ M) (lock^ Bool) (tb^ BUINT) (r^ Int))
;;   	  (not (and (Jar b lock tb)
;; 		    (T b lock tb s v b^ lock^ tb^ r^)
;; 		    (not (= r^ 0))))))

;; (check-sat)
;; z3> sat

;A determinacy property in a Horn clause
(assert
 (forall ((b M) (lock Bool) (tb BUINT) (s A) (v BUINT)
 	  (b^ M) (lock^ Bool) (tb^ BUINT) (r^ Int) (r_^ Int)
	  (b_^ M) (lock_^ Bool) (tb_^ BUINT))
  	  (not (and (Jar b lock tb)
		    (T b lock tb s v b^ lock^ tb^ r^)
		    (T b lock tb s v b_^ lock_^ tb_^ r_^)
		    (= r^ 0)
		    (= r_^ 0)
		    (not (and (= b^ b_^)
			      (= lock^ lock_^)
			      (= tb^ tb_^)))))))

(check-sat)
;; z3> unsat

