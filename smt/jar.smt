(set-option :produce-proofs true)
(set-logic HORN)

(declare-datatypes () ((Unit unit)))
;;(define-sort A () (_ BitVec 3)) ;address
(define-sort A () Unit)
(define-sort BUINT () (_ BitVec 2)) ; bounded 256bit unsigned integer
(define-sort M () (Array A BUINT)) ;mapping from address to Int
(declare-fun P_alpha (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun P_omega (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_alpha (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_1 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_2 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_3 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_omega (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun S (M BUINT A BUINT M BUINT Int) Bool)
(declare-fun T (M BUINT A BUINT M BUINT Int) Bool)
(declare-fun Ext (M BUINT M BUINT) Bool)
(declare-fun Jar (M BUINT) Bool)
(declare-fun Init (M BUINT) Bool)

(define-fun buint0 () BUINT ((_ int2bv 2) 0))
(define-fun zeros () M ((as const M) buint0))

;; deposit()
(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT)
	  (l_b M) (l_s A) (l_v BUINT) (l_tb BUINT) (l_r Int))
	 (=> (and (= b l_b) (= s l_s) (= v l_v) (bvule buint0 v) (= l_r 0)
		  (= l_tb (bvadd tb l_v)) (bvule tb l_tb) (bvule l_v l_tb))
	     (P_alpha b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (P_alpha b s v tb l_b l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s (bvadd (select l_b l_s) l_v)))
		  (bvule (select l_b l_s) (select l_b^ l_s))
		  (bvule l_v (select l_b^ l_s)))
	     (P_omega b s v tb l_b^ l_s l_v l_tb l_r))))

;; Summary deposit()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (P_omega b s v tb l_b l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= tb^ l_tb)))
		  (= r l_r))
	     (S b tb s v b^ tb^ r))))

;; withdraw()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= s l_s) (= v l_v) (= l_r 0) (= l_tb tb))
	     (Q_alpha b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_alpha b s v tb l_b l_s l_v l_tb l_r)
		  (not (= (select l_b l_s) buint0)))
	     (Q_1 b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT))
	 (=> (and (Q_1 b s v tb l_b l_s l_v l_tb l_r)
		  (= l_tb^ (bvsub l_tb (select l_b l_s)))
		  (bvule (select l_b l_s) l_tb))
	     (Q_2 b s v tb l_b l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (l_b^ M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
	 (=> (and (Q_2 b s v tb l_b l_s l_v l_tb l_r)
		  (and (Ext b^ tb^ b^^ tb^^)
		       (= b^ l_b) (= b^^ l_b^)
		       (= tb^ l_tb) (= tb^^ l_tb^)))
	     (Q_3 b s v tb l_b^ l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (Q_3 b s v tb l_b l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s buint0)))
	     (Q_omega b s v tb l_b^ l_s l_v l_tb l_r))))

;; Summary withdraw()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Q_omega b s v tb l_b l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= tb^ l_tb)))
		  (= r l_r))
	     (T b tb s v b^ tb^ r))))

;; Init
(assert (forall ((b M) (tb BUINT)) (Init b tb)))

;; (assert (forall ((b M) (tb BUINT) (a A) (v BUINT))
;; 		(=> (and (Init b tb)
;; 			 (bvule tb (bvadd tb v))
;; 			 (bvule v (bvadd tb v))
;; 			 (bvule (select b a) (bvadd (select b a) v))
;; 			 (bvule v (bvadd (select b a) v)))
;; 		    (Init (store b a (bvadd (select b a) v)) (bvadd tb v)))))

;; Jar
(assert (forall ((b M) (tb BUINT)) (=> (Init b tb) (Jar b tb))))

(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Jar b tb)
		  (T b tb s v b^ tb^ r)
		  (= r 0))
	     (Jar b^ tb^))))

(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Jar b tb)
		  (S b tb s v b^ tb^ r)
		  (= r 0))
	     (Jar b^ tb^))))

;; Ext
(assert (forall ((b M) (tb BUINT)) (Ext b tb b tb)))

(assert (forall ((b M) (s A) (v BUINT) (r Int)
		 (tb BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
		(=> (and (Ext b tb b^ tb^)
			 (S b^ tb^ s v b^^ tb^^ r)
			 (= r 0))
		    (Ext b tb b^^ tb^^))))

(assert (forall ((b M) (s A) (v BUINT) (r Int)
		 (tb BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
		(=> (and (Ext b tb b^ tb^)
			 (T b^ tb^ s v b^^ tb^^ r)
			 (= r 0))
		    (Ext b tb b^^ tb^^))))

;; Safety property
;; (assert
;;   (forall ((b M) (tb BUINT) (s A) (v BUINT)
;;  	   (b^ M) (tb^ BUINT) (r^ Int))
;;   	  (not (and (Jar b tb)
;; 		    (T b tb s v b^ tb^ r^)
;; 		    (not (= r^ 0))))))

;; (check-sat)
;; z3> sat

;; A determinacy property in a Horn clause
(assert
 (forall ((b M) (tb BUINT) (s A) (v BUINT)
 	  (b^ M) (tb^ BUINT) (r^ Int) (r_^ Int)
	  (b_^ M) (tb_^ BUINT))
  	  (not (and (Jar b tb)
		    (T b tb s v b^ tb^ r^)
		    (T b tb s v b_^ tb_^ r_^)
		    (= r^ 0)
		    (= r_^ 0)
		    (not (and (= b^ b_^) (= tb^ tb_^)))))))

(check-sat)
;; z3> unsat

(get-proof)
;; ((set-logic HORN)
;; (declare-fun query!0 ((Array (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256) (_ BitVec 256) (_ BitVec 256) (Array (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256) Int Int (Array (_ BitVec 256) (_ BitVec 256)) (_ BitVec 256)) Bool)
;; (proof
;; (let ((?x169417 ((as const (Array (_ BitVec 256) (_ BitVec 256))) (_ bv0 256))))
;;  (let ((?x319963 (store ?x169417 (_ bv288230376151711744 256) (_ bv57896923274742488653949073477085629643538986418682211193787197821148375023616 256))))
;;  (let ((?x319960 (store (store ?x169417 (_ bv0 256) (_ bv20800038484634643035584567912118586456079303944506707367258402646238817157122 256)) (_ bv288230376151711744 256) (_ bv57669883426918466267597619748240164614255154737933694157668571424282273382399 256))))
;;  (let (($x254861 (query!0 ?x319960 (_ bv59726499699374718779720585191373287173150093949386261379971576754490683949057 256) (_ bv0 256) (_ bv0 256) ?x319963 (_ bv39153501062564098130487471008100165746354621685628071048831800505117968433152 256) 0 0 (store ?x169417 (_ bv288230376151711744 256) (_ bv57669883426918466267597619748240164614255154737933694157668571424282273382399 256)) (_ bv38926461214740075744136017279254700717070790004879554012713174108251866791935 256))))
;;  (let (($x544 (forall ((A (Array (_ BitVec 256) (_ BitVec 256))) (B (_ BitVec 256)) )(Ext A B A B))
;;  ))
;;  (let ((@x286055 ((_ hyper-res 0 0) (asserted $x544) (Ext ?x319960 (_ bv38926461214740075744136017279254700717070790004879554012713174108251866791935 256) ?x319960 (_ bv38926461214740075744136017279254700717070790004879554012713174108251866791935 256)))))
;;  (let (($x828 (forall ((A (Array (_ BitVec 256) (_ BitVec 256))) (B (_ BitVec 256)) (C (_ BitVec 256)) (D (_ BitVec 256)) (E (Array (_ BitVec 256) (_ BitVec 256))) (F (_ BitVec 256)) (G (Array (_ BitVec 256) (_ BitVec 256))) (H (_ BitVec 256)) )(let (($x831 (and (Ext G H A D) (bvule D (bvadd D C)) (bvule C (bvadd (select A B) C)) (bvule C (bvadd D C)) (= F (bvadd D C)) (= E (store A B (bvadd (select A B) C))) (bvule (select A B) (bvadd (select A B) C)))))
;;  (=> $x831 (Ext G H E F))))
;;  ))
;;  (let ((@x254867 ((_ hyper-res 0 0 0 1) (asserted $x828) @x286055 (Ext ?x319960 (_ bv38926461214740075744136017279254700717070790004879554012713174108251866791935 256) (store ?x319963 (_ bv0 256) (_ bv20800038484634643035584567912118586456079303944506707367258402646238817157122 256)) (_ bv39153501062564098130487471008100165746354621685628071048831800505117968433152 256)))))
;;  (let (($x1017 (forall ((A (Array (_ BitVec 256) (_ BitVec 256))) (B (_ BitVec 256)) (C (_ BitVec 256)) (D (_ BitVec 256)) (E (_ BitVec 256)) (F (Array (_ BitVec 256) (_ BitVec 256))) (G (_ BitVec 256)) (H (Array (_ BitVec 256) (_ BitVec 256))) (I (_ BitVec 256)) (J (Array (_ BitVec 256) (_ BitVec 256))) (K (_ BitVec 256)) (L (Array (_ BitVec 256) (_ BitVec 256))) )(let (($x1015 (and (Ext A I J K) (Ext A E F G) (not (= (select A B) (_ bv0 256))) (= E (bvadd D (bvmul (_ bv115792089237316195423570985008687907853269984665640564039457584007913129639935 256) (select A B)))) (= I (bvadd D (bvmul (_ bv115792089237316195423570985008687907853269984665640564039457584007913129639935 256) (select A B)))) (= H (store F B (_ bv0 256))) (= L (store J B (_ bv0 256))) (or (not (= L H)) (not (= K G))) (bvule (select A B) D))))
;;  (=> $x1015 (query!0 A D B C L K 0 0 H G))))
;;  ))
;;    (mp ((_ hyper-res 0 0 0 1 0 2) (asserted $x1017) @x254867 @x286055 $x254861) (asserted (=> $x254861 false)) false))))))))))))

(reset)

(set-option :produce-proofs true)
(set-logic HORN)

(declare-datatypes () ((Unit unit)))
;;(define-sort A () (_ BitVec 3)) ;address
(define-sort A () Unit)
(define-sort BUINT () (_ BitVec 2)) ; bounded 256bit unsigned integer
(define-sort M () (Array A BUINT)) ;mapping from address to Int
(declare-fun P_alpha (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun P_omega (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_alpha (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_1 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_2 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_3 (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun Q_omega (M A BUINT BUINT M A BUINT BUINT Int) Bool)
(declare-fun S (M BUINT A BUINT M BUINT Int) Bool)
(declare-fun T (M BUINT A BUINT M BUINT Int) Bool)
(declare-fun Ext (M BUINT M BUINT) Bool)
(declare-fun Jar (M BUINT) Bool)
(declare-fun Init (M BUINT) Bool)

(define-fun buint0 () BUINT ((_ int2bv 2) 0))
(define-fun zeros () M ((as const M) buint0))

;; deposit()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= s l_s) (= v l_v) (bvule buint0 v) (= l_r 0)
		  (= l_tb (bvadd tb l_v)) (bvule tb l_tb) (bvule l_v l_tb))
	     (P_alpha b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (P_alpha b s v tb l_b l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s (bvadd (select l_b l_s) l_v)))
		  (bvule (select l_b l_s) (select l_b^ l_s))
		  (bvule l_v (select l_b^ l_s)))
	     (P_omega b s v tb l_b^ l_s l_v l_tb l_r))))

;; Summary deposit()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (P_omega b s v tb l_b l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= tb^ l_tb)))
		  (= r l_r))
	     (S b tb s v b^ tb^ r))))

;; withdraw()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (= b l_b) (= s l_s) (= v l_v) (= l_r 0) (= l_tb tb))
	     (Q_alpha b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT))
	 (=> (and (Q_alpha b s v tb l_b l_s l_v l_tb l_r)
		  (not (= (select l_b l_s) buint0)))
	     (Q_1 b s v tb l_b l_s l_v l_tb l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT))
	 (=> (and (Q_1 b s v tb l_b l_s l_v l_tb l_r)
		  (= l_tb^ (bvsub l_tb (select l_b l_s)))
		  (bvule (select l_b l_s) l_tb))
	     (Q_2 b s v tb l_b l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (l_b^ M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_tb^ BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
	 (=> (and (Q_2 b s v tb l_b l_s l_v l_tb l_r)
		  (and (Ext b^ tb^ b^^ tb^^)
		       (= b^ l_b) (= b^^ l_b^)
		       (= tb^ l_tb) (= tb^^ l_tb^)))
	     (Q_3 b s v tb l_b^ l_s l_v l_tb^ l_r))))

(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (l_b^ M))
	 (=> (and (Q_3 b s v tb l_b l_s l_v l_tb l_r)
		  (= l_b^ (store l_b l_s buint0)))
	     (Q_omega b s v tb l_b^ l_s l_v l_tb l_r))))

;; Summary withdraw()
(assert
 (forall ((b M) (l_b M) (s A) (l_s A) (v BUINT) (l_v BUINT) (l_r Int)
	  (tb BUINT) (l_tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Q_omega b s v tb l_b l_s l_v l_tb l_r)
		  (=> (not (= l_r 0)) (and (= b^ b) (= tb^ tb)))
		  (=> (= l_r 0) (and (= b^ l_b) (= tb^ l_tb)))
		  (= r l_r))
	     (T b tb s v b^ tb^ r))))

;; Init
(assert (forall ((b M) (tb BUINT)) (Init b tb)))

;; (assert (forall ((b M) (tb BUINT) (a A) (v BUINT))
;; 		(=> (and (Init b tb)
;; 			 (bvule tb (bvadd tb v))
;; 			 (bvule v (bvadd tb v))
;; 			 (bvule (select b a) (bvadd (select b a) v))
;; 			 (bvule v (bvadd (select b a) v)))
;; 		    (Init (store b a (bvadd (select b a) v)) (bvadd tb v)))))

;; Jar
(assert (forall ((b M) (tb BUINT)) (=> (Init b tb) (Jar b tb))))

(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Jar b tb)
		  (T b tb s v b^ tb^ r)
		  (= r 0))
	     (Jar b^ tb^))))

(assert
 (forall ((b M) (s A) (v BUINT) (tb BUINT) (b^ M) (tb^ BUINT) (r Int))
	 (=> (and (Jar b tb)
		  (S b tb s v b^ tb^ r)
		  (= r 0))
	     (Jar b^ tb^))))

;; Ext
(assert (forall ((b M) (tb BUINT)) (Ext b tb b tb)))

;; Commented out in order to check the case deposit() won't be called from unknown external contracts
;; (assert (forall ((b M) (s A) (v BUINT) (r Int)
;; 		 (tb BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
;; 		(=> (and (Ext b tb b^ tb^)
;; 			 (S b^ tb^ s v b^^ tb^^ r)
;; 			 (= r 0))
;; 		    (Ext b tb b^^ tb^^))))

(assert (forall ((b M) (s A) (v BUINT) (r Int)
		 (tb BUINT) (b^ M) (tb^ BUINT) (b^^ M) (tb^^ BUINT))
		(=> (and (Ext b tb b^ tb^)
			 (T b^ tb^ s v b^^ tb^^ r)
			 (= r 0))
		    (Ext b tb b^^ tb^^))))

;; Safety property
;; (assert
;;   (forall ((b M) (tb BUINT) (s A) (v BUINT)
;;  	   (b^ M) (tb^ BUINT) (r^ Int))
;;   	  (not (and (Jar b tb)
;; 		    (T b tb s v b^ tb^ r^)
;; 		    (not (= r^ 0))))))

;; (check-sat)
;; z3> sat

;; A determinacy property in a Horn clause
(assert
 (forall ((b M) (tb BUINT) (s A) (v BUINT)
 	  (b^ M) (tb^ BUINT) (r^ Int) (r_^ Int)
	  (b_^ M) (tb_^ BUINT))
  	  (not (and (Jar b tb)
		    (T b tb s v b^ tb^ r^)
		    (T b tb s v b_^ tb_^ r_^)
		    (= r^ 0)
		    (= r_^ 0)
		    (not (and (= b^ b_^) (= tb^ tb_^)))))))

(check-sat)
;; z3> unsat

(get-proof)
;; ((set-logic HORN)
;; (declare-fun query!0 ((Array Unit (_ BitVec 2)) (_ BitVec 2) Unit (_ BitVec 2) (Array Unit (_ BitVec 2)) (_ BitVec 2) Int Int (Array Unit (_ BitVec 2)) (_ BitVec 2)) Bool)
;; (proof
;; (let ((?x2247 ((as const (Array Unit (_ BitVec 2))) (_ bv0 2))))
;; (let ((?x2347 (store ?x2247 unit (_ bv1 2))))
;; (let (($x2931 (query!0 ?x2347 (_ bv3 2) unit (_ bv0 2) ?x2247 (_ bv1 2) 0 0 ?x2247 (_ bv2 2))))
;; (let (($x534 (forall ((A (Array Unit (_ BitVec 2))) (B (_ BitVec 2)) )(Ext A B A B))))
;; (let ((@x3083 (asserted $x534)))
;; (let ((@x3082 ((_ hyper-res 0 0) @x3083 (Ext ?x2347 (_ bv2 2) ?x2347 (_ bv2 2)))))
;; (let (($x953 (forall ((A (Array Unit (_ BitVec 2))) (B Unit) (C (_ BitVec 2)) (D (_ BitVec 2)) (E (Array Unit (_ BitVec 2)))
;;                        (F (_ BitVec 2)) (G (Array Unit (_ BitVec 2))) (H (Array Unit (_ BitVec 2))) (I (_ BitVec 2)) )
;;                      (let (($x951 (and (Ext H I A C) (Ext A D E F) (not (= (select A B) (_ bv0 2))) (= D (bvadd C (bvmul (_ bv3 2) (select A B))))
;;                         (= G (store E B (_ bv0 2))) (bvule (select A B) C))))
;;            (=> $x951 (Ext H I G F))))
;;  ))
;;  (let ((@x2953 ((_ hyper-res 0 0 0 1 0 2) (asserted $x953) @x3082 ((_ hyper-res 0 0) @x3083 (Ext ?x2347 (_ bv1 2) ?x2347 (_ bv1 2))) (Ext ?x2347 (_ bv2 2) ?x2247 (_ bv1 2)))))
;;       (let (($x999 (forall ((A (Array Unit (_ BitVec 2))) (B Unit) (C (_ BitVec 2)) (D (_ BitVec 2)) (E (_ BitVec 2)) (F (Array Unit (_ BitVec 2)))
;;                             (G (_ BitVec 2)) (H (Array Unit (_ BitVec 2))) (I (_ BitVec 2)) (J (Array Unit (_ BitVec 2))) (K (_ BitVec 2)) (L (Array Unit (_ BitVec 2))) )
;;                            (let (($x997 (and (Ext A I J K) (Ext A E F G) (not (= (select A B) (_ bv0 2))) (= E (bvadd D (bvmul (_ bv3 2) (select A B))))
;;                                              (= I (bvadd D (bvmul (_ bv3 2) (select A B)))) (= H (store F B (_ bv0 2))) (= L (store J B (_ bv0 2)))
;;                                              (or (not (= L H)) (not (= K G))) (bvule (select A B) D))))
;;                                 (=> $x997 (query!0 A D B C L K 0 0 H G)))) ))
;;            (mp ((_ hyper-res 0 0 0 1 0 2) (asserted $x999) @x2953 @x3082 $x2931) (asserted (=> $x2931 false)) false))))))))))))
