(defun negate (exp)
  (if (listp exp)
      (case (car exp)
	    ((all) `(exists ,(cadr exp) ,(negate (caddr exp))))
	    ((exists) `(all ,(cadr exp) ,(negate (caddr exp))))
	    ((not) (cadr exp))
	    ((or) `(and ,(negate (cadr exp)) ,(negate (caddr exp))))
	    ((and) `(or ,(negate (cadr exp)) ,(negate (caddr exp))))
	    (otherwise `(not ,exp)))
      `(not ,exp)))

(defun wrap (exp)
  (if (listp exp) exp (list exp)))

(defun unwrap (exp)
  (if (and (and (listp exp) (not (listp (car exp)))) (not (cdr exp))) (car exp) exp))

(defun imply-exp (exp)
  (if (listp exp)
      (case (car exp)
	((implies) `(or ,(negate (imply-exp (cadr exp))) ,(imply-exp (caddr exp))))
	((equivalent) (imply-exp `(and (implies ,(cadr exp) ,(caddr exp)) (implies ,(caddr exp) ,(cadr exp)))))
	(otherwise (mapcar #'imply-exp exp)))
      exp))

(defun prop-not (exp)
  (if (listp exp)
      (case (car exp)
	    ((not) (negate (cadr exp)))
	    (otherwise (mapcar #'prop-not exp)))
    exp))

(defun push-or (exp)
  (if (listp exp)
      (case (car exp)
	    ((or)
	     (let ((sub1 (cadr exp))
		   (sub2 (caddr exp)))
	       (cond ((and (listp sub1) (eq (car sub1) 'and))
		      (push-or (dist-or sub2 sub1)))
		     ((and (listp sub2) (eq (car sub2) 'and))
		      (push-or (dist-or sub1 sub2)))
		     (t (mapcar #'push-or exp)))))
	    (otherwise (mapcar #'push-or exp)))
    exp))

(defun dist-or (val and-exp)
  `(and (or ,val ,(cadr and-exp)) (or ,val ,(caddr and-exp))))

(defun iter-push-or (exp)
  (let ((new-exp (push-or exp)))
    (if (not (equal exp new-exp))
	(iter-push-or new-exp)
      exp)))

(defun substitute (var tar exp)
  (if (listp exp)
      (cond
       ((eq var (car exp)) (cons tar ((lambda (e) (substitute var tar e)) (cdr exp))))
       (t (mapcar (lambda (e) (substitute var tar e)) exp)))
    (if (eq var exp) tar exp)))

(defun make-mapping (deps label)
  (if deps
      (cons (intern (concatenate 'string "G" (write-to-string label))) deps)
    (intern (concatenate 'string "U" (write-to-string label)))))

(defun remove-exists (exp)
  (defparameter *label* 0) 
  (labels ((skolemise (expr deps)
		    (if (listp expr)
			(case (car expr)
			      ((all) (mapcar (lambda (e) (skolemise e (cons (cadr expr) deps))) expr))
			      ((exists) (progn (defparameter *label* (1+ *label*))
					       (substitute (cadr expr) (make-mapping deps *label*) (skolemise (caddr expr) deps))))
			      (otherwise (mapcar (lambda (e) (skolemise e deps)) expr)))
		      expr)))
	(skolemise exp ())))

(defun remove-all (exp)
  (defparameter *label* 0)
  (labels ((rm-univ (expr)
		    (if (listp expr)
			(case (car expr)
			      ((all) (progn (defparameter *label* (1+ *label*))
					    (substitute (cadr expr)
							(intern (concatenate 'string "$W" (write-to-string *label*)))
							(rm-univ (caddr expr)))))
			      (otherwise (mapcar #'rm-univ expr)))
		      expr)))
	  (rm-univ exp)))

(defun cnf (exp)
  (iter-push-or (remove-all (remove-exists (prop-not (imply-exp exp))))))

(defun remove-and (exp)
  (if (listp exp)
      (case (car exp)
	((and) (append (wrap (remove-and (cadr exp))) (wrap (remove-and (caddr exp)))))
	(otherwise (list exp)))
      exp))

(defun remove-or (exp)
  (if (listp exp)
      (case (car exp)
	((or) (append (wrap (remove-or (cadr exp))) (wrap (remove-or (caddr exp)))))
	(otherwise (list exp)))
      exp))

(defun clausify (exp)
  (mapcar (lambda (x) (wrap (remove-or x))) (remove-and exp)))

(defun cnf-clausify (exp)
  (clausify (cnf exp)))

(defun combine-disjunction (dis)
  (if dis
      (if (find-if (lambda (x) (equal x (car dis))) (cdr dis))
	  (combine-disjunction (cdr dis))
	  (cons (car dis) (combine-disjunction (cdr dis))))
      dis))

(defun eliminate-disjunction (dis)
  (if dis
      (if (find-if (lambda (x) (equal x (negate (car dis)))) (cdr dis))
	  t
	  (cons (car dis) (eliminate-disjunction (cdr dis))))
      dis))

(defun simplify-disjunctions (clause)
  (mapcar (lambda (x) (eliminate-disjunction (combine-disjunction x))) clause))

(defun simplify-conjunctions (conj)
  (if conj
      (cond ((not (car conj)) ())
	    ((eq (car conj) t) (simplify-conjunctions (cdr conj)))
	    ((find-if (lambda (x) (equal (unwrap x) (negate (unwrap (car conj))))) (cdr conj)) ())
	    (t (cons (car conj) (simplify-conjunctions (cdr conj)))))
      conj))

(defun simplify-clause (clause)
  (simplify-conjunctions (simplify-disjunctions clause)))

(defun variablep (exp)
  (if (listp exp) () (equal "$" (subseq (symbol-name exp) 0 1))))

(defun resolvep (dis1 dis2)
  (if dis1
      (if (find-if (lambda (x) (equal (unwrap x) (negate (unwrap (car dis1))))) dis2) (car dis1) (resolvep (cdr dis1) dis2))
    ()))

(defun subequal (exp1 exp2)
  (equal (unwrap exp1) (unwrap exp2)))

(defun resolve (dis1 dis2)
  (let ((rp (resolvep dis1 dis2)))
    (if rp
	(remove-if (lambda (x) (subequal x rp)) (remove-if (lambda (x) (subequal x (negate rp))) (append dis1 dis2)))
      ())))
