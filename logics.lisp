(defun negate (exp)
  (if (listp exp)
      (case (car exp)
	    ((all) `(exists ,(cadr exp) ,(negate (caddr exp))))
	    ((exists) `(all ,(cadr exp) ,(negate (caddr exp))))
	    ((not) (cdr exp))
	    ((or) `(and ,(negate (cadr exp)) ,(negate (caddr exp))))
	    ((and) `(or ,(negate (cadr exp)) ,(negate (caddr exp))))
	    ((implies) (negate `(or ,(negate (cadr exp)) ,(caddr exp))))
	    (otherwise `(not ,exp))
	    )
    `(not ,exp)
    )
  )

(defun imply-exp (exp)
  (if (listp exp)
      (case (car exp)
	    ((implies) `(or ,(negate (imply-exp (cadr exp))) ,(imply-exp (caddr exp))))
	    (otherwise (mapcar #'imply-exp exp))
	    )
    exp
    )
  )

(defun prop-not (exp)
  (if (listp exp)
      (case (car exp)
	    ((not) (negate (cadr exp)))
	    (otherwise (mapcar #'prop-not exp))
	    )
    exp
    )
  )

(defun push-or (exp)
  (if (listp exp)
      (case (car exp)
	    ((or)
	     (let ((sub1 (cadr exp))
		   (sub2 (caddr exp)))
	       (cond ((and (listp sub1) (eq (car sub1) 'and))
		      (push-or (dist-or sub2 sub1))
		      )
		     ((and (listp sub2) (eq (car sub2) 'and))
		      (push-or (dist-or sub1 sub2))
		      )
		     (t (mapcar #'push-or exp))
		     )
	       )
	     )
	    (otherwise (mapcar #'push-or exp))
	    )
    exp
    )
  )

(defun dist-or (val and-exp)
  `(and (or ,val ,(cadr and-exp)) (or ,val ,(caddr and-exp)))
  )

(defun iter-push-or (exp)
  (let ((new-exp (push-or exp)))
    (if (not (equal exp new-exp))
	(iter-push-or new-exp)
      exp
      )
    )
  )

(defun substitute (var tar exp)
  (if (listp exp)
      (cond
       ((eq var (car exp)) (cons tar ((lambda (e) (substitute var tar e)) (cdr exp))))
       (t (mapcar (lambda (e) (substitute var tar e)) exp)))
    (if (eq var exp) tar exp)))

(defun make-mapping (deps label)
  (if deps
      (cons (intern (concatenate 'string "G" (write-to-string label))) deps)
    (intern (concatenate 'string "U" (write-to-string label)))
    )
  )

(defun remove-exists (exp)
  (defparameter *label* 0) 
  (labels ((skolemise (expr deps)
		    (if (listp expr)
			(case (car expr)
			      ((all) (mapcar (lambda (e) (skolemise e (cons (cadr expr) deps))) expr))
			      ((exists) (progn (defparameter *label* (1+ *label*))
					       (substitute (cadr expr) (make-mapping deps *label*) (caddr expr))))
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
							(intern (concatenate 'string "W" (write-to-string *label*)))
							(caddr expr))))
			      (otherwise (mapcar #'rm-univ expr)))
		      expr)))
	  (rm-univ exp)))

(defun cnf (exp)
 (iter-push-or (remove-all (remove-exists (prop-not (imply-exp exp))))))
