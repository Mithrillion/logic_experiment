(defun count-member (val list)
  (let ((ml (member val list)))
    (cond
     (ml (1+ (count-member val (cdr ml))))
     (t 0)
     )
    )
  )
