(include-book "std/lists/top" :dir :system)
(include-book "acl2s/cgen/top" :dir :system :ttags :all)
(acl2s-defaults :set testing-enabled t)

(defund consume-separator (char-list separator)
  (if (endp separator)
      ;; this should not happen at the first call from
      ;; consume-until-separator - that function should always call
      ;; with a non-nil separator. rather, this should mark the base
      ;; case where we don't need to consume any more
      (mv char-list nil)
    ;; still something to consume
    (if (or (endp char-list)
	    (not (equal (car char-list) (car separator))))
	;;ouch! we want to consume but we cannot!
	(mv char-list t)
      ;; so far so good. let's recurse.
      (consume-separator (cdr char-list) (cdr separator)))))

;; there's a difference between consuming the separator and finding
;; nothing afterwards, and not even finding the separator
(defund consume-through-separator (char-list separator backwards-field)
  (if (endp char-list)
      ;;first base case
      ;;separator not found
      ;;we assume there are no empty separators
      (mv char-list (reverse backwards-field) t) ;; char-list is nil here
    (if (equal (car char-list) (car separator))
	;; second base case
	;; we assume that once we've seen the first character of the separator,
	;; it is an error for the rest not to follow
	(mv-let (a b) (consume-separator char-list separator)
		(declare)
		(if b
		    ;; error thrown by consume-separator
		    ;; separator not found
		    (mv char-list (reverse backwards-field) b) ;; b is t here
		  ;; no error thrown by consume-separator
		  (mv a (reverse backwards-field) b)))
      ;; induction case
      (consume-through-separator
       (cdr char-list)
       separator
       (cons (car char-list) backwards-field)))))

(defthm list-fix-nil (iff (equal (list-fix x) nil) (atom x)))

(in-theory (enable consume-through-separator))

(defthm no-error-consuming-through-separator
  (implies
   (mv-let (a b c) (consume-through-separator char-list separator nil)
     (declare (ignore a) (ignore b))
     (not c))
   ;; (and
    (consp char-list)
    ;; (mv-let (a b) (consume-separator char-list separator)
    ;;   (declare (ignore a))
    ;;   (not b)))
    ))

(in-theory (disable consume-through-separator))

(defund separate-char-list (char-list separator-list field-list)
  (declare (xargs :measure (len separator-list)))
  ;;endp requires true-listp
  (if (endp separator-list)
      ;; no more separators!
      (reverse (cons char-list field-list))
    ;;still some separators
    (mv-let (a b c) (consume-through-separator char-list
					       (car separator-list)
					       nil)
	(declare)
      (if c
	  ;; the separator was not found
	  (reverse (cons char-list field-list))
	;; the separator was found, so let's recurse
	(separate-char-list a
			    (cdr separator-list)
			    (cons b field-list))))))

(defthm no-separator-one-field
  (implies (not (consp separator-list))
	   (equal (len (separate-char-list char-list separator-list field-list))
		  (+ 1 (len field-list))))
  :hints (("Goal" :in-theory (enable separate-char-list))))

(in-theory (enable separate-char-list))

(defthm separators-between-fields
  (<=
   (len (separate-char-list char-list separator-list field-list))
   (+ 1 (len field-list) (len separator-list)))
  ;; :hints (("Goal"
  ;; 	   :induct (and
  ;; 		    ;; (len field-list)
  ;; 		    (len separator-list)))
  ;; 	  ("Subgoal *1/1"
  ;; 	   :in-theory (enable separate-char-list)))
  )

(defun unseparate-char-list (separator-list field-list)
  (if (endp field-list)
      ;;no more fields. this can happen even when there are yet
      ;;separators.
      nil
    (append
     (car field-list)
     (if (endp separator-list)
	 nil
       (append
	(car separator-list)
	(unseparate-char-list (cdr separator-list) (cdr field-list)))))))

(defun is-separator-list (separators)
    (cond
     ((consp separators) (character-listp (car separators)))
     (t (equal separators nil))))

(thm
 (mv-let (a b c) (consume-through-separator char-list (car separators) nil)
   (declare) 
   (implies
    (and
     (consp separators)
     (not c)
     (not (true-listp a))
     (true-listp char-list)
     (character-listp (car separators)))
    (equal
     (unseparate-char-list
      separators
      (separate-char-list a (cdr separators) (list b)))
     char-list))))

;; thanks to cgen, i get it
;; this theorem is messed up in the event that the first separator doesn't even
;; appear in the list
(defthm unseparate-separate
  (implies (and
            (true-listp char-list)
            (is-separator-list separators)
            )
	   (equal
	    (unseparate-char-list
	     separators
	     (separate-char-list
	      char-list
	      separators
	      nil))
	    char-list)))