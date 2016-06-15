(in-package "ACL2")

#||
Update: there is are two more publicly-exposed functions, called
is-valid-http-url and is-valid-ftp-url. See example calls below.

ACL2 !>(is-valid-http-url "http://www.utexas.edu/grades?curve=no#ok")
T
ACL2 !>(is-valid-http-url "https://www.utexas.edu/grades?curve=no#ok")
T
ACL2 !>(is-valid-http-url "ftp://www.utexas.edu/grades?curve=no#ok")
NIL
ACL2 !>(is-valid-http-url "http:/")
NIL
||#

#||
Update: there is now a new publicly-exposed function, called
parse-url-by-template. Here are two example invocations:

ACL2 !>(parse-url-by-template  (list
                                (cons :scheme "://")
                                (cons :host "/")
                                (cons :path "?")
                                (cons :query "#")
                                (cons :fragment "")) "http://www.utexas.edu/grades?curve=no#ok")
((:SCHEME . "http")
 (:HOST . "www.utexas.edu")
 (:PATH . "grades")
 (:QUERY . "curve=no")
 (:FRAGMENT . "ok"))
ACL2 !>(parse-url-by-template  (list
                                (cons :scheme "://")
                                (cons :host "/")
                                (cons :path "?")
                                (cons :query "#")
                                (cons :fragment "")) "http://www.utexas.edu/grades")
((:SCHEME . "http")
 (:HOST . "www.utexas.edu")
 (:PATH . "grades")
 (:QUERY . "")
 (:FRAGMENT . ""))
||#

#||
The publicly-exposed functions for this book are separate-char-list and
unseparate-char-list-list. They serve to parse URLs based on a list of separators
provided as an argument and pretty-print a parsed URL, respectively. They are
inverses of each other, as shown by the theorem unseparate-separate.
Here are some examples that may prove instructive.

Parsing a URL:
ACL2 !>(let ((char-list (coerce "http://www.utexas.edu/grades" 'LIST))
      (separators (list (coerce "://" 'LIST) (coerce "/" 'LIST)))
      (field-separator-list nil))
  (separate-char-list
   char-list
   separators
   field-separator-list))
((#\h #\t #\t #\p)
 (#\: #\/ #\/)
 (#\w #\w #\w #\.
      #\u #\t #\e #\x #\a #\s #\. #\e #\d #\u)
 (#\/)
 (#\g #\r #\a #\d #\e #\s))

Pretty-printing a parsed URL:
ACL2 !>(let ((char-list (coerce "http://www.utexas.edu/grades" 'LIST))
      (separators (list (coerce "://" 'LIST) (coerce "/" 'LIST)))
      (field-separator-list nil))
  (unseparate-char-list-list (separate-char-list
                              char-list
                              separators
                              field-separator-list)))
(#\h #\t #\t #\p #\: #\/ #\/ #\w
     #\w #\w #\. #\u #\t #\e #\x #\a #\s #\.
     #\e #\d #\u #\/ #\g #\r #\a #\d #\e #\s)

Coercing the pretty-printed URL back to a string:
ACL2 !>(let ((char-list (coerce "http://www.utexas.edu/grades" 'LIST))
      (separators (list (coerce "://" 'LIST) (coerce "/" 'LIST)))
      (field-separator-list nil))
  (coerce (unseparate-char-list-list (separate-char-list
                                      char-list
                                      separators
                                      field-separator-list)) 'STRING))
"http://www.utexas.edu/grades"

||#

(include-book "std/lists/top" :dir :system)

(defun consume-separator (char-list separator)
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
(defun consume-through-separator (char-list separator backwards-field)
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
    (consp char-list)
    ))

;; (in-theory (disable consume-through-separator))

(defun separate-char-list (char-list separator-list field-separator-list)
  (declare (xargs :measure (len separator-list)))
  ;;endp requires true-listp
  (if (endp separator-list)
      ;; no more separators!
      (reverse (cons char-list field-separator-list))
    ;;still some separators
    (mv-let (a b c) (consume-through-separator char-list
					       (car separator-list)
					       nil)
	(declare)
      (if c
	  ;; the separator was not found
	  (reverse (cons char-list field-separator-list))
	;; the separator was found, so let's recurse
	(separate-char-list a
			    (cdr separator-list)
			    (cons (car separator-list) (cons b field-separator-list)))))))

(in-theory (enable separate-char-list))

(defun unseparate-char-list-list (field-separator-list)
  (if (endp field-separator-list)
      ;;no more fields. this can happen even when there are yet
      ;;separators.
      nil
    (append
     (car field-separator-list)
     (unseparate-char-list-list (cdr field-separator-list)))))

(defun character-list-listp (separators)
    (cond
     ((atom separators) (equal separators nil))
     (t (and
         (character-listp (car separators))
         (character-list-listp (cdr separators))))))

(defthm consume-separator-gigo
  (implies (character-listp char-list)
	   (mv-let (a b) (consume-separator char-list separator)
             (declare (ignore b))
             (character-listp a)))
  :hints (("Goal" :in-theory (enable consume-separator))))

(defthm
  consume-through-separator-gigo
  (implies (and (character-listp char-list) (character-listp backwards-field))
           (mv-let (a b c)
             (consume-through-separator char-list separator backwards-field)
             (declare (ignore b) (ignore c))
             (character-listp a)))
  :hints (("Goal" :in-theory (enable consume-through-separator))))

#||
(let ((char-list (coerce "http://www.utexas.edu/grades" 'LIST))
      (separators (list (coerce "://" 'LIST) (coerce "/" 'LIST)))
      (field-separator-list nil))
  (implies (and
            (character-listp char-list)
            (character-list-listp separators)
            (character-list-listp field-separator-list)
            )
	   (equal
	    (unseparate-char-list-list (reverse (cons char-list field-separator-list)))
	    (unseparate-char-list-list
	     (separate-char-list
              char-list
              separators
              field-separator-list)))))
||#

(defthm unseparate-char-list-list-append
  (equal (unseparate-char-list-list (append x y))
         (append (unseparate-char-list-list x)
                 (unseparate-char-list-list y))))

(defthm actually-consumes-separator
  (mv-let (a b) (consume-separator char-list separator) (declare)
    (implies
     (not b)
     (equal
      (append separator a)
      char-list))))

(defthm unseparate-separate-lemma-lemma-lemma
 (implies
  (and (not (mv-nth 2
                    (consume-through-separator char-list separator backwards-field)))
       (character-listp char-list)
       (character-listp separator))
  (equal
   (append
    (mv-nth 1
            (consume-through-separator char-list separator backwards-field))
    separator
    (mv-nth 0
            (consume-through-separator char-list separator backwards-field)))
   (append (rev backwards-field) char-list))))

; To eliminate this skip-proofs, I'm pretty sure you'll need to replace the
; final argument of nil in consume-through-separator by backwards-field.
(defthm unseparate-separate-lemma-lemma
  (implies
   (and (not (mv-nth 2
                     (consume-through-separator char-list separator nil)))
        (character-listp char-list)
        (character-listp separator))
   (equal
    (append
     (mv-nth 1
             (consume-through-separator char-list separator nil))
     separator
     (mv-nth 0
             (consume-through-separator char-list separator nil)))
    char-list)))

(defthm character-listp-rev
  (implies (character-listp x)
           (character-listp (rev x))))

(defthm character-listp-mv-nth-1-consume-through-separator
  (implies (and (not (mv-nth 2
                             (consume-through-separator char-list separator
                                                        backwards-field)))
                (character-listp char-list)
                (character-listp separator)
                (character-listp backwards-field))
           (character-listp
            (mv-nth 1
                    (consume-through-separator char-list separator backwards-field)))))

(defthm unseparate-separate-lemma
  (implies (and
            (character-listp char-list)
            (character-list-listp separators)
            (character-list-listp field-separator-list)
            )
	   (equal
	    (unseparate-char-list-list
	     (separate-char-list
              char-list
              separators
              field-separator-list))
	    (unseparate-char-list-list (reverse (cons char-list field-separator-list))))))

(defthm unseparate-separate
  (implies (and
            (character-listp char-list)
            (character-list-listp separators)
            )
	   (equal
	    (unseparate-char-list-list
	     (separate-char-list
	      char-list
	      separators
	      nil))
	    char-list)))

(defun get-separators-from-template (template)
  (if (or (endp template) (endp (cdr template)))
      nil
    (cons (coerce (cdr (car template)) 'list) (get-separators-from-template (cdr template)))))

#||
(get-separators-from-template (list
                             (cons :template "://")
                             (cons :host "/")
                             (cons :path "?")
                             (cons :query "#")
                             (cons :fragment "")))
||#

(defun force-field-separator-list-into-template (template field-separator-list)
  (if (endp template)
      nil
    (let
        ((car-field-separator-list
          (if (endp field-separator-list) nil (car field-separator-list)))
         (cddr-field-separator-list
          (if (or (endp field-separator-list) (endp (cdr field-separator-list)))
              nil
            (cddr field-separator-list))))
      (cons (cons (car (car template)) (coerce car-field-separator-list 'string))
            (force-field-separator-list-into-template
             (cdr template)
             cddr-field-separator-list
             )))
    ))

(defun parse-url-by-template (template url)
  (force-field-separator-list-into-template
   template
   (separate-char-list (coerce url 'list) (get-separators-from-template template) nil)))

(defun is-valid-http-url (url)
  (let (
        (parsed-url (parse-url-by-template
                     (list
                      (cons :scheme "://")
                      (cons :host "/")
                      (cons :path "?")
                      (cons :query "#")
                      (cons :fragment ""))
                     url)))
    (and
     (consp parsed-url)
     (consp (car parsed-url))
     (equal (car (car parsed-url)) :scheme)
     (or (equal (cdr (car parsed-url)) "http") (equal (cdr (car parsed-url)) "https")))))

(defun is-valid-ftp-url (url)
  (let (
        (parsed-url (parse-url-by-template
                     (list
                      (cons :scheme "://")
                      (cons :host "/")
                      (cons :path "?")
                      (cons :query "#")
                      (cons :fragment ""))
                     url)))
    (and
     (consp parsed-url)
     (consp (car parsed-url))
     (equal (car (car parsed-url)) :scheme)
     (equal (cdr (car parsed-url)) "ftp"))))
