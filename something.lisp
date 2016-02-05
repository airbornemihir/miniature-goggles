(defund extract-scheme-from-char-list (char-list backwards-scheme)
  (if (endp char-list) (mv char-list (REVERSE backwards-scheme) "That's all? Your URL is just a scheme!") ;; error!
    (if (equal (car char-list) #\:)
	(if (or
	     (or (endp (cdr char-list)) (not (equal (cadr char-list) #\/)))
	     (or (endp (cddr char-list)) (not (equal (caddr char-list) #\/)))) ;; error!
	    (mv char-list (REVERSE backwards-scheme) "Your scheme is not followed by ://")
	  (mv (cdddr char-list) (REVERSE backwards-scheme) nil))
      (extract-scheme-from-char-list
       (cdr char-list)
       (cons (car char-list) backwards-scheme))
      )
    ))

(defund extract-host-from-char-list (char-list backwards-host)
  (if (endp char-list) (mv char-list (REVERSE backwards-host)) ;; maybe we can prove that doing this gives an empty backwards-host
    (if (equal (car char-list) #\/)
	(mv (cdr char-list) (REVERSE backwards-host))
      (extract-host-from-char-list (cdr char-list) (cons (car char-list) backwards-host))
      )))

(defund extract-path-from-char-list (char-list backwards-path)
  (if (endp char-list) (mv char-list (REVERSE backwards-path)) ;; maybe we can prove that doing this gives an empty backwards-path
    (if (equal (car char-list) #\?)
	(mv (cdr char-list) (REVERSE backwards-path))
      (extract-path-from-char-list (cdr char-list) (cons (car char-list) backwards-path))
      )))

(defund extract-query-from-char-list (char-list backwards-query)
  (if (endp char-list) (mv char-list (REVERSE backwards-query)) ;; maybe we can prove that doing this gives an empty backwards-query
    (if (equal (car char-list) #\#)
	(mv (cdr char-list) (REVERSE backwards-query))
      (extract-query-from-char-list (cdr char-list) (cons (car char-list) backwards-query))
      )))

(defund legal-scheme-check (char-list)
  (or (endp char-list) ;; base case
      (and (characterp (car char-list)) ;; guard for Standard-char-p
	   (Standard-char-p (car char-list)) ;; guard for Alpha-char-p
	   (or (Alpha-char-p (car char-list)) ;; alphabet
	       (member (car char-list) (list #\+ #\. #\-))) ;; period, dash or plus
	   (legal-scheme-check (cdr char-list)))) ;; recurse
  )

(defund parse-url (url)
  (if (stringp url)
      (mv-let (a b c)
	      (extract-scheme-from-char-list (coerce url 'LIST) nil)
	      (if (equal c nil)
		  (if (legal-scheme-check b)
		      (mv-let (d e)
			      (extract-host-from-char-list a nil)
			      (mv-let (f g)
				      (extract-path-from-char-list d nil)
				      (mv-let (h i)
					      (extract-query-from-char-list f nil)
					      (list
					       (cons :scheme b)
					       (cons :host e)
					       (cons :path g)
					       (cons :query i)
					       (cons :fragment h))
					      )
				      ))
		    (list (cons :error "Illegal scheme.")))
		(list (cons :error c))
		)
	      )
    (list (cons :error "Not a string."))
    ))

(defthm trouble-with-scheme
  (implies
   (mv-let (a b c) (extract-scheme-from-char-list (coerce url 'LIST) nil)
	   (declare (ignore a))
	   (or c (not (legal-scheme-check b)) ))
   (assoc :error  (parse-url url))
   )
  :hints (("Goal" :in-theory (enable parse-url))))

(defund url-scheme (urlstruct)
  (cdr (assoc :scheme urlstruct))) ;; how do we catch errors?

(defund url-host (urlstruct)
  (cdr (assoc :host urlstruct)))

(defund url-path (urlstruct)
  (cdr (assoc :path urlstruct)))

(defund url-query (urlstruct)
  (cdr (assoc :query urlstruct)))

(defund url-fragment (urlstruct)
  (cdr (assoc :fragment urlstruct)))

(defthm fields-are-all-there
  (implies
   (not (and
	 (assoc :scheme (parse-url url))
	 (assoc :host (parse-url url))
	 (assoc :path (parse-url url))
	 (assoc :query (parse-url url))
	 (assoc :fragment (parse-url url))))
   (assoc :error (parse-url url))
   )
  :hints (("Goal" :in-theory (enable parse-url))))

(defund print-url (urlstruct)
  (coerce 
	  (if (assoc :error urlstruct)
	      nil ;; if :error is around, that means our struct isn't proper, so we return an empty string. 
	    (append
	     (url-scheme urlstruct)
	     (list #\: #\/ #\/)
	     (url-host urlstruct)
	     (if (not (url-path urlstruct))
		 nil ;; when path is empty
	       (append
		(list #\/)
		(url-path urlstruct)
		(if (not (url-query urlstruct))
		    nil ;; when query is empty
		  (append
		   (list #\?)
		   (url-query urlstruct)
		   (if (not (url-fragment urlstruct))
		       nil ;; when fragment is empty
		     (append
		      (list #\#)
		      (url-fragment urlstruct))
		     ))
		  ))
	       ))
	    )
	  'string)
  )

(defund translate-url (url) (print-url (parse-url url)))

(in-theory (disable url-fragment url-query url-path url-host url-scheme))

(defthm empty-url-generates-error
  (IMPLIES (EQUAL "" URL)
	   (MV-NTH 2
		   (EXTRACT-SCHEME-FROM-CHAR-LIST (COERCE URL 'LIST)
						  NIL)) 
	   ))

(defund has-properly-separated-scheme (char-list)
  (if (endp char-list) nil ;; error!
    (if (equal (car char-list) #\:)
	(if (or
	     (or (endp (cdr char-list)) (not (equal (cadr char-list) #\/)))
	     (or (endp (cddr char-list)) (not (equal (caddr char-list) #\/)))) ;; error!
	    nil
	  t)
      (has-properly-separated-scheme
       (cdr char-list))
      )
    ))

(defthm aerg
  (implies (has-properly-separated-scheme char-list)
	   (equal (MV-NTH 1 (EXTRACT-SCHEME-FROM-CHAR-LIST char-list (LIST x)))
		  (cons x (MV-NTH 1 (EXTRACT-SCHEME-FROM-CHAR-LIST char-list nil)))))
  :hints (("Goal" :in-theory (enable extract-scheme-from-char-list
				     has-properly-separated-scheme))))

(defthm append-extract-scheme
  (implies (has-properly-separated-scheme char-list)
	   (equal (APPEND
		   (MV-NTH 1
			   (EXTRACT-SCHEME-FROM-CHAR-LIST char-list NIL))
		   '(#\: #\/ #\/)
		   (mv-nth 0 (EXTRACT-SCHEME-FROM-CHAR-LIST char-list NIL)))
		  char-list))
  :hints (("Goal" :in-theory (enable has-properly-separated-scheme
				     extract-scheme-from-char-list))))

(defthm strict-url-translation-identity
  (implies
   (not (assoc :error (parse-url url)))
   (equal
    (translate-url url)
    url))
  :hints (("Goal" :in-theory (enable translate-url
				     parse-url
				     print-url
				     url-scheme
				     url-host
				     url-path
				     url-query)))
  ;; :hints (("Subgoal 1'''" :use empty-url-generates-error))
  )

(defthm idempotent-translation
  (equal
   (translate-url (translate-url url))
   (translate-url url)))
