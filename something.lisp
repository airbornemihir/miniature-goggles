(defun extract-scheme-from-char-list (char-list backwards-scheme)
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

(defun extract-host-from-char-list (char-list backwards-host)
  (if (endp char-list) (mv char-list (REVERSE backwards-host)) ;; maybe we can prove that doing this gives an empty backwards-host
    (if (equal (car char-list) #\/)
	(mv (cdr char-list) (REVERSE backwards-host))
      (extract-host-from-char-list (cdr char-list) (cons (car char-list) backwards-host))
      )))

(defun extract-path-from-char-list (char-list backwards-path)
  (if (endp char-list) (mv char-list (REVERSE backwards-path)) ;; maybe we can prove that doing this gives an empty backwards-path
    (if (equal (car char-list) #\?)
	(mv (cdr char-list) (REVERSE backwards-path))
      (extract-path-from-char-list (cdr char-list) (cons (car char-list) backwards-path))
      )))

(defun extract-query-from-char-list (char-list backwards-query)
  (if (endp char-list) (mv char-list (REVERSE backwards-query)) ;; maybe we can prove that doing this gives an empty backwards-query
    (if (equal (car char-list) #\#)
	(mv (cdr char-list) (REVERSE backwards-query))
      (extract-query-from-char-list (cdr char-list) (cons (car char-list) backwards-query))
      )))

(defun legal-scheme-check (char-list)
  (or (endp char-list) ;; base case
      (and (characterp (car char-list)) ;; guard for Standard-char-p
	   (Standard-char-p (car char-list)) ;; guard for Alpha-char-p
	   (or (Alpha-char-p (car char-list)) ;; alphabet
	       (member (car char-list) (list #\+ #\. #\-))) ;; period, dash or plus
	   (legal-scheme-check (cdr char-list)))) ;; recurse
  )

(defun parse-url (url)
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
					   (cons :scheme (coerce b 'STRING))
					   (cons :host (coerce e 'STRING))
					   (cons :path (coerce g 'STRING))
					   (cons :query (coerce i 'STRING))
					   (cons :fragment (coerce h 'STRING)))
					  )
				  ))
		(list (cons :error "Illegal scheme.")))
	    (list (cons :error c))
	    )
	  ))

(defthm trouble-with-scheme
  (implies
   (mv-let (a b c) (extract-scheme-from-char-list (coerce url 'LIST) nil)
	   (declare (ignore a))
	   (or (not (equal c nil)) (not (legal-scheme-check b)) ))
   (equal (caar (parse-url url)) :error)
   ))

(defun url-scheme (urlstruct)
  (cdr (assoc :scheme urlstruct))) ;; how do we catch errors?

(defun url-host (urlstruct)
  (cdr (assoc :host urlstruct)))

(defun url-path (urlstruct)
  (cdr (assoc :path urlstruct)))

(defun url-query (urlstruct)
  (cdr (assoc :query urlstruct)))

(defun url-fragment (urlstruct)
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
   ))

(defun print-url (urlstruct)
  (if (assoc :error urlstruct)
      ""
    (if (and (equal (car (car urlstruct)) :scheme) (equal (car (car (cdr urlstruct))) :host))
	(concatenate 'string
		     (url-scheme urlstruct)
		     "://"
		     (url-host urlstruct)
		     (if (and (equal (car (car (cdr (cdr urlstruct)))) :path) (not (equal (cdr (car (cdr (cdr urlstruct)))) "")))
			 (concatenate 'string
				      "/"
				      (url-path urlstruct)
				      (if (and (equal (car (car (cdr (cdr (cdr urlstruct))))) :query) (not (equal (cdr (car (cdr (cdr (cdr urlstruct))))) "")))
					  (concatenate 'string
						       "?"
						       (url-query urlstruct)
						       (if (and (equal (car (car (cdr (cdr (cdr (cdr urlstruct)))))) :fragment) (not (equal (cdr (car (cdr (cdr (cdr (cdr urlstruct)))))) "")))
							   (concatenate 'string
									"#"
									(url-fragment urlstruct))
							 "" ;; when fragment is either out of whack or empty
							 ))
					"" ;; when query is either out of whack or empty
					))
		       "" ;; when path is either out of whack or empty
		       ))
      nil ;; when scheme or host are out of whack
      )))

(defun translate-url (url) (print-url (parse-url url)))

(defthm idempotent-translation
  (equal
   (translate-url url)
   (translate-url (translate-url url))))
