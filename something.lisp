(defun rev (list1)
  (if (endp list1) nil
    (append (rev (cdr list1)) (cons (car list1) nil))
    ))

(defun extract-scheme-from-char-list (char-list backwards-scheme)
  (if (endp char-list) (mv char-list backwards-scheme t) ;; error!
    (if (equal (car char-list) #\:)
	(if (or
	     (or (endp (cdr char-list)) (not (equal (cadr char-list) #\/)))
	     (or (endp (cddr char-list)) (not (equal (caddr char-list) #\/)))) ;; error!
	    (mv char-list backwards-scheme t)
	  (mv (cdddr char-list) backwards-scheme nil))
      (extract-scheme-from-char-list
       (cdr char-list)
       (cons (car char-list) backwards-scheme))
      )
    ))

(defun extract-host-from-char-list (char-list backwards-host)
  (if (endp char-list) (mv char-list backwards-host) ;; maybe we can prove that doing this gives an empty backwards-host
    (if (equal (car char-list) #\/)
	(mv (cdr char-list) backwards-host)
      (extract-host-from-char-list (cdr char-list) (cons (car char-list) backwards-host))
      )))

(defun extract-path-from-char-list (char-list backwards-path)
  (if (endp char-list) (mv char-list backwards-path) ;; maybe we can prove that doing this gives an empty backwards-path
    (if (equal (car char-list) #\?)
	(mv (cdr char-list) backwards-path)
      (extract-path-from-char-list (cdr char-list) (cons (car char-list) backwards-path))
      )))

(defun extract-query-from-char-list (char-list backwards-query)
  (if (endp char-list) (mv char-list backwards-query) ;; maybe we can prove that doing this gives an empty backwards-query
    (if (equal (car char-list) #\#)
	(mv (cdr char-list) backwards-query)
      (extract-query-from-char-list (cdr char-list) (cons (car char-list) backwards-query))
      )))

(defun parse-url (url)
  (mv-let (a b c)
	  (extract-scheme-from-char-list (coerce url 'LIST) nil)
	  (if (equal c nil)
	      (mv-let (d e)
		      (extract-host-from-char-list a nil)
		      (mv-let (f g)
			      (extract-path-from-char-list d nil)
			      (mv-let (h i)
				      (extract-query-from-char-list f nil)
				      (list
				       (cons :scheme (coerce (rev b) 'STRING))
				       (cons :host (coerce (rev e) 'STRING))
				       (cons :path (coerce (rev g) 'STRING))
				       (cons :query (coerce (rev i) 'STRING))
				       (cons :fragment (coerce h 'STRING)))
				      )
			      ))
	    (list (cons :error "That's all? Your URL is just a scheme!"))
	    )
	  ))

(defthm trouble-with-scheme
  (implies
   (mv-let (a b c) (extract-scheme-from-char-list (coerce url 'LIST) nil)
	   (declare (ignore a) (ignore b)) (equal c t))
   (equal (caar (parse-url url)) :error)
   ))
