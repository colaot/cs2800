; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;; data definition for list of rationals
(defdata lor (listof rational))

;; returns the length of a given list
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

;; returns true if the element a is in the list
;; otherwise returns false
(definec in2 (a :all X :tl) :bool
  (and (consp X)
       (or (== a (first X))
           (in2 a (rest X)))))

;; removes the first occurence of a from the list
(definec del2 (a :all X :tl) :tl
  (cond ((endp X) nil)
        ((== a (car X)) (cdr X))
        (t (cons (car X) (del2 a (cdr X))))))

;; returns true if the two lists contain the same elements
;; regardless of their order
(definec permp (x :tl y :tl) :bool
  (cond ((endp x) (endp y))
        (t (and (in2 (car x) y)
                (permp (cdr x) (del2 (car x) y))))))

;; performs one pass of the bubble sort algorithm
;; swaps adjacent elements in the list if the first is greater
;; than the second
(definec bubble-sort (ls :lor) :lor
  (if (endp (cdr ls))
    ls
     (if (> (first ls) (second ls))
      (cons (second ls) (bubble-sort (cons (first ls) (cddr ls))))
      (cons (first ls) (bubble-sort (cons (second ls) (cddr ls)))))))

;; recursively calls bubble-sort until the measure function reaches 0
;; the number of call is equal to the size of the input list
(definec bubble-sort-r (ls :lor n :nat) :lor
  :ic (<= n (len2 ls))
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      ls
    (bubble-sort (bubble-sort-r ls (1- n)))))

;; calls the bubble-sort-r function passing the length of the list
;; in for the measure function
(definec bubble (ls :lor) :lor
  (bubble-sort-r ls (len2 ls)))

;; proves the inductive case to allow the next proof to pass
(defthm permp-ind
  (implies (lorp x)
           (permp (cdr x) (del2 (car x) (bubble-sort x)))))

;; proves that bubble-sort produces a permutation of the input list
(defthm permp-bubble-sort
  (implies (lorp x)
           (permp x (bubble-sort x))))#|ACL2s-ToDo-Line|#
