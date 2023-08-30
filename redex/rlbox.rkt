#lang racket
(require rackunit)
(provide (all-defined-out))
(require redex/reduction-semantics)
;; (require racket/control)

(caching-enabled? #f) ; don't cache so that parameters are consulted
(define *D* (make-parameter (term ()))) ; struct table
(define *H* (make-parameter (term ()))) ; global heap (for type system)
(define *Fs* (make-parameter (term ()))) ; global function definition table
(define *N* (make-parameter (term ()))) ; global number value
(define *eFs* (make-parameter (term ()))) ; global erased function definition table

(define *debug* (make-parameter (term #f))) ; debug flag

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This extends the POST model in a few ways
;; - let variable lookup that avoids substitution
;; - n-ary let
;; - null-terminated arrays that use the let lookup to update array bounds
;; - standard conditional form that can be used to safely check terminator
;; - function pointers and calls


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax
;; TODO: modify the syntax to match the paper.

;; heap max cardinality 2^n
;; one heap, but two heaps created by splitting it using 2^(n - 1). Basically, split the one heap into a checked region and a tainted/unchecked region.
;; c heap and u heap. Everytime when someone compiles, mallocs, in CoreC, the cardinality increases (for the region it belongs to).
;; It needs to remember the cardinality of both regions.
;; in our world, unchecked and tainted are basically the same, but tainted can be used outside of the unchecked region
;; We don't need to worry about null-terminated pointers. So I don't need to worry about strlen.
;; figure 13:
;; left side is checked c code, right side is core c code
;; helper map (gamma). Rho can go, since no null-terminated pointers.
;; In NT-array.rkt ty>>>, those set of rules (line ~1600, typing) are both type rules and compilation rules, which compiles checked c to core c. This is written based on checked-c
;; Now we need to split it into two (the checked and tainted/unchecked heaps).
;; Copy the code into rlbox and make some modifictions (according to what we want, which is splitting into two heaps).
;; First copy the code over, then modify it based on the rules in the paper (in figure 13)
;; insert bounds check and insert null check. Since we have two heaps, we need to add one more check (similar to the bounds check), but for a fixed bounds (2^(n - 1))
;; if it's in c, I check if where it's going into is within 0 to 2^(n - 1), and if it's u or t, I check if the region it's going into in the heap is from 2^(n - 1) to 2^n
;; Do this for C-Assign and C-Def
;; Malloc in checked c needs to compile to calloc in core-c
;; just compile malloc to malloc, but I need to add an additional flag to see if it goes to c or u/t.
;; Change the c's to k.
;; move the needed code from ntarray to rlbox

(define-language CoreChkC+
  (m ::= c u)
  (K ::= m t)
  (τ ::= int (ptr K ω))
  (ω ::= τ (struct T)
     (array le he τ)
     (ntarray le he τ)
     ;; NEW:
     (fun (x ...) τ (τ ...)))

  ;; NEW
  ;; normalized types
  (vτ ::= int (ptr K vω))
  (vω ::= vτ (struct T)
     (array l h vτ)
     (ntarray l h vτ)
     ;; NEw:
     (fun (x ...) τ (τ ...)))

  (e ::= (n : τ) x (let x = e in e) (malloc K ω) (cast τ e)
     (e + e) (& e → f) (* e) (* e = e)
     ;; NEW checked expr
     ;;(unchecked (x ...) e) (checked (x ...) e)
     (to m e)
     (if e e e)
     (strlen e)
     (free e)
     ;; (dyn-bound-cast τ e) I can remove this one
     (call e e ...))
     ;; NEW switching operation
     ;;()
  
  ;; erased expressions
<<<<<<< Updated upstream
  (ee ::=  i eS)
=======
  (ee ::=  i eS) ;; i is an integer, and eS is another erased expression
>>>>>>> Stashed changes

  ;; NEW:
  (le he ::= l ls)
  (ls hs ::= (x + l))

  ;;NEW functions
  (Fs ::= (F F))
  (F ::= ((defun ((x : τ) ... e) : τ) ...))

  (n k ::= natural)
  (l h i ::= integer)
  (D ((T fs) ...))
  (fs ((vτ f) (vτ f) ...))
  (x eff f T ::= variable-not-otherwise-mentioned)

  ;;(Hs ::= (H H))
  (H ::= ((n : vτ) ...))

  ;;(eHs ::= (eH eH))
  (eH ::= (n ...))
  (eFs ::= (eF eF))
  (eF ::= ((defun ee x ... ee) ...))
  ;;NEW functions
  (r ::= e ε)
  (er ::= ee ε)
  (ε ::= Null Bounds)
  (E ::= hole (let x = E in e) (let x = (n : vτ) in E) (E + e) ((n : vτ) + E) ;; this defines a context and defines the semantics
     (& E → f) (dyn-bound-cast Eτ e) (dyn-bound-cast vτ E) (cast Eτ e) (cast vτ E) (* E) (* E = e) (* (n : vτ) = E)
     ;;(unchecked (x ...) E) (checked (x ...) E)
     (to m E)
     (if E e e)
     (strlen E)
     (malloc K Eω)
     (free E)
     (n : Eτ)
     ;;New for functions
     (call E e ...)
     (call (n : vτ) (n : vτ) ... E e ...))

  (Eω ::= (array hole he τ)
       (array l hole τ)
       (array l h Eτ)
       (ntarray hole he τ)
       (ntarray l hole τ)
       (ntarray l h Eτ)
       Eτ)

  (Eτ ::= (ptr K Eω))

  ;; A Potential Redex (pr) is a term of the form matching the
  ;; premises of the ⊢→ basic reduction relation.
  (pr ::=
      (let x = (n : vτ) in (in-hole E (x + i)))
      (let x = (n : vτ) in (in-hole E (strlen x)))
      (let x = (n : vτ) in (n_2 : vτ_2))
      (let x = (n : vτ) in (in-hole E x))
      (let x = (n : vτ) in (in-hole E (* x)))
      (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x)))
      (* (n : vτ))
      (* (n : vτ) = (n_1 : vτ_1))
      (strlen (n : vτ))
      (call (n_1 : vτ_1) (n_args : vτ_args) ...)
      (dyn-bound-cast vτ (n : vτ_′))
      ((n_1 : vτ_1) + (n_2 : vτ_2))
      (cast vτ (n : vτ_′))
      (& (n : vτ) → f_i)
      (malloc K vω)
      (free (n : vτ))
      ;;(unchecked (x ...) (n : vτ))
      ;; NEW checked expr
      ;;(checked (x ...) (n : vτ))
      (to m (n : vτ))
      (if (n : vτ) e_1 e_2))

 ;; result
  (eE ::= hole
      (eE + ee) (i + eE)
      (x = eE)
      (eE - ee) (i - eE)
      (star-l eE) (star-r eE)
      (star-l eE = ee) (star-r eE)
      (star-l i = eE) (star-r i = eE)
      (eE <=? ee)
      (i <=? eE)
      (if eE ee ee)
      (strlen eE)
      (free eE)
      (let x = eE in ee)
      (let x = i in eE)

      ;;New for functions
      (call eE ee ...)
      (call ee ee ... eE ee ...))


  ;; erased serious terms
 (eS ::= x (malloc-lr ee) ;; (malloc-l ee) (malloc-r ee) is this the right way to combine them? Or can I just combine these by swapping to the nt-array version?
      (ee + ee) (ee - ee)
      (star-l ee) (star-r ee)
      (star-l ee = ee) (star-r ee = ee)
      (x = ee)
      (ee <=? ee)
      (if ee ee ee)
      (let x = ee in ee)
      (strlen-l ee) (strlen-r ee)
      (free-l ee) (free-r ee)
;      (call-l ee ee ...) then I need to combine these two
;      (call-r ee ee ...)
      (call-lr ee ee ...)
      ;; exceptions
      (enull) (ebounds))

;; eK is a context
;; TODO: star-l and star-r
  (eK ::= hole
      pop
<<<<<<< Updated upstream
      (malloc []) ;; 
=======
      (malloc-lr []) ;; 
>>>>>>> Stashed changes
                  ;; (malloc-l [])
                  ;; (malloc-r [])
      ([] + ee) (i + [])
      (x = [])
      ([] - ee) (i - [])
      (star-l []) (star-r [])
      (star-l [] = ee) (star-r [] = ee)
      (star-l i = []) (star-r i = [])
      ([] <=? ee)
      (i <=? [])
      (if [] ee ee)
      (strlen-l [])
      (strlen-r [])
      (free-l [])
      (free-r [])
      (let x = [] in ee)
      ;;New for functions
      (call-l [] ee ...)
      (call-l ee ee ... [] ee ...)
      (call-r [] ee ...)
      (call-r ee ee ... [] ee ...)
      (call [] ee ...)
      (call ee ee ... [] ee ...))


  (eΣ ::= ((x_!_0 i_0) ...))

  ;; auxiliary type for compilation
  (cE ::= (compatible-closure-context ee))



  ;; static
  (Γ ::= ((x = maybe-e : τ) ...))
  (maybe-e ::= e none)
  (σ ::= ((n : τ) ...))

  ;; map from a checked array to the variable that stores its upper bound
  (ρ ::= ((x_!_0 (x_!_1 x_!_2)) ...))

  ;; only as a helper
  ;; (boolean ::= #t #f)

  #:binding-forms
  (let x = ee in ee_body #:refers-to x)
  (let x = e in e_body #:refers-to x)
  ; ':' can't appear twice. yet another redex bug?
  ; modified to allow let*-like behavior
  (defun ((x : τ) #:...bind (args x (shadow args x)) e_body #:refers-to args) _ τ_res #:refers-to args)
  (defun x ... ee #:refers-to (shadow x ...))
  (eH ((x i) ...) ee #:refers-to (shadow x ...) eH))

(default-language CoreChkC+)


(define ~~>
  (reduction-relation
   CoreChkC+ #:domain (H r)
   (--> (H e) (H_′ r_′) (judgment-holds (⊢↝ (H e) (H_′ r_′))))))

;; This needs fixing so that it doesn't use two heaps?
(define (---> m) ;; top
  (reduction-relation
   CoreChkC+
   #:domain (H r)
   (--> (H e) (H_′ r)
        (judgment-holds (⊢⟶ (H e ,m) (H_′ r))))))

(define --->cu
  (reduction-relation
   CoreChkC+
   #:domain (H r)
   (-->
    (H (in-hole E pr))
    (H_′ (in-hole E e_′))
    (judgment-holds (⊢↝/name (H pr) (H_′ e_′ any_name)))
    (computed-name (term any_name)))

   (-->
    (H (in-hole E pr))
    (H_′ ε)
    (judgment-holds (⊢↝/name (H pr) (H_′ ε any_name)))
    (computed-name (term any_name)))))

(define-judgment-form CoreChkC+
  #:contract (⊢↝/name (H e) (H r any))
  #:mode     (⊢↝/name I O)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; New rules

  [(⊢↝/name (H (let x = (n_0 : vτ_0) in (in-hole E (x + i_0))))
       (H (let x = (n_0 : vτ_0) in (in-hole E i_1))
          E-VarTy))
   (where i_1 ,(+ (term n_0) (term i_0)))
   E-VarTy]

  [(⊢↝/name (H (let x = (n_0 : vτ_0)  in (n_2 : vτ_2))) (H (n_2 : vτ_2) E-Let))
   E-Let]

  [(⊢↝/name (H (let x = (n : vτ) in (name e (in-hole E x)))) (H (let x = (n : vτ) in (in-hole E (n : vτ))) E-VarNonNT))
   (where #t (⊢non-nt-deref-or-strlen? vτ e))
   E-VarNonNT]

  ;; I need to fix these heap lookup so that it accepts K and it doesn't use m anymore
  
  [(⊢↝/name (H (let x = (n : vτ_1) in (in-hole E (* x)))) (H (let x = (n : vτ_2) in (in-hole E (n_′ : vτ_′))) E-VarNT-Incr))
   (where (ptr K _) vτ_1)
;   (where H (⊢heap-by-mode H m))
   (where (n_′ : vτ_′) (⊢heap-lookup H K n))
   (where #f ,(zero? (term n_′)))
   (where vτ_2 (⊢nt-incr vτ_1))
   E-VarNT-Incr]

  [(⊢↝/name (H (let x = (n : vτ_1) in (in-hole E (* x)))) (H (let x = (n : vτ_1) in (in-hole E (* (n : vτ_1)))) E-VarNT-Sub))
   (where (ptr K _) vτ_1)
;   (where H (⊢heap-by-mode H m))
   (side-condition ,(let ([i (term (⊢heap-lookup H K n))])
                      (or (not i)
                          (zero? (first i)))))
   E-VarNT-Sub]

  ;; this are just like their array counterparts
  [(⊢↝/name (H (* (n : vτ))) (H Bounds X-NTDerefOOB))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   X-NTDerefOOB]

  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_1))) (H Bounds X-NTAssignOOB))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-NTAssignOOB]

  [(⊢↝/name (H ((0 : vτ) + (n : vτ_′))) (H Null X-BinopNTNull))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   X-BinopNTNull]

  ;; file a bug report on microsoft/checkedc?
  [(⊢↝/name (H (strlen (0 : vτ))) (H Null X-StrNull))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   X-StrNull]

  [(⊢↝/name (H (strlen (n : vτ))) (H Bounds X-StrOOB))
   (where (ptr c (ntarray l h vτ_1)) vτ)
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   X-StrOOB]

  [(⊢↝/name (H (strlen (n : vτ))) (H Null X-StrTainted))
   (where (ptr t (ntarray l h vτ_1)) vτ)
;   (where H (⊢heap-by-mode H t))
   (where #f (⊢strlen n H))
   X-StrTainted] 

  ;; no longer about error states.
  ;; I changed this to accept K, may need some looking at
  ;; This is because we don't use m anymore.
  [(⊢↝/name (H (strlen (n : vτ))) (H (n_1 : int) E-Str))
   (where (ptr K (ntarray l h vτ_1)) vτ)
;   (where H (⊢heap-by-mode H m))
   (where n_1 (⊢strlen n K H))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(and (<= (term l) 0) (<= 0 (term h))))
   E-Str]

  [(⊢↝/name (H (call (n_1 : vτ_1) (n_args : vτ_args) ..._1))  (H Null X-FunTainted))
   (where (ptr t (fun _ _ _)) vτ_1) 
   (where #f (⊢fun-lookup (⊢fheap-by-mode t) n_1))
   X-FunTainted]

  
  [(⊢↝/name (H (call (n_1 : vτ_1) (n_args : vτ_args) ..._1))  (H (⊢build-call-stack e (x (n_args : vτ_args)) ...) E-Fun))
   (where (ptr m (fun _ _ _)) vτ_1) 
   (where (defun ((x : τ_2′) ..._1 e) : τ) (⊢fun-lookup (⊢fheap-by-mode m) n_1)) ;; defun no vτ_1 
   E-Fun]

  [(⊢↝/name (H (dyn-bound-cast vτ (n : vτ_′))) (H (n : vτ_′) E-DynCast)) ;; note that the annotation does not change
   (where #t (⊢bounds-within vτ vτ_′)) ;; only need the ntarray/array subsumption cases
   E-DynCast]

  [(⊢↝/name (H (dyn-bound-cast vτ (n : vτ_′))) (H Bounds X-DynCast))
   (where #f (⊢bounds-within vτ vτ_′))
   X-DynCast]
  
  ;; Old rules
  [(⊢↝/name (H ((n_1 : vτ_1) + (n_2 : vτ_2))) (H (n_3 : vτ_3) E-Binop))
   (where n_3 ,(+ (term n_1) (term n_2)))
   (where vτ_3 (⊢binop-type vτ_1 n_1 n_2))
   E-Binop]

  [(⊢↝/name (H (cast vτ (n : vτ_′))) (H (n : vτ) E-Cast))
   E-Cast]

  ;; Could ths way of changing them messed things up, since it isn't evaluating the expression.
  ;; This is in reference to replacing m with K, and making heap lookup accept K when calling it.
  [(⊢↝/name (H (* (n : vτ))) (H (n_1 : vτ_1) E-Deref))
   (where #t (⊢deref-ok? vτ))
   (where (ptr K _) vτ)
   ;;(where H (⊢heap-by-mode H m))
   (where (n_1 : _) (⊢heap-lookup H K n))
   (where vτ_1 (⊢deref-type-dyn ,(*D*) vτ))
   E-Deref]

  ;; the type stored on the heap musn't change
  ;; the type attached to n_1 can stay as the evaluation result because it's all on the stack
  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_1))) (H_′ (n_1 : vτ_1) E-Assign))
   (where #t (⊢assign-ok? vτ))
   (where (ptr m _) vτ)
;   (where H (⊢heap-by-mode H m))
   (where H_′ (⊢heap-update H n n_1))
   (where H_′ (⊢update-heap-by-mode H H_′ m))
   E-Assign]

  [(⊢↝/name (H (& (n : vτ) → f_i)) (H (n_0 : vτ_0) E-Amper))
   (where (n_0 : vτ_0) (⊢& vτ f_i n))
   E-Amper]

<<<<<<< Updated upstream
=======
  ;; I think these two mallocs are fine. No need to edit
>>>>>>> Stashed changes
  ;; I need to change these too to the if condition
  [(⊢↝/name (H (malloc m vω)) (H_′ (n_1 : (ptr c vω)) E-Malloc))
   (where (vτ_1 ...) (⊢types ,(*D*) vω))
;   (where H (⊢heap-by-mode H m))
   (where ((n : vτ) ...) H)
   (where H_′ ((n : vτ) ... (0 : vτ_1) ...))
   (where H_′ (⊢update-heap-by-mode H H_′ m))
   (where n_1 ,(add1 (length (term H))))
   (where #t (⊢malloc-type-wf vω))      ; making sure the lower bound is always 0
   (side-condition ,(positive? (term (⊢sizeof vω))))
   E-Malloc]

  [(⊢↝/name (H (malloc m vω)) (H (0 : (ptr c vω)) E-MallocZero))
   (where #t (⊢malloc-type-wf vω))      ; making sure the lower bound is always 0
   (side-condition ,(not (positive? (term (⊢sizeof vω)))))
   E-MallocZero]

  [(⊢↝/name (H (unchecked (n : vτ))) (H (n : vτ) E-Unchecked))
   E-Unchecked]

  [(⊢↝/name (H (* (n : vτ))) (H Bounds X-DerefOOB))
   (side-condition ,(not (zero? (term n))))
   (where (ptr c (array l h vτ_1)) vτ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-DerefOOB]

  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_1))) (H Bounds X-AssignOOB))
   (side-condition ,(not (zero? (term n))))
   (where (ptr c (array l h vτ_1)) vτ)
   (side-condition ,(not (and (<= (term l) 0) (< 0 (term h)))))
   X-AssignOOB]

  ;; issue with these maybe?
  [(⊢↝/name (H (* (n : vτ))) (H Null X-DerefTainted))
   (where (ptr t _) vτ)
;   (where H (⊢heap-by-mode H t))
   (where #f (⊢heap-lookup H n))
   X-DerefTainted] 
  
  [(⊢↝/name (H (* (0 : vτ))) (H Null X-DerefNull))
   (where (ptr c vω) vτ)
   X-DerefNull]

  [(⊢↝/name (H (* (n : vτ) = (n_1 : vτ_′))) (H Null X-AssignTainted))
   (where (ptr t _) vτ)
;   (where H (⊢heap-by-mode H t))
   (where #f (⊢heap-lookup H n))
   X-AssignTainted] 
  
  [(⊢↝/name (H (* (0 : vτ) = (n_1 : vτ_′))) (H Null X-AssignNull))
   (where (ptr c vω) vτ)
   X-AssignNull]

  [(⊢↝/name (H (& (n : vτ) → f)) (H Null X-AmperTainted))
   (where (ptr t _) vτ)
;   (where H (⊢heap-by-mode H t))
   (where #f (⊢heap-lookup H n))
   X-AmperTainted] 

  [(⊢↝/name (H (& (0 : vτ) → f)) (H Null X-AmperNull))
   (where (ptr c (struct T)) vτ)
   X-AmperNull]

  [(⊢↝/name (H ((0 : vτ) + (n : vτ_′))) (H Null X-BinopNull))
   (where (ptr c (array l h vτ_1)) vτ)
   X-BinopNull]

  [(⊢↝/name (H (if (n : vτ) e_1 e_2)) (H e_1 If-T))
   (side-condition ,(< (term 0) (term n)))
   If-T]
  [(⊢↝/name (H (if (n : vτ) e_1 e_2)) (H e_2 If-F))
   (side-condition ,(= (term 0) (term n)))
   If-F]

  [(⊢↝/name (H (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
       (H (let x = (n : (ptr c (ntarray l h_′ vτ))) in (in-hole E (n_1 : int))) E-VarNTstr))
   (where n_1 (⊢strlen n))
   (where h_′ ,(max (term h) (term n_1)))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(and (<= (term l) 0) (<= 0 (term h))))
   E-VarNTstr]

  [(⊢↝/name (H (let x = (0 : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
       (H Null E-VarNTNull))
   E-VarNTNull]

  [(⊢↝/name (H (let x = (n : (ptr c (ntarray l h vτ))) in (in-hole E (strlen x))))
            (H Bounds E-VarNTOOB))
   (side-condition ,(not (zero? (term n))))
   (side-condition ,(not (and (<= (term l) 0) (<= 0 (term h)))))
   E-VarNTOOB])

;; These need to be modified so that it does not take two heaps. These don't actually need to be modified.
(define-judgment-form CoreChkC+
  #:contract (⊢↝ (H e) (H r))
  #:mode     (⊢↝ I O)
  [(⊢↝ (H e) (H_′ r))
   (⊢↝/name (H e) (H_′ r any))])

(define-judgment-form CoreChkC+
  #:contract (⊢⟶ (H e m) (H r))
  #:mode     (⊢⟶ I O)
  [(where (in-hole E e_0) e) 
   (⊢↝ (H e_0) (H_′ e_0′))
   (where e_′ (in-hole E e_0′))
   (where m_′ (⊢mode E))
   (where #t (⊢check-mode m m_′))
   ------ C-Exp
   (⊢⟶ (H e m) (H_′ e_′))]

  [(where (in-hole E e_0) e)
   (⊢↝ (H e_0) (H_′ ε))
   (where m_′ (⊢mode E))
   (where #t (⊢check-mode m m_′))
   ------- C-Halt
   (⊢⟶ (H e m) (H_′ ε))])




(define-metafunction CoreChkC+
  ⊢join-type : Γ τ τ -> τ or #f
  [(⊢join-type Γ (ptr c (ntarray le_0 he_0 τ)) (ptr c (ntarray le_1 he_1 τ)))
   (ptr c (ntarray le_2 he_2 τ))
   (where le_0′ (⊢sub-bound Γ le_0))
   (where le_1′ (⊢sub-bound Γ le_1))
   (where he_0′ (⊢sub-bound Γ he_0))
   (where he_1′ (⊢sub-bound Γ he_1))
   (where le_2  (⊢join-lower le_0′ le_1′))
   (where he_2  (⊢join-upper he_0′ he_1′))]
  [(⊢join-type Γ (ptr c (array le_0 he_0 τ)) (ptr c (array le_1 he_1 τ)))
   (ptr c (array le_2 he_2 τ))
   (where le_0′ (⊢sub-bound Γ le_0))
   (where le_1′ (⊢sub-bound Γ le_1))
   (where he_0′ (⊢sub-bound Γ he_0))
   (where he_1′ (⊢sub-bound Γ he_1))
   (where le_2  (⊢join-lower le_0′ le_1′))
   (where he_2  (⊢join-upper he_0′ he_1′))]
  [(⊢join-type _ τ τ) τ]
  [(⊢join-type _ _ _) #f])

(define-metafunction CoreChkC+
  ⊢join-lower : le le -> le or #f
  [(⊢join-lower (x + i_0) (x + i_1))
   (x + i_2)
   (where i_2 ,(max (term i_0) (term i_1)))]
  [(⊢join-lower i_0 i_1)
   i_2
   (where i_2 ,(max (term i_0) (term i_1)))]
  [(⊢join-lower _ _) #f])

(define-metafunction CoreChkC+
  ⊢join-upper : he he -> he or #f
  [(⊢join-upper (x + i_0) (x + i_1))
   (x + i_2)
   (where i_2 ,(min (term i_0) (term i_1)))]
  [(⊢join-upper i_0 i_1)
   i_2
   (where i_2 ,(min (term i_0) (term i_1)))]
  [(⊢join-upper _ _)
   #f])

;; only performs substitution when the definition is a constant int
(define-metafunction CoreChkC+
  ⊢sub-bound : Γ le -> le
  [(⊢sub-bound _ l) l]
  [(⊢sub-bound (_ ... (x = (i : int) : _) _ ...) (x + l))
   ,(+ (term i) (term l))]
  [(⊢sub-bound _ le) le])




;; bounds-within : to-type from-type
;; dyn-bound-cast to-type (n : from-type)
(define-metafunction CoreChkC+
  ⊢bounds-within : vτ vτ -> #t or #f
  [(⊢bounds-within (ptr c (ntarray l_1 h_1 τ_1)) (ptr c (ntarray l_2 h_2 τ_2)))
   #t
   (side-condition (and (>= (term l_1) (term l_2))
                        (<= (term h_1) (term h_2))))
   or
   #f]
  [(⊢bounds-within (ptr c (array l_1 h_1 τ_1)) (ptr c (array l_2 h_2 τ_2)))
   #t
   (side-condition (and (>= (term l_1) (term l_2))
                        (<= (term h_1) (term h_2))))
   or
   #f]
  ;; is this default case ok?
  [(⊢bounds-within _ _)
   #t])

;; once we generalize to arbitrary bound expressions
;; should take the more generalized τ instead of vτ

(define-metafunction CoreChkC+
  ⊢binop-type : τ n n -> τ or #f
  [(⊢binop-type (ptr c (array l h τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (name τ int) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr m (struct T))) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr m int)) n_1 n_2) τ]
  [(⊢binop-type (name τ (ptr u (ntarray l h _))) n_1 n_2) τ]

  ;;  there's a lot of repetition in these rules
  ;; can we design a helper metafunction that encapsulates the common parts?
  [(⊢binop-type (ptr c (ntarray l h τ)) n_1 n_2)
   (ptr c (ntarray l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (array (x + l) h τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (+ (term x) (term l)) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (array l (x + h) τ)) n_1 n_2)
   (ptr c (array l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (+ (term x) (term h)) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (ntarray (x + l) h τ)) n_1 n_2)
   (ptr c (ntarray l_2 h_2 τ))
   (where l_2 ,(- (+ (term x) (term l)) (term n_2)))
   (where h_2 ,(- (term h) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (ptr c (ntarray l (x + h) τ)) n_1 n_2)
   (ptr c (ntarray l_2 h_2 τ))
   (where l_2 ,(- (term l) (term n_2)))
   (where h_2 ,(- (+ (term x) (term h)) (term n_2)))
   (side-condition (not (= 0 (term n_1))))]

  [(⊢binop-type (name τ (ptr u (array le he _))) n_1 n_2)   τ]
  [(⊢binop-type (name τ (ptr u (ntarray le he _))) n_1 n_2) τ]
  [(⊢binop-type _ _ _) #f])

(define-metafunction CoreChkC+
  ⊢heap-defined? : H n vω -> #t or #f
  [(⊢heap-defined? H n (array i_0 _ _))
   ,(< 0 (+ (term n) (term i_0)) (add1 (length (term H))))]
  [(⊢heap-defined? H n (ntarray i_0 _ _))
   ,(< 0 (+ (term n) (term i_0)) (add1 (length (term H))))]
  [(⊢heap-defined? H n vω)
   ,(< 0 (term n) (add1 (length (term H))))])


(define-metafunction CoreChkC+
  ⊢update-heap-by-mode : H H m -> H
  [(⊢update-heap-by-mode H H c) (H ,(list-ref (term H) 1))]
  [(⊢update-heap-by-mode H H t) (,(list-ref (term H) 0) H)]
  [(⊢update-heap-by-mode H H u) (,(list-ref (term H) 0) H)])

(define-metafunction CoreChkC+
  ⊢update-eheap-by-mode : eH eH m -> eH
  [(⊢update-eheap-by-mode eH eH c) (eH ,(list-ref (term eH) 1))]
  [(⊢update-eheap-by-mode eH eH t) (,(list-ref (term eH) 0) eH)]
  [(⊢update-eheap-by-mode eH eH u) (,(list-ref (term eH) 0) eH)])

;(define-metafunction CoreChkC+
;  ⊢heap-by-mode : H m -> H
;  [(⊢heap-by-mode H c) ,(list-ref (term H) 0)]
;  [(⊢heap-by-mode H t) ,(list-ref (term H) 1)]
;  [(⊢heap-by-mode H u) ,(list-ref (term H) 1)])

(define-metafunction CoreChkC+
  ⊢eheap-by-mode : eH m -> eH
  [(⊢eheap-by-mode eH c) ,(list-ref (term eH) 0)]
  [(⊢eheap-by-mode eH t) ,(list-ref (term eH) 1)]
  [(⊢eheap-by-mode eH u) ,(list-ref (term eH) 1)])

(define-metafunction CoreChkC+
  ⊢fheap-by-mode : m -> F
  [(⊢fheap-by-mode c) ,(list-ref (*Fs*) 0)]
  [(⊢fheap-by-mode t) ,(list-ref (*Fs*) 1)]
  [(⊢fheap-by-mode u) ,(list-ref (*Fs*) 1)])

(define-metafunction CoreChkC+
  ⊢efheap-by-mode : m -> F
  [(⊢efheap-by-mode c) ,(list-ref (*eFs*) 0)]
  [(⊢efheap-by-mode t) ,(list-ref (*eFs*) 1)]
  [(⊢efheap-by-mode u) ,(list-ref (*eFs*) 1)])


(define-metafunction CoreChkC+
  ⊢heap-lookup : H K n -> (n : τ) or #f
  [(⊢heap-lookup (_ ... (n : (ptr K ω)) _ ...) K n) (n : (ptr K ω))] ;; case 1
  [(⊢heap-lookup _ K n) #f] ;; case 2
  )
;; Old Code
;;   ,(and (<= (term n) (length (term H)))
;;         (positive? (term n))
 ;;        (list-ref (term H) (sub1 (term n))))

;(define-metafunction CoreChkC+
;  ⊢fun-lookup : F n -> (defun e ((x : τ) ... e) : τ) or #f
;  [(⊢fun-lookup ((defun (n : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) _ ...) n)
;          (defun (n : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 )]
;  [(⊢fun-lookup (_ (defun (n_′ : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) ...) n)
;          (⊢fun-lookup ((defun (n_′ : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) ...) n)]
;  )
(define-metafunction CoreChkC+
  ⊢fun-lookup : F n -> (defun ((x : τ) ... e) : τ) or #f
  [(⊢fun-lookup F n)
   ,(and (<= (term n) (length (term F)))
         (positive? (term n))
         (list-ref (term F) (sub1 (term n))))])


(define-metafunction CoreChkC+
  ⊢efun-lookup : eF n -> (defun x ... ee) or #f
  [(⊢efun-lookup eF n)
   ,(and (<= (term n) (length (term eF)))
         (positive? (term n))
         (list-ref (term eF) (sub1 (term n))))])

(define-metafunction CoreChkC+
  ⊢eheap-lookup : eH n -> n or #f
  [(⊢eheap-lookup eH i)
   ,(and (<= (term i) (length (term eH)))
         (positive? (term i))
         (list-ref (term eH) (sub1 (term i))))])

(define-metafunction CoreChkC+
  ⊢heap-update : H n n -> H or #f
  [(⊢heap-update H n n_1)
   ,(list-set (term H) (sub1 (term n)) (term (n_1 : vτ_1)))
   (where n_H ,(length (term H)))
   (side-condition (>= (term n_H) (term n)))
   (side-condition (>= (term n) 1))
   (where (_ : vτ_1) (⊢heap-lookup H n))
   or
   #f])

(define-metafunction CoreChkC+
  ⊢eheap-update : eH m n n -> eH
  [(⊢eheap-update (eH_1 eH_2) c n n_1)
   (,(list-set (term eH_1) (sub1 (term n)) (term n_1)) eH_2)]
  [(⊢eheap-update (eH_1 eH_2) _ n n_1)
   (eH_1 ,(list-set (term eH_2) (sub1 (term n)) (term n_1)))])

(define-metafunction CoreChkC+
  ⊢heap-from : H n vω -> H
  [(⊢heap-from H n (ntarray l _ _)) ,(drop (term H) (+ (term l) (sub1 (term n))))]
  [(⊢heap-from H n (array l _ _)) ,(drop (term H) (+ (term l) (sub1 (term n))))]
  [(⊢heap-from H n _) ,(drop (term H) (sub1 (term n)))])

(define-metafunction CoreChkC+
  ⊢struct-lookup : D T -> fs
  [(⊢struct-lookup ((T fs) _ ...) T) fs]
  [(⊢struct-lookup (_ (T_′ fs) ...) T)
   (⊢struct-lookup ((T_′ fs) ...) T)])

(define-metafunction CoreChkC+
  ⊢deref-ok? : τ -> #t or #f
  [(⊢deref-ok? int) #t]
  [(⊢deref-ok? (ptr u ω)) #t]
  [(⊢deref-ok? (ptr c τ)) #t]
  [(⊢deref-ok? (ptr c (struct T))) #t]
  [(⊢deref-ok? (ptr c (fun _ _ _))) #t]
  [(⊢deref-ok? (ptr c (array l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢deref-ok? (ptr c (ntarray l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (<= 0 (term h))))]
  [(⊢deref-ok? _) #f])

(define-metafunction CoreChkC+
  ⊢assign-ok? : τ -> #t or #f
  [(⊢assign-ok? int) #t]
  [(⊢assign-ok? (ptr u ω)) #t]
  [(⊢assign-ok? (ptr c τ)) #t]
  [(⊢assign-ok? (ptr c (struct T))) #t]
  [(⊢assign-ok? (ptr c (fun _ _ _))) #t]
  [(⊢assign-ok? (ptr c (array l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢assign-ok? (ptr c (ntarray l h τ)))
   #t
   (side-condition (and (<= (term l) 0) (< 0 (term h))))]
  [(⊢assign-ok? _) #f])

(define-metafunction CoreChkC+
  ⊢bound-le? : le le -> #t or #f
  [(⊢bound-le? l_1 l_2) #t
   (side-condition (<= (term l_1) (term l_2)))]
  [(⊢bound-le? (x + l_1) (x + l_2)) #t
   (side-condition (<= (term l_1) (term l_2)))]
  [(⊢bound-le? _ _) #f])


(define-metafunction CoreChkC+
  ⊢types : D ω -> (τ ...)
  [(⊢types D τ) (τ)]
  [(⊢types D (fun _ τ _)) (τ)]
  [(⊢types D (array l h τ))
   ,(make-list (term n) (term τ))
   (where n ,(- (term h) (term l)))
   or
   ()]
  [(⊢types D (struct T))
   (τ ...)
   (where ((τ f) ...) (⊢struct-lookup D T))]
  ;; used when malloc'ing we do one more then the length
  [(⊢types D (ntarray l h τ))
   ,(make-list (term n) (term τ))
   (where n ,( + 1 (- (term h) (term l))))
   or
   ()])

;; fixes a minor bug in paper: should be τ_0 f_0; ...; τ_k f_k, 0 <= i <= k,
;; i.e. 0-based counting, not 1-based
(define-metafunction CoreChkC+
  ⊢& : τ f n -> (n : τ) or #f
  [(⊢& (ptr m (struct T)) f_i n)
   (n_i : τ_i′)
   (where ((τ_0 f_0) ... (τ_i f_i) _ ...) (⊢struct-lookup ,(*D*) T))
   (where n_i ,(+ (term n) (length (term ((τ_0 f_0) ...)))))
   (where τ_i′ (ptr m τ_i))
   (side-condition (or (eq? (term m) 'u) (not (= 0 (term n)))))]
  [(⊢& _ _ _) #f])

(define-metafunction CoreChkC+
  ⊢check-mode : m m -> #t or #f
  [(⊢check-mode u _) #t]
  [(⊢check-mode m m) #t]
  [(⊢check-mode _ _) #f])

;(define-metafunction CoreChkC+ ;;use as reference
;  ⊢fun-lookup : F n -> (defun e ((x : τ) ... e) : τ) or #f
;  [(⊢fun-lookup ((defun (n : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) _ ...) n)
;          (defun (n : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 )]
;  [(⊢fun-lookup (_ (defun (n_′ : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) ...) n)
;          (⊢fun-lookup ((defun (n_′ : τ_2) ((x_1 : τ_1) ... e_1) : τ_3 ) ...) n)]
;  )

(define-metafunction CoreChkC+
  ⊢check-heap-by-mode : m H n -> #t or #f
  [(⊢check-heap-by-mode c _ _) #t]
  [(⊢check-heap-by-mode u _ _) #t]
  [(⊢check-heap-by-mode t H n) (if (not (⊢heap-lookup H n)) #t #f)])

;; need to include the extra cases for type-level redex
(define-metafunction CoreChkC+
  ⊢mode : E -> m
  [(⊢mode hole) c]
  [(⊢mode (unchecked E)) u]
  [(⊢mode (let x = E in e)) (⊢mode E)]
  [(⊢mode (let x = (n : vτ) in E)) (⊢mode E)]
  [(⊢mode (E + e))          (⊢mode E)]
  [(⊢mode ((n : vτ) + E))    (⊢mode E)]
  [(⊢mode (& E → f))        (⊢mode E)]
  [(⊢mode (cast τ E))       (⊢mode E)]
  [(⊢mode (dyn-bound-cast τ E))       (⊢mode E)]
  [(⊢mode (* E))            (⊢mode E)]
  [(⊢mode (* E = e))        (⊢mode E)]
  [(⊢mode (* (n : τ) = E))  (⊢mode E)]
  [(⊢mode (x = E))          (⊢mode E)]
  [(⊢mode (if E e_1 e_2))   (⊢mode E)]
  ;;NEW
  [(⊢mode (call (n_0 : vτ) (n_1 : vτ2) ... E e ...))
   (⊢mode E)]
  [(⊢mode (strlen E))
   (⊢mode E)])

(define-metafunction CoreChkC+
  ⊢not-in : (x ...) x -> #t or #f
  [(⊢not-in (_ ... x _ ...) x) #f]
  [(⊢not-in _ _) #t])

;; fixed to handle all types
(define-metafunction CoreChkC+
  ⊢nt-incr : (ptr c (ntarray le he τ)) -> (ptr c (ntarray le he τ))
  ;; does it make sense to use le?
  [(⊢nt-incr (ptr c (ntarray le 0 τ))) (ptr c (ntarray le 1 τ))]
  [(⊢nt-incr τ) τ])


(define-metafunction CoreChkC+
  ⊢is-literal? : e -> #t or #f
  [(⊢is-literal? (n : _)) #t]
  [(⊢is-literal? _) #f])

(define-metafunction CoreChkC+
  ⊢bounds-sub : ω n -> ω or #f
  [(⊢bounds-sub (ntarray le he τ) n)
   (ntarray (⊢bound-sub le n) (⊢bound-sub he n) τ)]
  [(⊢bounds-sub (array le he τ) n)
   (array (⊢bound-sub le n) (⊢bound-sub he n) τ)]
  [(⊢bounds-sub _ n) #f])

(define-metafunction CoreChkC+
  ⊢bound-sub : le n -> le
  [(⊢bound-sub l n) ,(- (term l) (term n))]
  [(⊢bound-sub (x + l) n) (x + ,(- (term l) (term n)))])

(define-metafunction CoreChkC+
  ⊢is-array-or-nt-array? : ω -> #t or #f
  [(⊢is-array-or-nt-array? (ptr m (ntarray le he τ)))
   #t]
  [(⊢is-array-or-nt-array? (ptr m (array le he τ)))
   #t]
  [(⊢is-array-or-nt-array? _)
   #f])

(define-metafunction CoreChkC+
  ⊢extend-ρ′ : ((x : τ) ...) ρ -> (cE ρ)
  [(⊢extend-ρ′ () ρ) (hole ρ)]
  [(⊢extend-ρ′ ((x : τ) (x_0 : τ_0) ...) ρ)
   ((in-hole cE_1 cE_0) ρ_1)
   (where (cE_0 ρ_0) (⊢extend-ρ′ ((x_0 : τ_0) ...) ρ))
   (where (cE_1 ρ_1) (⊢extend-ρ x τ ρ_0))])

(define-metafunction CoreChkC+
  ⊢extend-ρ : x τ ρ -> (cE ρ)
  [(⊢extend-ρ x (ptr m (ntarray le he τ)) ((x_0 (x_lo0 x_hi0)) ...))
   ((let x_lo = le in
        (let x_hi = he in
             hole))
    ((x (x_lo x_hi)) (x_0 (x_lo0 x_hi0)) ...))
   (where (x_lo x_hi) ,(variables-not-in (term (x le he τ (x_0 (x_lo0 x_hi0)) ...)) '(x_lo x_hi)))]
  [(⊢extend-ρ x _ ρ)
   (hole ρ)]
  )



(define-metafunction CoreChkC+
  ⊢extend-Γ : (x = maybe-e : τ) Γ -> Γ
  [(⊢extend-Γ (x_0 = maybe-e_0 : τ_0) ((x_1 = maybe-e_1 : τ_1) ...))
   ((x_0 = maybe-e_0 : τ_0) (x_1 = maybe-e_1 : τ_1) ...)])

(define-metafunction CoreChkC+
  ⊢checked-strlen-var? : Γ e -> #t or #f
  [(⊢checked-strlen-var? Γ (strlen x))
   #t
   (where (_ (ptr c _)) (⊢ty-env-lookup Γ x))]
  [(⊢checked-strlen-var? _ _) #f])

(define-metafunction CoreChkC+
  ⊢nt-ptr? : τ -> #t or #f
  [(⊢nt-ptr? (ptr m (ntarray le he τ))) #t]
  [(⊢nt-ptr? _) #f])

(define-metafunction CoreChkC+
  ⊢non-nt-deref-or-strlen? : τ e -> #t or #f
  [(⊢non-nt-deref-or-strlen? (ptr u _) _) #t]
  [(⊢non-nt-deref-or-strlen? (ptr m (ntarray le he τ)) (in-hole E (* x))) #f]
  [(⊢non-nt-deref-or-strlen? (ptr m (ntarray le he τ))
  ;; only match strlen x instead of let ... = strlen x because we are
  ;; dealing with operational semantics
                             (in-hole E (strlen x))) #f]
  [(⊢non-nt-deref-or-strlen? _ _) #t])

(define-metafunction CoreChkC+
  ⊢strlen : n K H -> n or #f
  [(⊢strlen n K H)
   0
   (where (0 : _) (⊢heap-lookup H K n))]
  [(⊢strlen n K H)
   ,(add1 (term (⊢strlen ,(add1 (term n)) K H)))
   (where (n_0 : _) (⊢heap-lookup H K n))
   (side-condition (not (zero? (term n_0))))
   or
   #f])

(define-metafunction CoreChkC+
  ⊢estrlen : n eH -> n or #f
  [(⊢estrlen n eH)
   0
   (where 0 (⊢eheap-lookup eH n))]
  [(⊢estrlen n eH)
   ,(let ([r (term (⊢estrlen ,(add1 (term n)) eH))])
      (and r (add1 r)))
   (where n_0 (⊢eheap-lookup eH n))
   (side-condition (not (zero? (term n_0))))
   or
   #f])

(define-metafunction CoreChkC+
  ⊢malloc-type-wf : ω -> #t or #f
  [(⊢malloc-type-wf int) #t]
  [(⊢malloc-type-wf (ptr _ ω)) (⊢malloc-type-wf ω)]
  [(⊢malloc-type-wf (struct T)) #t]
  [(⊢malloc-type-wf (array 0 he τ)) (⊢malloc-type-wf τ)]
  [(⊢malloc-type-wf (ntarray 0 he τ)) (⊢malloc-type-wf τ)]
  [(⊢malloc-type-wf _) #f])

(define-metafunction CoreChkC+
  ⊢build-call-stack : e (x (n : vτ)) ...  -> e
  [(⊢build-call-stack e)
   e]
  [(⊢build-call-stack e (x_0 (n_0 : vτ_0)) (x_1 (n_1 : vτ_1)) ...)
   (let x_0 = (n_0 : vτ_0) in (⊢build-call-stack e (x_1 (n_1 : vτ_1)) ...))])

(define-metafunction CoreChkC+
  ⊢ebuild-call-stack : ee (x i) ...  -> ee
  [(⊢ebuild-call-stack ee)
   ee]
  [(⊢ebuild-call-stack ee (x_0 i_0) (x_1 i_1) ...)
   (let x_0 = i_0 in (⊢ebuild-call-stack ee (x_1 i_1) ...))])

(define-metafunction CoreChkC+
  ⊢sizeof : ω -> ee or #f
  [(⊢sizeof τ) 1]
  [(⊢sizeof (struct T)) ,(length (term (⊢struct-lookup ,(*D*) T)))]
  [(⊢sizeof (array 0 he _)) he]
  [(⊢sizeof (ntarray 0 (x + i) _)) (x + ,(+ 1 (term i)))]
  [(⊢sizeof (ntarray 0 i _)) ,(+ 1 (term i))]
  [(⊢sizeof _) ,(raise 'impossible)])

(define-metafunction CoreChkC+
  ⊢base? : n τ -> #t or #f
  [(⊢base? n int) #t]
  [(⊢base? n (ptr u ω)) #t]
  [(⊢base? 0 τ) #t]
  [(⊢base? n (ptr c (array 0 0 τ_′))) #t]
  [(⊢base? n (ptr c (ntarray 0 0 τ_′))) #t]
  [(⊢base? _ _) #f])

(define-metafunction CoreChkC+
  ⊢deref-type-dyn : D τ -> τ
  [(⊢deref-type-dyn _ int) int]
  [(⊢deref-type-dyn _ (ptr m τ)) τ]
  [(⊢deref-type-dyn _ (ptr m (ntarray _ _ τ))) τ]
  [(⊢deref-type-dyn _ (ptr m (array _ _ τ))) τ]
  [(⊢deref-type-dyn _ (ptr m (fun _ τ _))) τ]
  [(⊢deref-type-dyn D (ptr m (struct T)))
   τ_1
   (where ((τ_1 _) _ ...) (⊢struct-lookup D T))])

(define-metafunction CoreChkC+
  ⊢deref-type : ω -> τ
  [(⊢deref-type τ) τ]
  [(⊢deref-type (array le he τ)) τ]
  [(⊢deref-type (ntarray le he τ)) τ])



(module+ test
  (test--> (---> 'c)
             (term (() (let x = (1 : int) in x)))
             (term (() (let x = (1 : int) in (1 : int)))))
  (test--> (---> 'c)
             (term (() (let x = (1 : int) in (1 : int))))
             (term (() (1 : int))))
  (test-->> (---> 'c)
             (term (() (let x = (1 : int) in x)))
             (term (() (1 : int))))
    ;; shadowing. explicitly spelling out the steps to prevent non-deterministic semantics
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in (x + (let x = (4 : int) in x)))))
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in x))))))
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in x)))))
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in (4 : int)))))))
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in ((1 : int) + (let x = (4 : int) in (4 : int))))))
           (term (() (let x = (1 : int) in ((1 : int) + (4 : int))))))
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in ((1 : int) + (4 : int)))))
           (term (() (let x = (1 : int) in (5 : int)))))
  (test--> (---> 'c)
           (term (() (let x = (1 : int) in (5 : int))))
           (term (() (5 : int))))
  (test-->> (---> 'c)
             (term (() (let x = (1 : int) in
                            (let y = (2 : int) in (x + y)))))
             (term (() (3 : int))))

  (test-->> (---> 'c)
             (term (() (let x = (1 : int) in
                            (let y = (2 : (ptr c (ntarray 0 0 int))) in (x + y)))))
             (term (() (3 : int))))

;  ;; strlen non-NT case
;  (test-->> (---> 'c)
;            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
;                   (strlen (2 : (ptr c (ntarray 0 0 int))))))
;            (term (((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))
;                   (3 : int))))

;  ;;tainted strlen case
;    (test-->> (---> 'c)
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ())
;                   (strlen (2 : (ptr t (ntarray 0 0 int))))))
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ())
;                   Null)))
;
;  (test-->> (---> 'c)
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   (let x = (2 : (ptr c (ntarray 0 0 int))) in (strlen (x + (1 : int))))))
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int))) Bounds)))
;
;;; E-VarNTstr
;  (test--> (---> 'c)
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   (let x = (2 : (ptr c (ntarray 0 0 int))) in (strlen x))))
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   (let x = (2 : (ptr c (ntarray 0 3 int))) in (3 : int)))))
;
;  ;; make sure the bound always expands
;  (test--> (---> 'c)
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   (let x = (2 : (ptr c (ntarray 0 4 int))) in (strlen x))))
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   (let x = (2 : (ptr c (ntarray 0 4 int))) in (3 : int)))))
; 
;; This test doesn't work with 1 heap, will need to be restructured. The test is the issue, I need to fix the test.
  (test-->> (---> 'c)
            (term (((8 : int) (0 : int))
                   (let x = (1 : int) in
                        (let y = (2 : (ptr c (ntarray 0 0 int))) in (* y)))))
            (term (((8 : int) (0 : int)) (0 : int))))

;   (test-->> (---> 'c)
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   (strlen (0 : (ptr c (ntarray 0 0 int))))))
;            (term ((((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)) ((1 : int) (1 : int) (1 : int) (1 : int) (0 : int)))
;                   Null)))
;
;
;
;  ;; E-VarTy
;  (test--> (---> 'c)
;           (term ((() ()) (let x = (1 : int) in
;                          (malloc c (array (x + 0) (x + 0) int)))))
;           (term ((() ()) (let x = (1 : int) in
;                          (malloc c (array 1 (x + 0) int))))))
;
;
;  (test--> (---> 'c)
;           (term ((() ()) (malloc c (array 0 -7 int))))
;           (term ((() ()) (0 : (ptr c (array 0 -7 int))))))
;
;  (test--> (---> 'c)
;           (term ((() ()) (malloc c (array 0 0 int))))
;           (term ((() ()) (0 : (ptr c (array 0 0 int))))))
;
;  (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
;            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y)))))
;
;  (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
;            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y)))))
;
;  (test--> (---> 'c)
;           (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in y))))
;           (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array 1 0 int))) in (0 : (ptr c (array 1 0 int))))))))
;
;  (test-->> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in (let y = (0 : (ptr c (array (x + 0) 0 int))) in y))))
;            (term ((() ()) (0 : (ptr c (array 1 0 int))))))
;
;  ;; E-Malloc (cases where it gets stuck)
;  (test-->> (---> 'c)
;            (term ((() ()) (malloc c (array 2 3 int))))
;            (term ((() ()) (malloc c (array 2 3 int)))))
;
;  (test-->> (---> 'c)
;            (term ((() ()) (malloc c (array 0 3 int))))
;            (term ((((0 : int) (0 : int) (0 : int)) ()) (1 : (ptr c (array 0 3 int))))))
;
;  ;; E-Malloc (empty)
;  (test-->> (---> 'c)
;            (term ((() ()) (malloc c (array 0 -1 int))))
;            (term ((() ()) (0 : (ptr c (array 0 -1 int))))))
;
;  (test-->> (---> 'c)
;            (term ((((1 : int)) ()) (malloc c (array 0 0 int))))
;            (term ((((1 : int)) ()) (0 : (ptr c (array 0 0 int))))))
;
;
;  (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array (x + 0) 0 int))) in
;                                (let z = (cast int y) in (malloc c (array 0 (z + 0) int)))))))
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (cast int y) in (malloc c (array 0 (z + 0) int))))))))
;
;   (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (cast int y) in (malloc c (array 0 (z + 0) int)))))))
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (cast int (4 : (ptr c (array 1 0 int)))) in (malloc c (array 0 (z + 0) int))))))))
;
;  (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (cast int (4 : (ptr c (array 1 0 int)))) in (malloc c (array 0 (z + 0) int)))))))
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (4 : int) in (malloc c (array 0 (z + 0) int))))))))
;
;  (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (4 : int) in (malloc c (array 0 (z + 0) int)))))))
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (4 : int) in (malloc c (array 0 4 int))))))))
;
;  (test-->> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in
;                           (let y = (4 : (ptr c (array 1 0 int))) in
;                                (let z = (4 : int) in (malloc c (array 0 4 int)))))))
;            (term ((((0 : int) (0 : int) (0 : int) (0 : int)) ()) (1 : (ptr c (array 0 4 int))))))
;
;  (test--> (---> 'c)
;            (term ((() ()) (let x = (1 : int) in
;                           (* ((malloc c (array 0 (x + 0) int)) + x)))))
;            (term ((() ()) (let x = (1 : int) in
;                           (* ((malloc c (array 0 1 int)) + x))))))
;
;  (test--> (---> 'c)
;           (term ((() ()) (let x = (1 : int) in
;                          (* ((malloc c (array 0 1 int)) + x)))))
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* ((1 : (ptr c (array 0 1 int))) + x))))))
;
;    (test--> (---> 'c)
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* ((1 : (ptr c (array 0 1 int))) + x)))))
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int)))))))
;
;  (test--> (---> 'c)
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* ((1 : (ptr c (array 0 1 int))) + x)))))
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int)))))))
;
;  (test--> (---> 'c)
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* ((1 : (ptr c (array 0 1 int))) + (1 : int))))))
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* (2 : (ptr c (array -1 0 int))))))))
;
;  (test--> (---> 'c)
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* (2 : (ptr c (array -1 0 int)))))))
;           (term ((((0 : int)) ()) Bounds)))
;
;  (test--> (---> 'c)
;           (term ((((0 : int)) ()) (let x = (1 : int) in
;                                   (* (2 : (ptr t (array -1 0 int)))))))
;           (term ((((0 : int)) ()) Null)))

  )

;(module+ test
;  (parameterize ((*Fs* (term (((defun  ((x : int) (x + (1 : int))) : int)      ; (fun (x ...) τ (τ ...)))
;                             (defun ((y : int) (y + (2 : int))) : int)      ; (+2) at position 1
;                             (defun ((p : int) (q : int) (p + q)) : int)
;                             )
;                             ((defun ((x : int) (x + (1 : int))) : int)      ; (+1) at position 0
;                             (defun ((y : int) (y + (2 : int))) : int)      ; (+2) at position 1
;                             (defun ((p : int) (q : int) (p + q)) : int)
;                             )))))        ; (+)  at position 2
;    (test--> (---> 'c)
;           (term ((() ()) (call (1 : (ptr c (fun () int (int)))) (4 : int))))
;           (term ((() ()) (let y = (4 : int) in (y + (1 : int))))))
;    (test--> (---> 'c)
;           (term ((() ()) (call (3 : (ptr c (fun () int (int int)))) (4 : int) (5 : int))))
;           (term ((() ()) (let p = (4 : int) in (let q = (5 : int) in (p + q))))))
;    )
;
;   (parameterize ((*Fs* (term (((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
;                               (if (* x)
;                                   ((1 : int) +
;                                          (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (cast (ptr c (ntarray 0 0 int)) (x + (1 : int)))))
;                                       (0 : int))) : int))
;                               ((defun ((x : (ptr t (ntarray 0 0 int)))    ;strlen
;                               (if (* x)
;                                   ((1 : int) +
;                                          (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (cast (ptr t (ntarray 0 0 int)) (x + (1 : int)))))
;                                       (0 : int))) : int))))))
;
;    (test-->> (---> 'c)
;           (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;                  (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int)))))) (1 : (ptr c (ntarray 0 0 int))))))
;           (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;                  (3 : int))))
;     )
;
; (parameterize ((*Fs* (term (((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
;                               (if (* x)
;                                   ((1 : int) +
;                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                       (0 : int))) : int))
;                            ((defun ((x : (ptr t (ntarray 0 0 int)))    ;strlen
;                               (if (* x)
;                                   ((1 : int) +
;                                              (call (1 : (ptr t (fun () int ((ptr t (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                       (0 : int))) : int))))))
;    (test-->>
;     (---> 'c)
;
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int)))))) (1 : (ptr c (ntarray 0 0 int))))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (3 : int)))))
;
;   ;; arity
;  (parameterize ((*Fs* (term (((defun ((x : int)
;                               (x + (1 : int))) : int))
;                              ((defun ((x : int)
;                               (x + (1 : int))) : int))))))
;    (test-->>
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (call (1 : (ptr c (fun () int (int)))) (2 : int) (2 : int) )))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (call (1 : (ptr c (fun () int (int)))) (2 : int) (2 : int) ))))
;    (test-->>
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (call (1 : (ptr c (fun () int (int)))) (2 : int) )))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (3 : int)))))
;
;  (parameterize ((*Fs* (term (((defun ((x : (ptr c (ntarray 0 0 int)))    ;strlen
;                               (if (* x)
;                                   ((1 : int) +
;                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                       (0 : int))) : int))
;                              ((defun ((x : (ptr t (ntarray 0 0 int)))    ;strlen
;                               (if (* x)
;                                   ((1 : int) +
;                                              (call  (1 : (ptr t (fun () int ((ptr t (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                       (0 : int))) : int))))))
;    (test-->
;     (---> 'c)
;
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (call  (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int)))))) (1 : (ptr c (ntarray 0 0 int))))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 0 int))) in
;                 (if (* x)
;                     ((1 : int) +
;                                (call  (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                            (x + (1 : int))))
;                     (0 : int))))))
;
;    (test-->
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 0 int))) in
;                 (if (* x)
;                     ((1 : int) +
;                                (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                            (x + (1 : int))))
;                     (0 : int)))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 (if (1 : int)
;                     ((1 : int) +
;                                (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                            (x + (1 : int))))
;                     (0 : int))))))
;
;    (test-->
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 (if (1 : int)
;                     ((1 : int) +
;                                (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                            (x + (1 : int))))
;                     (0 : int)))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                        (x + (1 : int))))))))
;
;    (test-->
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                        (x + (1 : int)))))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                        ((1 : (ptr c (ntarray 0 1 int))) + (1 : int))))))))
;
;    (test-->
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                        ((1 : (ptr c (ntarray 0 1 int))) + (1 : int)))))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                        (2 : (ptr c (ntarray -1 0 int)))))))))
;
;    (test-->
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                            (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                        (2 : (ptr c (ntarray -1 0 int))))))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                  (let x = (2 : (ptr c (ntarray -1 0 int))) in
;                       (if (* x)
;                                   ((1 : int) +
;                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                   (0 : int))))))))
;
;    (test-->
;     (---> 'c)
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                  (let x = (2 : (ptr c (ntarray -1 0 int))) in
;                       (if (* x)
;                                   ((1 : int) +
;                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                   (0 : int)))))))
;     (term ((((1 : int) (1 : int) (1 : int) (0 : int)) ())
;            (let x = (1 : (ptr c (ntarray 0 1 int))) in
;                 ((1 : int) +
;                  (let x = (2 : (ptr c (ntarray -1 1 int))) in
;                       (if (1 : int)
;                                   ((1 : int) +
;                                              (call (1 : (ptr c (fun () int ((ptr c (ntarray 0 0 int))))))
;                                          (x + (1 : int))))
;                                       (0 : int))))))))
;    )
;)

;;;;;;;;;;;;;;;;;;;;;;;;;;Test functions

;(module+ test
;  (test-equal (term (⊢types () (ntarray 0 0 int))) (term (int)))
;  (test-equal (term (⊢types () (ntarray 0 1 int))) (term (int int)))
;
;  (test--> ~~>
;           (term ((((8 : int) (0 : int)) ())
;                  (let x = (1 : (ptr c (ntarray 0 0 int))) in (* x))))
;           (term ((((8 : int) (0 : int)) ())
;                  (let x = (1 : (ptr c (ntarray 0 1 int))) in (8 : int)))))
;
;  (test-->>∃ ~~>
;             (term ((((8 : int) (0 : int)) ())
;                    (let x = (1 : (ptr c (ntarray 0 0 int))) in (* x))))
;             (curry (default-equiv)
;                    (term ((((8 : int) (0 : int)) ())
;                           (let x = (1 : (ptr c (ntarray 0 1 int))) in (8 : int))))))
;
;  (test-->> (---> 'c)
;            (term ((((8 : int) (0 : int)) ())
;                   (let x = (1 : (ptr c (ntarray 0 0 int))) in
;                        (if (* x)
;                            (let y = (x + (1 : int)) in
;                                 (* y))
;                            (1 : int)))))
;            (term ((((8 : int) (0 : int)) ()) (0 : int))))
;  (test-->> (---> 'c)
;            (term ((((8 : int) (0 : int)) ())
;                   (if (5 : int) (2 : int) (3 : int))))
;            (term ((((8 : int) (0 : int)) ()) (2 : int)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
<<<<<<< Updated upstream
=======

;; Subtype

(define-judgment-form CoreChkC+
  #:contract (⊢subtype τ τ)
  #:mode (⊢subtype I I)

  [
   -------------- Sub-Nt
   (⊢subtype (ptr c (nt-array l h τ)) (ptr c (array l h τ)))]

  [
   ------------- Sub-Refl
   (⊢subtype τ τ)]

  [
   ------------- Sub-Ptr
   (⊢subtype (ptr c τ) (ptr c (array 0 1 τ)))]

   [
   ------------- Sub-Arr
   (⊢subtype (ptr c (array 0 1 τ)) (ptr c τ))]

  [
   (where #t (⊢bound-le? le le_1))
   (where #t (⊢bound-le? he_1 he))
   ------------- Sub-SubsumeNT
   (⊢subtype (ptr c (ntarray le he τ)) (ptr c (ntarray le_1 he_1 τ)))]

  [
   (where #t (⊢bound-le? le le_1))
   (where #t (⊢bound-le? he_1 he))
   ------------- Sub-Subsume
   (⊢subtype (ptr c (array le he τ)) (ptr c (array le_1 he_1 τ)))]

  ;; Again to match Coq developement, might remove
  ;; something wrong syntactically here
  [(where ((τ_f f) _ ...) (⊢struct-lookup ,(*D*) T))
   (⊢subtype τ_f τ)
   ------------- Sub-struct-array-field
   (⊢subtype (ptr c (struct T)) (ptr c τ))])

;;tests for subtyping
(module+ test
  (parameterize ((*D* (term ((foo ((int x) (int y))))))))
;; tests for subtyping
  (test-judgment-holds
   (⊢subtype int int))
  (test-judgment-holds
   (⊢subtype (ptr c (ntarray 0 6 int)) (ptr c (ntarray 0 6 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (ntarray 0 6 int)) (ptr c (ntarray 0 2 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array 0 6 int)) (ptr c (array 0 2 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array 0 6 int)) (ptr c (array 0 0 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array -1 6 int)) (ptr c (array 0 0 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (ntarray -1 6 int)) (ptr c (ntarray 0 0 int))))
  (test-judgment-holds
   (⊢subtype (ptr c int) (ptr c (array 0 1 int))))
  (test-judgment-holds
   (⊢subtype (ptr c (array 0 1 int)) (ptr c int)))
  (test-judgment-holds
   (⊢subtype (ptr c (struct foo)) (ptr c int))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
>>>>>>> Stashed changes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operational Semantics

(define --->^
  (reduction-relation
   CoreChkC+ #:domain (eH ee) #:codomain (eH er)
   (--> (eH (in-hole eE (i_0 + i_1)))
        (eH (in-hole eE ,(+ (term i_0) (term i_1))))
        eE-Add)

   (--> (eH (in-hole eE (i_0 <=? i_1)))
        (eH (in-hole eE ,(if (<= (term i_0) (term i_1)) 1 0)))
        eE-Leq)

   (--> (eH (in-hole eE (i_0 - i_1)))
        (eH (in-hole eE ,(- (term i_0) (term i_1))))
        eE-Subtract)

   ;; apparently negative values (a.k.a bounds) should never appear on the heap
   (--> (eH (in-hole eE (star-l n)))
        (eH (in-hole eE n_0))
        (where eH (⊢eheap-by-mode eH c))
        (where n_0 (⊢eheap-lookup eH n))
        eE-DerefLeft)

   (--> (eH (in-hole eE (star-r n)))
        (eH (in-hole eE n_0))
        (where eH (⊢eheap-by-mode eH u))
        (where n_0 (⊢eheap-lookup eH n))
        eE-DerefRight)

   ;; don't forget the underscore!!!!! Is the eE stuff just for coreC?
   (--> (eH (in-hole eE (star-l n = n_0)))
        (eH_′ (in-hole eE n_0))
        (where eH_′ (⊢eheap-update eH c n n_0))
        eE-AssignLeft)

   (--> (eH (in-hole eE (star-r n = n_0)))
        (eH_′ (in-hole eE n_0))
        (where eH_′ (⊢eheap-update eH u n n_0))
        eE-AssignRight)

   (--> (eH (in-hole eE (let x = i_0 in
                                (in-hole eE_′ (x = i_1)))))
        (eH (in-hole eE (let x = i_1 in
                                (in-hole eE_′ i_1))))
        eE-Set)

   ;; Merge the mallocs
   ;; add an if condition to nt-array malloc
   ;; These are for corec
   (--> (eH (in-hole eE (malloc-l n_1)))
        (eH_′ (in-hole eE n_2))
        (side-condition (positive? (term n_1)))
        (where eH (⊢eheap-by-mode eH c))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where eH_′ (⊢update-eheap-by-mode eH eH_′ c))
        (where n_2 ,(add1 (length (term eH))))
        eE-MallocLeft)

   (--> (eH (in-hole eE (malloc-r n_1)))
        (eH_′ (in-hole eE n_2))
        (side-condition (positive? (term n_1)))
        (where eH (⊢eheap-by-mode eH u))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where eH_′ (⊢update-eheap-by-mode eH eH_′ u))
        (where n_2 ,(add1 (length (term eH))))
        eE-MallocRight)

<<<<<<< Updated upstream
=======
   ;; is this good?
   (--> (eH (in-hole eE (malloc-lr n_1)))
        (eH_′ (in-hole eE n_2))
        (side-condition (positive? (term n_1)))
        (where eH (⊢eheap-by-mode eH u))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where eH_′ (⊢update-eheap-by-mode eH eH_′ u))
        (where n_2 ,(add1 (length (term eH))))
        eE-Malloc)

>>>>>>> Stashed changes
   (--> (eH (in-hole eE (malloc-l i_1)))
        (eH (in-hole eE 0))
        (side-condition (not (positive? (term i_1))))
        eE-MallocLeftZero)

   (--> (eH (in-hole eE (malloc-r i_1)))
        (eH (in-hole eE 0))
        (side-condition (not (positive? (term i_1))))
        eE-MallocRightZero)

<<<<<<< Updated upstream
=======
   ;; is this good?
   (--> (eH (in-hole eE (malloc-lr i_1))) ;; this line is the expression on the left hand side of the arrow
        (eH (in-hole eE 0)) ;; this is the expression on the right hand side of the arrow. Basically, evaluating the above, should give you this.
        (side-condition (not (positive? (term i_1))))
        eE-MallocZero)

>>>>>>> Stashed changes
   (--> (eH (in-hole eE (let x = i_0 in i_1)))
        (eH (in-hole eE i_1))
        eE-Let)

   (--> (eH (in-hole eE (let x = i_0 in (in-hole eE_′ x))))
        (eH (in-hole eE (let x = i_0 in (in-hole eE_′ i_0))))
        eE-Var)

   (--> (eH (in-hole eE (if i ee _)))
        (eH (in-hole eE ee))
        (side-condition (not (zero? (term i))))
        eE-IfT)

   (--> (eH (in-hole eE (if 0 _ ee)))
        (eH (in-hole eE ee))
        eE-IfF)

   (--> (eH (in-hole eE (strlen-l i)))
        (eH (in-hole eE i_0))
        (where eH (⊢eheap-by-mode eH c))
        (where i_0 (⊢estrlen i eH))
        eE-StrLeft)

   (--> (eH (in-hole eE (strlen-r i)))
        (eH (in-hole eE i_0))
        (where eH (⊢eheap-by-mode eH u))
        (where i_0 (⊢estrlen i eH))
        eE-StrRight)

   (--> (eH (in-hole eE (call-l i i_1 ..._1)))
        (eH (in-hole eE (⊢ebuild-call-stack ee (x i_1) ...)))
        (where (defun x ..._1 ee) (⊢efun-lookup ,(*eFs*) i c))
        eE-FunLeft)

   (--> (eH (in-hole eE (call-r i i_1 ..._1)))
        (eH (in-hole eE (⊢ebuild-call-stack ee (x i_1) ...)))
        (where (defun x ..._1 ee) (⊢efun-lookup ,(*eFs*) i u))
        eE-FunRight)

   (--> (eH (in-hole eE (enull)))
        (eH Null)
        eX-Null)

   (--> (eH (in-hole eE (ebounds)))
        (eH Bounds)
        eX-Bounds)))

(define --->^CEK
  (reduction-relation
   CoreChkC+ 
   (--> (eH eΣ (i_0 + i_1) (eK ...))
        (eH eΣ ,(+ (term i_0) (term i_1)) (eK ...))
        eE-Add)

   (--> (eH eΣ (i_0 <=? i_1) (eK ...))
        (eH eΣ ,(if (<= (term i_0) (term i_1)) 1 0) (eK ...))
        eE-Leq)

   (--> (eH eΣ (i_0 - i_1) (eK ...))
        (eH eΣ ,(- (term i_0) (term i_1)) (eK ...))
        eE-Subtract)

   (--> (eH eΣ (star-l n) (eK ...))
        (eH eΣ n_0 (eK ...))
        (where eH (⊢eheap-by-mode eH c))
        (where n_0 (⊢eheap-lookup eH n))
        eE-DerefLeft)

   (--> (eH eΣ (star-r n) (eK ...))
        (eH eΣ n_0 (eK ...))
        (where eH (⊢eheap-by-mode eH u))
        (where n_0 (⊢eheap-lookup eH n))
        eE-DerefRight)

   (--> (eH eΣ (star-l n = n_0) (eK ...))
        (eH_′ eΣ n_0 (eK ...))
        (where eH (⊢eheap-by-mode eH c))
        (where eH_′ (⊢eheap-update eH c n n_0))
        eE-AssignLeft)

   (--> (eH eΣ (star-r n = n_0) (eK ...))
        (eH_′ eΣ n_0 (eK ...))
        (where eH (⊢eheap-by-mode eH u))
        (where eH_′ (⊢eheap-update eH u n n_0))
        eE-AssignRight)

   (--> (eH ((x_0 i_0) ... (x _) (x_2 i_2) ...) (x = i_1) (eK ...))
        (eH ((x_0 i_0) ... (x i_1) (x_2 i_2) ...) i_1 (eK ...))
        eE-Set)

   ;; merge these mallocs together
   (--> (eH eΣ (malloc-l n_1) (eK ...))
        (eH_′ eΣ n_2 (eK ...))
        (side-condition (positive? (term n_1)))
        (where eH (⊢eheap-by-mode eH c))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where eH_′ (⊢update-eheap-by-mode eH eH_′ c))
        (where n_2 ,(add1 (length (term eH))))
        eE-MallocLeft)

   (--> (eH eΣ (malloc-r n_1) (eK ...))
        (eH_′ eΣ n_2 (eK ...))
        (side-condition (positive? (term n_1)))
        (where eH (⊢eheap-by-mode eH u))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where eH_′ (⊢update-eheap-by-mode eH eH_′ u))
        (where n_2 ,(add1 (length (term eH))))
        eE-MallocRight)

<<<<<<< Updated upstream
=======
   ;; is this good?
   (--> (eH eΣ (malloc-lr n_1) (eK ...))
        (eH_′ eΣ n_2 (eK ...))
        (side-condition (positive? (term n_1)))
        (where eH (⊢eheap-by-mode eH u))
        (where eH_′ ,(append (term eH) (build-list (term n_1) (const 0))))
        (where eH_′ (⊢update-eheap-by-mode eH eH_′ u))
        (where n_2 ,(add1 (length (term eH))))
        eE-Malloc)
   
>>>>>>> Stashed changes
   (--> (eH eΣ (malloc-l i_1) (eK ...))
        (eH eΣ 0 (eK ...))
        (side-condition (not (positive? (term i_1))))
        eE-MallocLeftZero)

   (--> (eH eΣ (malloc-r i_1) (eK ...))
        (eH eΣ 0 (eK ...))
        (side-condition (not (positive? (term i_1))))
        eE-MallocRightZero)

<<<<<<< Updated upstream
=======
   ;; is this good?
      (--> (eH eΣ (malloc-lr i_1) (eK ...))
        (eH eΣ 0 (eK ...))
        (side-condition (not (positive? (term i_1))))
        eE-MallocZero)
>>>>>>> Stashed changes

   (--> (eH ((x i) ...) (let x_0 = i_0 in ee) (eK ...))
        (eH ((x_0 i_0) (x i) ...) ee (pop eK ...))
        eE-Let)

   (--> (eH (name eΣ (_ ... (x i) _ ...)) x (eK ...))
        (eH eΣ i (eK ...))
        eE-Var)

   (--> (eH eΣ (if i ee _) (eK ...))
        (eH eΣ ee (eK ...))
        (side-condition (not (zero? (term i))))
        eE-IfT)

   (--> (eH eΣ (if 0 _ ee) (eK ...))
        (eH eΣ ee (eK ...))
        eE-IfF)

   (--> (eH eΣ (strlen-l i) (eK ...))
        (eH eΣ i_0 (eK ...))
        (where eH (⊢eheap-by-mode eH c))
        (where i_0 (⊢estrlen i eH))
        eE-StrLeft)

   (--> (eH eΣ (strlen-r i) (eK ...))
        (eH eΣ i_0 (eK ...))
        (where eH (⊢eheap-by-mode eH u))
        (where i_0 (⊢estrlen i eH))
        eE-StrRight)

   (--> (eH eΣ (call-l i i_1 ..._1) (eK ...))
        (eH eΣ (⊢ebuild-call-stack ee (x i_1) ...) (eK ...))
        (where (defun x ..._1 ee) (⊢efun-lookup (⊢efheap-by-mode ,(*eFs*) c) i))
        eE-FunLeft)

   (--> (eH eΣ (call-r i i_1 ..._1) (eK ...))
        (eH eΣ (⊢ebuild-call-stack ee (x i_1) ...) (eK ...))
        (where (defun x ..._1 ee) (⊢efun-lookup (⊢efheap-by-mode ,(*eFs*) u) i))
        eE-FunRight)

   
   (--> (eH eΣ (enull) (eK ...))
        (eH () Null ())
        eX-Null)

   (--> (eH eΣ (ebounds) (eK ...))
        (eH () Bounds ())
        eX-Bounds)

   ;; eval
   (--> (eH eΣ (if eS ee_0 ee_1) (eK ...))
        (eH eΣ eS ((if [] ee_0 ee_1) eK ...))
        eE-If-Eval)

   (--> (eH eΣ i ((if [] ee_0 ee_1) eK ...))
        (eH eΣ (if i ee_0 ee_1) (eK ...))
        eE-If-Cont)

   (--> (eH eΣ i ((strlen-l []) eK ...))
        (eH eΣ (strlen-r i) (eK ...))
        eE-StrlenLeft-Cont)

   (--> (eH eΣ i ((strlen-r []) eK ...))
        (eH eΣ (strlen-r i) (eK ...))
        eE-StrlenRight-Cont)

   (--> (eH eΣ (strlen-l eS) (eK ...))
        (eH eΣ eS ((strlen-l []) eK ...))
        eE-StrlenLeft-Eval)

   (--> (eH eΣ (strlen-r eS) (eK ...))
        (eH eΣ eS ((strlen-r []) eK ...))
        eE-StrlenRight-Eval)

   ;; merge these mallocs together
   (--> (eH eΣ i ((malloc-l []) eK ...))
        (eH eΣ (malloc-l i) (eK ...))
        eE-MallocLeft-Cont)

   (--> (eH eΣ i ((malloc-r []) eK ...))
        (eH eΣ (malloc-r i) (eK ...))
        eE-MallocRight-Cont)

<<<<<<< Updated upstream
=======
   ;; is this good?
   (--> (eH eΣ i ((malloc-lr []) eK ...))
        (eH eΣ (malloc-lr i) (eK ...))
        eE-Malloc-Cont)

>>>>>>> Stashed changes
   (--> (eH eΣ (malloc-l eS) (eK ...))
        (eH eΣ eS ((malloc-l []) eK ...))
        eE-MallocLeft-Eval)

   (--> (eH eΣ (malloc-r eS) (eK ...))
        (eH eΣ eS ((malloc-r []) eK ...))
        eE-MallocRight-Eval)

<<<<<<< Updated upstream
=======
   ;; is this good?
   (--> (eH eΣ (malloc-lr eS) (eK ...))
        (eH eΣ eS ((malloc-lr []) eK ...))
        eE-Malloc-Eval)
   
>>>>>>> Stashed changes

   (--> (eH eΣ (let x = eS in ee) (eK ...))
        (eH eΣ eS ((let x = [] in ee) eK ...))
        eE-Let-Eval0)

   (--> (eH eΣ i ((let x = [] in ee) eK ...))
        (eH eΣ (let x = i in ee) (eK ...))
        eE-Let-Cont0)


   (--> (eH ((x i) (x_0 i_0) ...) i_1 (pop eK ...))
        (eH ((x_0 i_0) ...) i_1 (eK ...))
        eE-Pop-Cont)

   (--> (eH eΣ (call-l n_fun n_args ... eS ee_args ...) (eK ...))
        (eH eΣ eS ((call-l n_fun n_args ... [] ee_args ...) eK ...))
        eE-FunLeft-Eval)

   (--> (eH eΣ (call-r n_fun n_args ... eS ee_args ...) (eK ...))
        (eH eΣ eS ((call-r n_fun n_args ... [] ee_args ...) eK ...))
        eE-FunRight-Eval)

   (--> (eH eΣ n ((call-l n_fun n_args ... [] ee_args ...) eK ...))
        (eH eΣ (call-l n_fun n_args ... n ee_args ...) (eK ...))
        eE-FunLeft-Cont)

   (--> (eH eΣ n ((call-r n_fun n_args ... [] ee_args ...) eK ...))
        (eH eΣ (call-r n_fun n_args ... n ee_args ...) (eK ...))
        eE-FunRight-Cont)

   (--> (eH eΣ (eS <=? ee) (eK ...))
        (eH eΣ eS (([] <=? ee) eK ...))
        eE-Leq-Eval0)

   (--> (eH eΣ i (([] <=? ee) eK ...))
        (eH eΣ (i <=? ee) (eK ...))
        eE-Leq-Cont0)

   (--> (eH eΣ (i <=? eS) (eK ...))
        (eH eΣ eS ((i <=? []) eK ...))
        eE-Leq-Eval1)

   (--> (eH eΣ i_0 ((i <=? []) eK ...))
        (eH eΣ (i <=? i_0) (eK ...))
        eE-Leq-Cont1)

   (--> (eH eΣ (star-l eS = ee) (eK ...))
        (eH eΣ eS ((star-l [] = ee) eK ...))
        eE-AssignLeft-Eval0)

   (--> (eH eΣ (star-r eS = ee) (eK ...))
        (eH eΣ eS ((star-r [] = ee) eK ...))
        eE-AssignRight-Eval0)

   (--> (eH eΣ i ((star-l [] = ee) eK ...))
        (eH eΣ (star-l i = ee) (eK ...))
        eE-AssignLeft-Cont0)
   
   (--> (eH eΣ i ((star-r [] = ee) eK ...))
        (eH eΣ (star-r i = ee) (eK ...))
        eE-AssignRight-Cont0)

   (--> (eH eΣ (star-l i = eS) (eK ...))
        (eH eΣ eS ((star-l i = []) eK ...))
        eE-AssignLeft-Eval1)

   (--> (eH eΣ (star-r i = eS) (eK ...))
        (eH eΣ eS ((star-r i = []) eK ...))
        eE-AssignRight-Eval1)

   (--> (eH eΣ i_0 ((star-l i = []) eK ...))
        (eH eΣ (star-l i = i_0) (eK ...))
        eE-AssignLeft-Cont1)

   (--> (eH eΣ i_0 ((star-r i = []) eK ...))
        (eH eΣ (star-r i = i_0) (eK ...))
        eE-AssignRight-Cont1)
   
   (--> (eH eΣ (star-l eS) (eK ...))
        (eH eΣ eS ((star-l []) eK ...))
        eE-DerefLeft-Eval)

   (--> (eH eΣ (star-r eS) (eK ...))
        (eH eΣ eS ((star-r []) eK ...))
        eE-DerefRight-Eval)
   
   (--> (eH eΣ i ((star-l []) eK ...))
        (eH eΣ (star-l i) (eK ...))
        eE-DerefLeft-Cont)

   (--> (eH eΣ i ((star-r []) eK ...))
        (eH eΣ (star-r i) (eK ...))
        eE-DerefRight-Cont)
   
   (--> (eH eΣ (x = eS) (eK ...))
        (eH eΣ eS ((x = []) eK ...))
        eE-Set-Eval)

   (--> (eH eΣ i ((x = []) eK ...))
        (eH eΣ i (x = i) (eK ...))
        eE-Set-Cont)

   (--> (eH eΣ (eS + ee) (eK ...))
        (eH eΣ eS (([] + ee) eK ...))
        eE-Add-Eval0)

   (--> (eH eΣ i (([] + ee) eK ...))
        (eH eΣ (i + ee) (eK ...))
        eE-Add-Cont0)

   (--> (eH eΣ (i + eS) (eK ...))
        (eH eΣ eS ((i + []) eK ...))
        eE-Add-Eval1)

   (--> (eH eΣ i_0 ((i + []) eK ...))
        (eH eΣ (i + i_0) (eK ...))
        eE-Add-Cont1)

   (--> (eH eΣ (eS - ee) (eK ...))
        (eH eΣ eS (([] - ee) eK ...))
        eE-Subtract-Eval0)

   (--> (eH eΣ i (([] - ee) eK ...))
        (eH eΣ (i - ee) (eK ...))
        eE-Subtract-Cont0)

   (--> (eH eΣ (i - eS) (eK ...))
        (eH eΣ eS ((i - []) eK ...))
        eE-Subtract-Eval1)

   (--> (eH eΣ i_0 ((i - []) eK ...))
        (eHs eΣ (i - i_0) (eK ...))
        eE-Subtract-Cont)))



(print "tests pass")


;; CoreC copied from nt-array

;; Should I switch m to K? probably?
(define-judgment-form CoreChkC+
  #:contract (⊢Fwf>>> Γ σ ρ m F eF)
  #:mode     (⊢Fwf>>> I I I I I O)
  [------------- WF-FUN-NIL
   (⊢Fwf>>> Γ σ ρ m () ())]
  [(⊢Fwf>>> Γ σ ρ m ((defun ((x_0 : τ_0) ... e_0) : τ_res0) ...) ((defun x_1 ... ee_1) ...))
   (⊢fwf>>> Γ σ ρ m ((x : τ) ...) τ_res e ee)
   ------------- WF-FUN-CONS
   (⊢Fwf>>> Γ σ ρ m ((defun ((x : τ) ... e) : τ_res) (defun ((x_0 : τ_0) ... e_0) : τ_res0) ...)
            ((defun x ... ee) (defun x_1 ... ee_1) ...))])

(define-judgment-form CoreChkC+
  #:contract (⊢fwf>>> Γ σ ρ m ((x : τ) ...) τ e ee)
  #:mode     (⊢fwf>>> I I I I I             I I O)
  [(⊢awf Γ ((x : τ) ...))
   (where (cE ρ_′) (⊢extend-ρ′ ((x : τ) ...) ρ))
   (⊢ty>>> ((x = none : τ) ... ) σ ρ_′ m e ee τ_res)
   ------------- WF-FUN
   (⊢fwf>>> Γ σ ρ m ((x : τ) ...) τ_res e (in-hole cE ee))])



;; ************** go through these rules one by one, should I replace m with K? ***********;;
;; Γ means environment
;; K is pointer mode and m is code mode
;; m_' means it falls under m, so change it to K, but the m in ⊢ty>>> Γ σ ρ m e ee τ doesn't need to be changed K
;; in Redex the left thing is what you return, and the right side is the function
;; I also need to define n. Put them where *D* or *Fs* are
;; One big thing to do is make the new bounds check, which will just follow the form of the current bounds check.
;; Then just change assign, and deref for adding the bounds check.
;; Malloc will be more tricky since I need to figure out how splitting the heap works. Basically I need to figure out how to fix malloc to work with our heap '
;; If pointer mode is c, then I do nothing, if t or u then I add 2^*N*-1 (add to n_1), so I just decide if I need to change n_1 or not.
;; For the others, I just need to modify m_' or m's to K
;; Go to e-malloc and eE-malloc
;; For testing, just use the tests from nt-array

;; 1. First, write the new bounds check
;; or first fix the mallocs, and the mallocs should be similar to the ones in nt-array

<<<<<<< Updated upstream
=======
;; Look at the original nt-array file in the master branch, and possibly copy that and modify it instead.

>>>>>>> Stashed changes

;; Typing
(define-judgment-form CoreChkC+
  #:contract (⊢ty>>> Γ σ ρ m e ee τ)
  #:mode     (⊢ty>>> I I I I I O O)

  [(⊢ty>>> Γ σ ρ m x x (ptr K (ntarray le he τ))) ;; changed m_' to K
   (where τ_2 (⊢nt-incr (ptr K (ntarray le he τ))))
   (⊢ty>>> (⊢extend-Γ (x = none : τ_2) Γ) σ ρ m e_1 ee_1 τ_1)
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ_3)
<<<<<<< Updated upstream
   (check_mode m K) ;; I may need to modify check_mode. unexpected judgement form name?
=======
   (where #t (⊢check-mode m K)) ;; I may need to modify check_mode. unexpected judgement form name?
>>>>>>> Stashed changes
   (where τ_4 (⊢join-type Γ τ_1 τ_3))
   ------------- T-IfNT
   (⊢ty>>> Γ σ ρ m (if (* x) e_1 e_2)
           (if (⊢widen-bounds-deref ρ x (ptr K (ntarray le he τ)) (* (if x x (enull))))
               ee_1 ee_2) τ_4)]
  ;; TODO: add join
  [(⊢ty>>> Γ σ ρ m e ee τ)
   (where #f (⊢nt-ptr-deref? Γ e))
   (⊢ty>>> Γ σ ρ m e_1 ee_1 τ_1)
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ_2)
   (where τ_3 (⊢join-type Γ τ_1 τ_2))
   ------------- T-IfNonNT
   (⊢ty>>> Γ σ ρ m (if e e_1 e_2) (if ee ee_1 ee_2) τ_3)]

  [(where (_ τ) (⊢ty-env-lookup Γ x))
   (⊢wf Γ τ)
   ------------- T-Var
   (⊢ty>>> Γ σ ρ m x x τ)]

  ;; POST rules
  ;; replace c with K?
  [(where (_ ... (n : τ) _ ...) σ)
   ------------- T-VConstC
   (⊢ty>>> Γ σ ρ c (n : τ) n τ)]

  ;; POST rules
  [
   ------------- T-VConstT
   (⊢ty>>> Γ σ ρ t (n : τ) n τ)]

  ;; NOTE: this rule is only for function elimination
  ;; the well-formdness judgment handles the introduction
  [(where (defun ((x : τ_2) ..._1 e) : τ) (⊢fun-lookup ,(*F*) n_1))
   (where (τ_2′ ... τ_res) (⊢instantiate-fun-args τ (x τ_2 e_2) ...))
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ_2′′) ...
<<<<<<< Updated upstream
   (⊢subtype τ_2′′  τ_2′) ...
   ------------- T-VCall
   (⊢ty>>> Γ σ ρ m (call n_1 e_2 ..._1) (call left_right n_1 ee_2 ...) τ_res)]
=======
   (⊢subtype τ_2′′  τ_2′) 
   ------------- T-VCall
   (⊢ty>>> Γ σ ρ m (call n_1 e_2 ..._1) (call n_1 ee_2 ...) τ_res)]
>>>>>>> Stashed changes

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 τ_1)
   (where (cE ρ_′) (⊢extend-ρ x τ_1 ρ))
   (⊢ty>>> (⊢extend-Γ (x = e_1 : τ_1) Γ) σ ρ_′ m e_2 ee_2 τ)
   (where #f (⊢checked-strlen-var? Γ e_1))
   ------------- T-LetNonStr
   (⊢ty>>> Γ σ ρ m (let x = e_1 in e_2)
           (let x = ee_1 in (in-hole cE ee_2)) (⊢instantiate-type x e_1 τ))]

  [(where (maybe-e (ptr K (ntarray le he τ_1))) (⊢ty-env-lookup Γ x_2))
   (⊢ty>>> (⊢extend-Γ (x_2 = maybe-e : (ptr K (ntarray le (x_1 + 0) τ_1))) ;; changed m to K
                   (⊢extend-Γ (x_1 = (strlen x_2) : int) Γ))
           σ ρ m e ee τ)
   (where (_ x_high) (⊢bound-var-lookup ρ x_2))
   (where eff ,(variable-not-in (term (x_high x_1 ee)) 'eff_strlen))
   (where τ_2 (⊢instantiate-type x_1 (strlen x_2) τ))
   ------------- T-LetStr
   ;; no need to extend ρ here because x_1 is an integer, not an array pointer
   (⊢ty>>> Γ σ ρ m (let x_1 = (strlen x_2) in e)
           (let x_1 = (strlen (⊢insert-check #f ρ x_2 x_2 (ptr K (ntarray le he τ_1)))) ;; should the m_' be changed to K or K_'?
                in (⊢insert-strlen-widening K x_1 x_high ee)) ;; changed this m_' to K
        τ_2)]

  [(⊢ty>>> Γ σ ρ m e ee (ptr K (ntarray le he τ))) ;; changed m_' to K
   ------------- T-Str
   (⊢ty>>> Γ σ ρ m (strlen e)
        (⊢widen-bounds-strlen ρ e
                              (ptr K (ntarray le he τ))
                              (strlen (⊢insert-check #f ρ e ee (ptr K (ntarray le he τ)))))
        int)]

  [(where #t (⊢base? n τ))
   ------------- T-Base
   (⊢ty>>> Γ σ ρ m (n : τ) n τ)]

  ;; TODO: add proper subtyping
  [(where (ptr c vω) τ) ;; change c to K?
   (where (τ_0 ..._1) (⊢types ,(*D*) vω))
   (where #t (⊢heap-defined? ,(*H*) n vω))
   (where ((n_1 : τ_1) ..._1 _ ...) (⊢heap-from ,(*H*) n vω))
   (where ((n_′ : τ_′) ...) σ)
   (⊢ty>>> Γ ((n : τ) (n_′ : τ_′) ...) ρ m (n_1 : τ_1) n_1 τ_0) ...
   ------------- T-PtrC
   (⊢ty>>> Γ σ ρ m (n : τ) n τ)]

  [(⊢ty>>> Γ σ ρ m e ee (ptr K (struct T))) ;; changed m_' to K
   (where ((τ_0 f_0) ... (τ_f f) _ ...) (⊢struct-lookup ,(*D*) T))
   (where n ,(length (term (τ_0 ...))))
   ------------- T-Amper
   (⊢ty>>> Γ σ ρ m (& e → f) ((⊢insert-null-check′ ρ ee (ptr K (struct T)))  + n) (ptr K τ_f))] ;; changed m_' to K

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 int)
   (⊢ty>>> Γ σ ρ m e_2 ee_2 int)
   ------------- T-BinopInt
   (⊢ty>>> Γ σ ρ m (e_1 + e_2) (ee_1 + ee_2) int)]

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr K ω)) ;; changed m_' to K
   (where ω_′ (⊢bounds-sub ω n))
   (⊢ty>>> Γ σ ρ m (n : τ) n int)
   ------------- T-BinopInd
   (⊢ty>>> Γ σ ρ m (e_1 + (n : τ)) ((⊢insert-null-check′ ρ ee_1 (ptr K ω)) + n) (ptr K ω_′))] ;; changed m_' to K

  [(⊢wf Γ (ptr K ω))
   (where #t (⊢malloc-type-wf ω))
   ------------- T-Malloc
   (⊢ty>>> Γ σ ρ m (malloc K ω) (malloc K (⊢sizeof ω)) (ptr K ω))]

  [ ....;;      list_sub (freeVars e) x... ->
      ;;well_typed env Q u e t ->
      ;;Forall (fun x => Env.MapsTo x t' env -> is_not_c t') x... ->
      ;;is_not_c t ->
   (⊢ty>>> Γ σ ρ u e ee τ)
   ------------- T-Unchecked
   (⊢ty>>> Γ σ ρ m (unchecked x... e) ee τ)]

  [ ....;;      list_sub (freeVars e) x... ->

      ;; well_typed env Q c e t ->
      ;;Forall (fun x => Env.MapsTo x t' env -> is_not_c t') x... ->
      ;;is_not_c t ->
   (⊢ty>>> Γ σ ρ u e ee τ)
   ------------- T-Checked
   (⊢ty>>> Γ σ ρ m (checked x... e) ee τ)]

  [(⊢ty>>> Γ σ ρ m e ee τ_′)
   (where #t (⊢dyn-bound-cast-ok? τ_′ τ))
   (where x_e ,(gensym 'x_e))
   (where ee_′ (⊢insert-bounds-check-dyn ρ x_e e τ_′ τ))
<<<<<<< Updated upstream
   ------------- T-DynCast
=======
   ------------- T-DynCast ;; below this is the original expression. Above are the conditions for below.
>>>>>>> Stashed changes
   (⊢ty>>> Γ σ ρ m (dyn-bound-cast τ e) (let x_e = ee in ee_′) τ)]

  [(⊢ty>>> Γ σ ρ m e ee τ_′)
   (where #t (⊢cast-ok? m τ_′ τ))
<<<<<<< Updated upstream
   ------------- T-Cast
=======
   ------------- T-Cast ;; so above the line are the conditions for checking if the types are correct
>>>>>>> Stashed changes
   (⊢ty>>> Γ σ ρ m (cast τ e) ee τ)]

  [(⊢ty>>> Γ σ ρ m e ee (ptr K ω)) ;;  changed m_' to K
   (where τ (⊢deref-type ω))
   (where #t (⊢mode-ok? K m)) ;; changed m_' to K
   ------------- T-Deref
   (⊢ty>>> Γ σ ρ m (* e) (⊢widen-bounds-deref ρ e (ptr K ω) ;; get x_mode --> if x_mode is c then determine if left or right star
                                           (* (⊢insert-check #f ρ e ee (ptr K ω)))) τ)] ;; changed m_' to K

  ;; generalize T-Index?
  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr K ω)) ;; changed m_' to K
   (⊢ty>>> Γ σ ρ m e_2 ee_2 int)
   (where #t (⊢mode-ok? K m)) ;; changed m_' to K
   (where #f (⊢is-literal? e_2))
   (where #f (⊢is-array-or-nt-array? ω)) ; this used to be #f; I have no idea why
   (where τ (⊢deref-type ω))
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e_1 ω))
   (where (x_ee x_ee1 x_ee2)
          ,(variables-not-in (term (ee_1 ee_2 ρ ω)) '(x x x)))
   ------------- T-Index
   (⊢ty>>> Γ σ ρ m
           (* (e_1 + e_2))
           (* (let x_ee1 = ee_1 in
                   (let x_ee2 = ee_2 in
                        (let x_ee = ((if x_ee1 x_ee1 (enull)) + x_ee2) in
                             (if x_ee
                                 (if (1 <=? (ee_lo - x_ee2))
                                     (ebounds)
                                     (if ((ee_hi - x_ee2) <=? (⊢array-upper-shift #f ω))
                                         (ebounds)
                                         x_ee))
                                 (enull)))))) τ)]

<<<<<<< Updated upstream
=======
  ;; these rules can return errors as something they evaluate to.
>>>>>>> Stashed changes
  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr K ω)) ;; changed m_' to K
   (⊢ty>>> Γ σ ρ m e_2 ee_2 τ)
   (where τ (⊢deref-type ω))
   (where (x_e1 x_e2) ,(variables-not-in (term (ee_1 ee_2 ω τ)) '(x_e1 x_e2)))
   (where #t (⊢mode-ok? K m)) ;; changed m_' to K
   ------------- T-Assign ;; is this the assign to change? But this assign already has a bounds check
   ;; TODO: rewrite without helper functions
   (⊢ty>>> Γ σ ρ m (* e_1 = e_2)
           (let x_e1 = ee_1 in
                (let x_e2 = ee_2 in
<<<<<<< Updated upstream
                     (* (⊢insert-check #t ρ e_1 x_e1 (ptr K ω)) = x_e2))) τ)] ;; changed m_' to K. Also, what does insert-check do???
=======
                     (* (⊢insert-check #t ρ e_1 x_e1 (ptr K ω)) = x_e2))) τ)] ;; changed m_' to K. Also, what does insert-check do??? ebounds evaluates to Bounds
>>>>>>> Stashed changes

  [(⊢ty>>> Γ σ ρ m e_1 ee_1 (ptr K ω)) ;; changed m_' to k
   (⊢ty>>> Γ σ ρ m e_2 ee_2 int)
   (⊢ty>>> Γ σ ρ m e_3 ee_3 τ)
   (where #t (⊢mode-ok? K m)) ;; changed m_' to K
   (where #f (⊢is-literal? e_2))
   (where #f (⊢is-array-or-nt-array? ω))
   (where τ (⊢deref-type ω))
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e_1 ω))
   (where (x_ee1 x_ee2 x_ee3 x_ee),(variables-not-in (term (ee_1 ee_2 ρ ω)) '(x x x x)))
   ------------- T-IndAssign
   (⊢ty>>> Γ σ ρ m (* (e_1 + e_2) = e_3)
           (* (let x_ee1 = ee_1 in
                   (let x_ee2 = ee_2 in
                        (let x_ee3 = ee_3 in
                             (let x_ee = ((if x_ee1 x_ee1 (enull)) + x_ee2) in
                                  (if x_ee
                                      (if (1 <=? (ee_lo - x_ee2))
                                          (ebounds)
                                          (if ((ee_hi - x_ee2) <=? (⊢array-upper-shift #t ω))
                                              (ebounds)
                                              (* x_ee = ee_3)))
                                      (enull))))))) τ)])




;; Everything below here may or may not be needed

;; typing rule that ignores the compiled expression
;; we need this in order to run the old tests
(define-judgment-form CoreChkC+
  #:contract (⊢ty Γ σ m e τ)
  #:mode     (⊢ty I I I I O)
  [(⊢ty>>> Γ σ () m e _ τ)
   -------------
   (⊢ty Γ σ m e τ)])

(define-judgment-form CoreChkC+
  #:contract (⊢awf Γ ((x : τ) ...))
  #:mode     (⊢awf I I)

  [------------- WFA-NIL
   (⊢awf Γ ())]

  [(⊢wf Γ τ_0)
   (⊢awf (⊢extend-Γ (x_0 = none : τ_0) Γ) ((x_1 : τ_1) ...))
   ------------- WFA-CONS
   (⊢awf Γ ((x_0 : τ_0) (x_1 : τ_1) ...))])

(define-judgment-form CoreChkC+
  #:contract (⊢bwf Γ le)
  #:mode     (⊢bwf I I)

  ;; well-formed bounds
  [------------- WFB-INT
   (⊢bwf Γ l)]

  [(where (_ int) (⊢ty-env-lookup Γ x))
   ------------- WFB-VAR
   (⊢bwf Γ (x + l))])

(define-judgment-form CoreChkC+
  #:contract (⊢wf Γ τ)
  #:mode     (⊢wf I I)

  [------------- WF-INT
   (⊢wf Γ int)]

  [(⊢wf Γ τ)
   (⊢bwf Γ le)
   (⊢bwf Γ he)
    ------------- WF-ARPTR
   (⊢wf Γ (ptr m (array le he τ)))]

  [(⊢wf Γ τ)
   (⊢bwf Γ le)
   (⊢bwf Γ he)
    ------------- WF-NTARPTR
   (⊢wf Γ (ptr m (ntarray le he τ)))]

  [------------- WF-STRCT
   (⊢wf Γ (ptr m (struct T)))]

  [(⊢wf Γ τ)
    ------------- WF-TPTR
   (⊢wf Γ (ptr m τ))])

;; do we need to widen bounds with unchecked pointers? probably yes

;; the boolean flag indicates whether we are assigning or not

;; I don't think we need the stuff after this, but I'm not sure. At the very least, the code above is neccessary

(define-metafunction CoreChkC+
  ⊢insert-strlen-widening : m x x ee -> ee
  [(⊢insert-strlen-widening u _ _ ee) ee]
  [(⊢insert-strlen-widening c x_new x_hi ee)
   (let eff = (if (x_new <=? x_hi)
                  0
                  (x_hi = x_new))
        in ee)
   (where eff ,(variable-not-in (term (x_hi x_new ee)) 'eff_strlen))])

;; changed m to K
(define-metafunction CoreChkC+
  ⊢insert-check : boolean ρ e ee (ptr K ω) -> ee
  [(⊢insert-check boolean ρ e ee (ptr K ω))
   (in-hole cE_1 ee_1)
   (where x_e ,(variable-not-in (term (e ee ω)) 'x_e))
   (where cE (let x_e = ee in hole))
   (where (cE_0 ee_0) (⊢insert-bounds-check boolean ρ e cE x_e (ptr K ω)))
   (where (cE_1 ee_1) (⊢insert-null-check cE_0 ee_0 x_e (ptr K ω)))])


(define-metafunction CoreChkC+
  ⊢insert-null-check′ : ρ ee (ptr m ω) -> ee
  [(⊢insert-null-check′ ρ ee (ptr m ω))
   (in-hole cE_0 ee_0)
   (where x_e ,(variable-not-in (term (ρ ee ω)) 'x_e))
   (where cE (let x_e = ee in hole))
   (where (cE_0 ee_0) (⊢insert-null-check cE x_e x_e (ptr m ω)))])

;; change m to K
(define-metafunction CoreChkC+
  ⊢insert-bounds-check-dyn : ρ x e (ptr K ω) (ptr K ω) -> ee
  [(⊢insert-bounds-check-dyn ρ x_e e (ptr K ω) (ptr K (_ le he _)))
   (let x_lo = ee_lo in     ; use macro/metafunction to simplify code?
        (let x_hi = ee_hi in
             (if (x_lo <=? le)
                 (if (he <=? x_hi)
                     x_e
                     (ebounds))
                 (ebounds))))
   (where c K)
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω))
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi)))
   or
   x_e])

<<<<<<< Updated upstream
(define-metafunction CoreChkC+
  ⊢insert-bounds-check : boolean ρ e cE x (ptr K ω) -> (cE ee)
=======
;; relative bounds checking, where the ptr is at 0. x_e is a pointer, so it's just an integer? no.
;; 
(define-metafunction CoreChkC+
  ⊢insert-bounds-check : boolean ρ e cE x (ptr K ω) -> (cE ee) 
>>>>>>> Stashed changes
  [(⊢insert-bounds-check boolean ρ e cE x_e (ptr K ω))
   ((in-hole
     cE
     (let x_lo = ee_lo in     ; use macro/metafunction to simplify code?
          (let x_hi = ee_hi in
               hole)))
    (if (1 <=? x_lo)
        (ebounds)
        (if (x_hi <=? (⊢array-upper-shift boolean ω))
            (ebounds)
            x_e)))
<<<<<<< Updated upstream
   (where c K)
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω))
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi)))
   or
=======
   (where c K) ;; these assign values to be used above. This one specifically says the value of K must be c.
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω))
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi))) ;; where is a helper function that assigns stuff
   or ;; line 56-68, it's the expression before or, and 
>>>>>>> Stashed changes
   (cE x_e)])


;; Make the new bounds check we need right here.
<<<<<<< Updated upstream
(define-metafunction CoreChkC+
  ⊢insert-constant-bounds-check : boolean ρ e cE x (ptr K ω) -> (cE ee)
  [(⊢insert-constant-bounds-check boolean ρ e cE x_e (ptr K ω))
   ((in-hole
     cE
     (let x_lo = (expt 2 (*N*-1)) in     ; use macro/metafunction to simplify code?
          (let x_hi = (expt 2 *N*) in
               hole)))
    (if (1 <=? x_lo) ;; these if statements just define exceptions. so if it passes these exceptions, it's the correct bounds? Otherwise, where should I write my if conditions
        (ebounds)    ;; I need to write my if conditions such that if they are below x_lo, they are in the first heap, and if above and below 2^n, they are in the 2nd heap
        (if (x_hi <=? (⊢array-upper-shift boolean ω)) ;; or do I have the wrong interpretation of x_lo and x_hi? Because I need to understand which ones are the input bounds.
            (ebounds)
            x_e)))
   (where c K)
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω)) ;; we don't need this? Or is ee_lo and ee_hi the input bounds? I'm confused right now about this
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi))) 
   or
   (cE x_e)]) ;; or (cE x_e) just returns the results of (cE x_e) doesn't it? Or is it like, it returns the above or below?
=======
;; 
(define-metafunction CoreChkC+
  ⊢insert-constant-bounds-check : boolean ρ e cE x (ptr K ω) -> (cE ee)
  [(⊢insert-constant-bounds-check boolean ρ e cE x_e (ptr c ω)) ;; checked half
   ((in-hole
     cE
     (let x_lo = ee_lo in     ; use macro/metafunction to simplify code?
          (let x_hi = ee_hi in
               hole))) ;; this returns cE. This part is just getting the cE, it's not doing the check.
    ;; this is where the checking happens, and is where I should put in the 2^n etc.
    (if (x_e <=? -1) ;; these if statements just define exceptions. so if it passes these exceptions, it's the correct bounds? Otherwise, where should I write my if conditions
        (ebounds)    ;; I need to write my if conditions such that if they are below x_lo, they are in the first heap, and if above and below 2^n, they are in the 2nd heap
        (if (((expt 2 (*N*-1)) + 1) <=? x_e) ;; or do I have the wrong interpretation of x_lo and x_hi? Because I need to understand which ones are the input bounds.
            (ebounds)
            x_e))) ;; and this part returns ee
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω)) ;; we don't need this? Or is ee_lo and ee_hi the input bounds? I'm confused right now about this
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi))) 
   or
   (cE x_e)] ;; or (cE x_e) just returns the results of (cE x_e) doesn't it? Or is it like, it returns the above or below?
  [(⊢insert-constant-bounds-check boolean ρ e cE x_e (ptr K ω)) ;; unchecked/tainted half.
   ((in-hole
     cE
     (let x_lo = ee_lo in     ; use macro/metafunction to simplify code?
          (let x_hi = ee_hi in
               hole))) ;; this returns cE. This part is just getting the cE, it's not doing the check.
    ;; this is where the checking happens, and is where I should put in the 2^n etc. So I should modify these checks.
    (if (x_e <=? (expt 2 (*N*-1))) ;; these if statements just define exceptions. so if it passes these exceptions, it's the correct bounds? Otherwise, where should I write my if conditions
        (ebounds)    ;; I need to write my if conditions such that if they are below x_lo, they are in the first heap, and if above and below 2^n, they are in the 2nd heap
        (if ((expt 2 *N*) <=? x_e) ;; Since I have fixed bounds, I don't need array upper shift anymore.
            (ebounds)
            x_e))) ;; and this part returns ee
   (where (ee_lo ee_hi) (⊢get-accurate-bounds ρ e ω)) ;; we don't need this? Or is ee_lo and ee_hi the input bounds? I'm confused right now about this
   (where (x_lo x_hi) ,(variables-not-in (term (ee_lo ee_hi x ω)) '(x_lo x_hi)))
   (side-condition (or (eq? (term K) 'u) (eq? (term K) 't)))
   or
   (cE x_e)]) 
>>>>>>> Stashed changes


(define-metafunction CoreChkC+
  ⊢insert-null-check : cE ee x (ptr m ω) -> (cE ee)
  [(⊢insert-null-check cE ee x_e (ptr m ω))
   (cE
    (if x_e
        ee
        (enull)))
   (where c m)
   or
   (cE x_e)])

(define-metafunction CoreChkC+
  ⊢array-upper-shift : boolean ω -> -1 or 0
  [(⊢array-upper-shift #f (ntarray _ _ _)) -1]
  [(⊢array-upper-shift _ _) 0])


(define-metafunction CoreChkC+
  ⊢get-accurate-bounds : ρ e ω -> (ee ee) or #f
  [(⊢get-accurate-bounds ρ e ω)
   (x_lo x_hi)
   (where x e)
   (where (x_lo x_hi) (⊢bound-var-lookup ρ x))
   or
   (⊢array-bounds ω)])


(define-metafunction CoreChkC+
  ⊢array-bounds : ω -> (ee ee) or #f
  [(⊢array-bounds (ntarray le he _))
   (le he)]
  [(⊢array-bounds (array le he _))
   (le he)]
  [(⊢array-bounds _)
   #f])


(define-metafunction CoreChkC+
  ⊢bound-var-lookup : ρ x -> (x x) or #f
  [(⊢bound-var-lookup ((x (x_lo x_hi)) _ ...) x)
   (x_lo x_hi)]
  [(⊢bound-var-lookup (_ (x_′ (x_lo′ x_hi′)) ...) x)
   (⊢bound-var-lookup ((x_′ (x_lo′ x_hi′)) ...) x)]
  [(⊢bound-var-lookup _ _) #f])


(define-metafunction CoreChkC+
  ⊢widen-bounds-deref : ρ e τ ee -> ee
  [(⊢widen-bounds-deref ρ e τ ee)
   (let x_derefed = ee in
        (if x_derefed
            (if x_hi
                x_derefed
                (let eff = (x_hi = 1) in x_derefed))
            x_derefed))
   (where (ptr c (ntarray _ _ _)) τ)
   (where #t (⊢nt-ptr? τ))
   (where x e)                          ; ee represents the compiled version of (* e_0 ...)
   (where (_ x_hi) (⊢bound-var-lookup ρ x)) ; e represents e_0 only
   (where (eff x_derefed) ,(variables-not-in (term (τ e ee ρ)) '(eff_ifnt x_derefed)))
   or
   ee])


(define-metafunction CoreChkC+
  ⊢widen-bounds-strlen : ρ e τ ee -> ee
  [(⊢widen-bounds-strlen ρ e τ ee)
   (let x_ee = ee in
        (if (x_ee <=? x_hi)
            x_ee
            (x_hi = x_ee)))
   (where #t (⊢nt-ptr? τ))
   (where x e)                          ; ee represents the compiled version of (strlen e_0 ...)
   (where (_ x_hi) (⊢bound-var-lookup ρ x)) ; e represents e_0 only
   (where (x_ee) ,(variables-not-in (term (τ e ee ρ)) '(x_ee)))
   or
   ee])

;; already defined
;(define-metafunction CoreChkC+
;  ⊢sizeof : ω -> ee or #f
;  [(⊢sizeof τ) 1]
;  [(⊢sizeof (struct T)) ,(length (term (⊢struct-lookup ,(*D*) T)))]
;  [(⊢sizeof (array 0 he _)) he]
;  [(⊢sizeof (ntarray 0 (x + i) _)) (x + ,(+ 1 (term i)))]
;  [(⊢sizeof (ntarray 0 i _)) ,(+ 1 (term i))]
;  [(⊢sizeof _) ,(raise 'impossible)])



(define-metafunction CoreChkC+
  ⊢dyn-bound-cast-ok? : τ τ -> #t or #f
  [(⊢dyn-bound-cast-ok? (ptr c (ntarray _ _ τ)) (ptr c (ntarray _ _ τ))) #t]
  [(⊢dyn-bound-cast-ok? (ptr c (array _ _ τ)) (ptr c (array _ _ τ))) #t]
  [(⊢dyn-bound-cast-ok? _ _) #f])

(define-metafunction CoreChkC+
  ⊢nt-ptr-deref? : Γ e -> #t or #f
  [(⊢nt-ptr-deref? Γ (* x))
   #t
   (where (_ (ptr c (ntarray _ _ _))) (⊢ty-env-lookup Γ x))]
  [(⊢nt-ptr-deref? _ _) #f])


(define-metafunction CoreChkC+
  ⊢ty-env-lookup : Γ x -> (maybe-e τ) or #f
  [(⊢ty-env-lookup () _) #f]
  [(⊢ty-env-lookup ((x = maybe-e : τ) _ ...) x) (maybe-e τ)]
  [(⊢ty-env-lookup (_ (x_′ = maybe-e_′ : τ_′) ...) x)
   (⊢ty-env-lookup ((x_′ = maybe-e_′ : τ_′) ...) x)])

;; already defined
;(define-metafunction CoreChkC+
;  ⊢base? : n τ -> #t or #f
;  [(⊢base? n int) #t]
;  [(⊢base? n (ptr u ω)) #t]
;  [(⊢base? 0 τ) #t]
;  [(⊢base? n (ptr c (array 0 0 τ_′))) #t]
;  [(⊢base? n (ptr c (ntarray 0 0 τ_′))) #t]
;  [(⊢base? _ _) #f])

(define-metafunction CoreChkC+
  ⊢cast-ok? : m τ τ -> #t or #f
  [(⊢cast-ok? u _ τ) #t]
  [(⊢cast-ok? c _ int) #t]
  [(⊢cast-ok? c _ (ptr u ω)) #t]
  [(⊢cast-ok? c τ_′ τ) #t
   (judgment-holds (⊢subtype τ_′ τ))]
  [(⊢cast-ok? _ _ _) #f])

;; already defined
;; deref-type under the context of operational semantics
;(define-metafunction CoreChkC+
;  ⊢deref-type-dyn : D τ -> τ
;  [(⊢deref-type-dyn _ int) int]
;  [(⊢deref-type-dyn _ (ptr m τ)) τ]
;  [(⊢deref-type-dyn _ (ptr m (ntarray _ _ τ))) τ]
;  [(⊢deref-type-dyn _ (ptr m (array _ _ τ))) τ]
;  [(⊢deref-type-dyn D (ptr m (struct T)))
;   τ_1
;   (where ((τ_1 _) _ ...) (⊢struct-lookup D T))])

;; already defined
;(define-metafunction CoreChkC+
;  ⊢deref-type : ω -> τ
;  [(⊢deref-type τ) τ]
;  [(⊢deref-type (array le he τ)) τ]
;  [(⊢deref-type (ntarray le he τ)) τ])


(define-metafunction CoreChkC+
  ⊢mode-ok? : m m -> #t or #f
  [(⊢mode-ok? u u) #t]
  [(⊢mode-ok? c _) #t]
  [(⊢mode-ok? _ _) #f])