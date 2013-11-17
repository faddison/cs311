#lang plai-typed

(require "typed-lang2.rkt")

;;;;;;;;;; Store Definitions ;;;;;;;;;;;;;;
;; Please consider the interface to the store to be:
;; - the types Location, Cell, and Store
;;   (and associated functions like cell-location)
;; - the variable empty-store
;; - the store-lookup, fresh-loc, update-store,
;;   and alloc-store functions
;;
;; TODO: complete fresh-loc, and alloc-store!

(define-type Cell
 [cell (location : Location) (value : ValueC)])

(define-type-alias Store (listof Cell))
(define empty-store empty)

; find the value stored at the given location
; (with an error on an unallocated location)
(define (store-lookup [locn : Location] [store : Store]) : ValueC
 (cond [(empty? store)
        (interp-error (string-append "Unallocated cell: "
                                     (to-string locn)))]
       [(= locn (cell-location (first store)))
        (cell-value (first store))]
       [else
        (store-lookup locn (rest store))]))

; produce a fresh location not presently in the store
(define (fresh-loc [store : Store]) : Location
 ;; TODO: implement me!
 ;; Hint: can you find out what the largest
 ;; location in the store is?  Once you have
 ;; that, can you calculate a fresh location?
 0)

; update the store to contain the given value at the given location
; PRESENTLY: no check that the location already exists
(define (update-store [locn : Location]
                     [value : ValueC]
                     [store : Store]) : Store
 (cons (cell locn value) store))

; allocate the given value at a new location in the store,
; producing the location used and the new store.
;
; to get the Location and Store out of the result, use
; code like:
;
; (local [(define-values (locn store) (alloc-store ...))]
;   ...)
;
; PRESENTLY: no check that the location already exists
; We may want to add that in the future.
(define (alloc-store [value : ValueC]
                    [store : Store]) : (Location * Store)
 ;; TODO: implement me!
 (values 0 empty-store))


(module+ test
  (local ((define store0 empty-store)
          (define-values (locn1 store1) (alloc-store (NumV 1) store0))
          (define-values (locn2 store2) (alloc-store (NumV 2) store1))
          (define-values (locn3 store3) (alloc-store (NumV 3) store2)))
    
    ; Sadly, these don't work because of the implementation of interp-error.
    ;(test/exn (store-lookup (fresh-loc store0) store0) "Unallocated cell:")
    ;(test/exn (store-lookup (fresh-loc store1) store1) "Unallocated cell:")
    ;(test/exn (store-lookup (fresh-loc store2) store2) "Unallocated cell:")
    ;(test/exn (store-lookup (fresh-loc store3) store3) "Unallocated cell:")
    
    ; Instead, we'll do this.
    (begin
      (test (member (fresh-loc store1) (list locn1)) false)
      (test (member (fresh-loc store2) (list locn1 locn2)) false)
      (test (member (fresh-loc store3) (list locn1 locn2 locn3)) false)
      
      (test (store-lookup locn1 store1) (NumV 1))
      (test (store-lookup locn1 store2) (NumV 1))
      (test (store-lookup locn2 store2) (NumV 2))
      (test (store-lookup locn1 store3) (NumV 1))
      (test (store-lookup locn2 store3) (NumV 2))
      (test (store-lookup locn3 store3) (NumV 3))
      (test (store-lookup locn1 (update-store locn1 (NumV -1) store1))
            (NumV -1))
      (test (store-lookup locn1 (update-store locn1 (NumV -1) store3))
            (NumV -1))
      (test (store-lookup locn3 (update-store locn1 (NumV -1) store3))
            (NumV 3))
      (test (store-lookup locn1 (update-store locn3 (NumV -3) store3))
            (NumV 1))
      (test (store-lookup locn3 (update-store locn3 (NumV -3) store3))
            (NumV -3)))))

(define-type Result
  [v*s (value : ValueC) (store : Store)])

(define (interp-full [exprC : ExprC] [env : Env] [store : Store]) : Result
  (type-case ExprC exprC
;; TODO: implement all remaining cases of ExprC; you will certainly
;;       want helper functions (like the Lookup metafunction
;;       described in the ParselTongue specifictaion!)    
    [NumC (n) (v*s (NumV n) store)]
    [else (interp-error (string-append "Haven't covered a case yet:"
                                       (to-string exprC)))]))

(define (interp [exprC : ExprC]) : ValueC
  (type-case Result (interp-full exprC empty empty)
    [v*s (value store) value]))

