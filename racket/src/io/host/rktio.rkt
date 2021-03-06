#lang racket/base
(require racket/include
         (only-in '#%linklet primitive-table))

(provide rktio
         rktio-error?
         rktio-errkind
         rktio-errno
         rktio-errstep
         racket-error?)
;; Move `provide`s added by macros

(define rktio-table
  (or (primitive-table '#%rktio)
      (error '#%rktio "rktio not supported by host")))

(define (lookup n)
  (hash-ref rktio-table n))

(define << arithmetic-shift)

(define-syntax-rule (define-constant n v)
  (begin
    (define n v)
    (provide n)))
  
(define-syntax-rule (define-type . _) (void))
(define-syntax-rule (define-struct-type . _) (void))

(define-syntax-rule (define-function _ name . _)
  (begin
    (define name (lookup 'name))
    (provide name)))

(define-syntax-rule (define-function/errno _ _ name . _)
  (define-function #f name))
(define-syntax-rule (define-function/errno+step _ _ name . _)
  (define-function #f name))

(include "../compiled/rktio.rktl")

(define-function #f rktio_filesize_ref)
(define-function #f rktio_timestamp_ref)
(define-function #f rktio_is_timestamp)
(define-function #f rktio_recv_length_ref)
(define-function #f rktio_recv_address_ref)
(define-function #f rktio_identity_to_vector)
(define-function #f rktio_convert_result_to_vector)
(define-function #f rktio_to_bytes)
(define-function #f rktio_to_bytes_list)
(define-function #f rktio_to_shorts)
(define-function #f rktio_NULL)
(define-function #f rktio_do_install_os_signal_handler)
(define-function #f rktio_get_ctl_c_handler)

;; Error results are represented as vectors:
(define rktio-error? vector?)
(define (rktio-errkind v) (vector-ref v 0))
(define (rktio-errno v) (vector-ref v 1))
(define (rktio-errstep v) (vector-ref v 2))

(define (racket-error? v errno)
  (and (eqv? (rktio-errkind v) RKTIO_ERROR_KIND_RACKET)
       (eqv? (rktio-errno v) errno)))

(define rktio (rktio_init))

(void (rktio_do_install_os_signal_handler rktio))
