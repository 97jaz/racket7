(library (io)
  (export)
  (import (except (chezpart)
                  close-port)
          (rename (only (chezscheme)
                        read-char peek-char
                        current-directory
                        error
                        input-port? output-port?
                        file-position flush-output-port
                        file-symbolic-link?)
                  [input-port? chez:input-port?]
                  [output-port? chez:output-port?]
                  [flush-output-port flush-output])
          (core)
          (thread))

  ;; ----------------------------------------
  ;; Tie knots:

  (define (path? v) (is-path? v))
  (define (path->string v) (1/path->string v))
  (define path->complete-path
    (case-lambda
     [(v) (1/path->complete-path v)]
     [(v wrt) (1/path->complete-path v wrt)]))
  (define (absolute-path? v) (1/absolute-path? v))
  (define (relative-path? v) (1/relative-path? v))

  ;; ----------------------------------------

  (module (|#%rktio-instance|)
    (meta define (convert-type t)
          (syntax-case t (ref *ref rktio_bool_t rktio_const_string_t)
            [(ref . _) #'uptr]
            [(*ref . _) #'u8*]
            [rktio_bool_t #'boolean]
            [rktio_const_string_t #'u8*]
            [else t]))

    (define-ftype intptr_t iptr)
    (define-ftype uintptr_t uptr)
    (define-ftype rktio_int64_t integer-64)
    (define _uintptr _uint64)
    (define NULL 0)

    (define (<< a b) (bitwise-arithmetic-shift-left a b))

    (define-syntax define-constant
      (syntax-rules ()
        [(_ id expr) (define id expr)]))
    
    (define-syntax (define-type stx)
      (syntax-case stx (rktio_const_string_t rktio_ok_t rktio_bool_t)
        [(_ rktio_const_string_t old_type)
         ;; skip
         #'(begin)]
        [(_ rktio_ok_t old_type)
         (with-syntax ([(_ type _) stx])
           #'(define-ftype type boolean))]
        [(_ rktio_bool_t old_type)
         (with-syntax ([(_ type _) stx])
           #'(define-ftype type boolean))]
        [(_ type old-type)
         (with-syntax ([old-type (convert-type #'old-type)])
           #'(define-ftype type old-type))]))

    (define-syntax (define-struct-type stx)
      (syntax-case stx ()
        [(_ type ([old-type field] ...))
         (with-syntax ([(old-type ...) (map convert-type #'(old-type ...))])
           #'(define-ftype type (struct [field old-type] ...)))]))

    (define-syntax (let-wrappers stx)
      ;; When an argument has type `rktio_const_string_t`, add an
      ;; explicit NUL terminator byte; when an argument has a
      ;; `nullable` wrapper, then add a #f -> 0 conversion
      (syntax-case stx (rktio_const_string_t ref nullable)
        [(_ () body) #'body]
        [(_ ([rktio_const_string_t arg-name] . args) body)
         #'(let ([arg-name (add-nul-terminator arg-name)])
             (let-wrappers args body))]
        [(_ ([(nullable type) arg-name] . args) body)
         #'(let ([arg-name (or arg-name 0)])
             (let-wrappers args body))]
        [(_ ([(ref type) arg-name] . args) body)
         #'(let-wrappers ([type arg-name] . args) body)]
        [(_ (_ . args) body)
         #'(let-wrappers args body)]))
    (define (add-nul-terminator bstr)
      (and bstr (bytes-append bstr '#vu8(0))))

    (meta define (convert-function stx)
          (syntax-case stx ()
            [(_ ret-type name ([orig-arg-type arg-name] ...))
             (with-syntax ([ret-type (convert-type #'ret-type)]
                           [(arg-type ...) (map convert-type #'(orig-arg-type ...))])
               #'(let ([proc (foreign-procedure (rktio-lookup 'name)
                                                (arg-type ...)
                                                ret-type)])
                   (lambda (arg-name ...)
                     (let-wrappers
                      ([orig-arg-type arg-name] ...)
                      (proc arg-name ...)))))]))

    (define-syntax (define-function stx)
      (syntax-case stx ()
        [(_ _ name . _)
         (with-syntax ([rhs (convert-function stx)])
           #'(define name rhs))]))

    (define-syntax (define-function*/errno stx)
      (syntax-case stx ()
        [(_ err-val err-expr ret-type name ([rktio-type rktio] [arg-type arg] ...))
         (with-syntax ([rhs (convert-function
                             #'(define-function ret-type name ([rktio-type rktio] [arg-type arg] ...)))])
           #'(define name
               (let ([proc rhs])
                 (lambda (rktio arg ...)
                   (let ([v (proc rktio arg ...)])
                     (if (eqv? v err-val)
                         err-expr
                         v))))))]))

    (define-syntax define-function/errno
      (syntax-rules ()
        [(_ err-val ret-type name ([rktio-type rktio] [arg-type arg] ...))
         (define-function*/errno err-val
           (vector (rktio_get_last_error_kind rktio)
                   (rktio_get_last_error rktio))
           ret-type name ([rktio-type rktio] [arg-type arg] ...))]))
    
    (define-syntax define-function/errno+step
      (syntax-rules ()
        [(_ err-val ret-type name ([rktio-type rktio] [arg-type arg] ...))
         (define-function*/errno err-val
           (vector (rktio_get_last_error_kind rktio)
                   (rktio_get_last_error rktio)
                   (rktio_get_last_error_step rktio))
           ret-type name ([rktio-type rktio] [arg-type arg] ...))]))

    (define loaded-librktio
      (load-shared-object (string-append "../../lib/librktio"
                                         (utf8->string (system-type 'so-suffix)))))

    (define (rktio-lookup name)
      (foreign-entry (symbol->string name)))

    (include "../io/compiled/rktio.rktl")

    (define (rktio_filesize_ref fs)
      (ftype-ref rktio_filesize_t () (make-ftype-pointer rktio_filesize_t fs) 0))
    (define (rktio_timestamp_ref fs)
      (ftype-ref rktio_timestamp_t () (make-ftype-pointer rktio_timestamp_t fs) 0))
    (define (rktio_is_timestamp v)
      (let ([radix (arithmetic-shift 1 (sub1 (* 8 (ftype-sizeof rktio_timestamp_t))))])
        (<= (- radix) v (sub1 radix))))

    (define (rktio_recv_length_ref fs)
      (ftype-ref rktio_length_and_addrinfo_t (len) (make-ftype-pointer rktio_length_and_addrinfo_t fs) 0))

    (define (rktio_recv_address_ref fs)
      (ftype-ref rktio_length_and_addrinfo_t (address) (make-ftype-pointer rktio_length_and_addrinfo_t fs) 0))

    (define (rktio_identity_to_vector p)
      (let ([p (make-ftype-pointer rktio_identity_t p)])
        (vector
         (ftype-ref rktio_identity_t (a) p 0)
         (ftype-ref rktio_identity_t (b) p 0)
         (ftype-ref rktio_identity_t (c) p 0)
         (ftype-ref rktio_identity_t (a_bits) p 0)
         (ftype-ref rktio_identity_t (b_bits) p 0)
         (ftype-ref rktio_identity_t (c_bits) p 0))))
    
    (define (rktio_convert_result_to_vector p)
      (let ([p (make-ftype-pointer rktio_convert_result_t p)])
        (vector
         (ftype-ref rktio_convert_result_t (in_consumed) p 0)
         (ftype-ref rktio_convert_result_t (out_produced) p 0)
         (ftype-ref rktio_convert_result_t (converted) p 0))))

      (define (cast v from to)
        (let ([p (malloc from)])
          (ptr-set! p from v)
          (ptr-ref p to)))

    (define (rktio_to_bytes fs)
      (cast fs _uintptr _bytes))

    (define (rktio_to_shorts fs)
      (cast fs _uintptr _short_bytes))

    ;; Unlike `rktio_to_bytes`, frees the array and strings
    (define rktio_to_bytes_list
      (case-lambda
       [(lls) (rktio_to_bytes_list lls #f)]
       [(lls len)
        (begin0
         (let loop ([i 0])
           (cond
            [(and len (fx= i len))
             '()]
            [else
             (let ([bs (foreign-ref 'uptr lls (* i (foreign-sizeof 'uptr)))])
               (if (not (eqv? 0 bs))
                   (cons (begin0
                          (cast bs _uintptr _bytes)
                          (rktio_free bs))
                         (loop (add1 i)))
                   '()))]))
         (rktio_free lls))]))

    (define (rktio_do_install_os_signal_handler rktio)
      (rktio_install_os_signal_handler rktio))

    (define (rktio_get_ctl_c_handler)
      (get-ctl-c-handler))

    (define |#%rktio-instance|
      (let ()
        (define-syntax extract-functions
          (syntax-rules (define-constant
                          define-type
                          define-struct-type
                          define-function
                          define-function/errno
                          define-function/errno+step)
            [(_ accum) (hasheq . accum)]
            [(_ accum (define-constant . _) . rest)
             (extract-functions accum . rest)]
            [(_ accum (define-type . _) . rest)
             (extract-functions accum . rest)]
            [(_ accum (define-struct-type . _) . rest)
             (extract-functions accum . rest)]
            [(_ accum (define-function _ id . _) . rest)
             (extract-functions ('id id . accum) . rest)]
            [(_ accum (define-function/errno _ _ id . _) . rest)
             (extract-functions ('id id . accum) . rest)]
            [(_ accum (define-function/errno+step _ _ id . _) . rest)
             (extract-functions ('id id . accum) . rest)]))
        (define-syntax begin
          (syntax-rules ()
            [(begin form ...)
             (extract-functions ['rktio_NULL
                                 NULL
                                 'rktio_filesize_ref rktio_filesize_ref
                                 'rktio_timestamp_ref rktio_timestamp_ref
                                 'rktio_is_timestamp rktio_is_timestamp
                                 'rktio_recv_length_ref rktio_recv_length_ref
                                 'rktio_recv_address_ref rktio_recv_address_ref
                                 'rktio_identity_to_vector rktio_identity_to_vector
                                 'rktio_convert_result_to_vector rktio_convert_result_to_vector
                                 'rktio_to_bytes rktio_to_bytes
                                 'rktio_to_bytes_list rktio_to_bytes_list
                                 'rktio_to_shorts rktio_to_shorts
                                 'rktio_do_install_os_signal_handler rktio_do_install_os_signal_handler
                                 'rktio_get_ctl_c_handler rktio_get_ctl_c_handler]
                                form ...)]))
        (include "../io/compiled/rktio.rktl"))))
  
  ;; ----------------------------------------

  (define format
    (case-lambda
     [(fmt arg)
      (unless (equal? fmt "~s")
        (raise-arguments-error 'format "should only be used as a fallback"
                               "format string" fmt
                               "argument" arg))
      (cond
       [(and (record? arg)
             (or (not (impersonator? arg))
                 (record? (unsafe-struct*-ref arg 0))))
        (let ([arg (if (impersonator? arg)
                       (unsafe-struct*-ref arg 0)
                       arg)])
          (chez:format "#<~a>" (record-type-name (record-rtd arg))))]
       [else
        (chez:format "~s" arg)])]
     [(fmt . args)
      (raise-arguments-error 'format "should only be used as a fallback"
                             "format string" fmt
                             "arguments" args)]))

  ;; ----------------------------------------

  (define (system-path-convention-type) 'unix)

  (define (primitive-table key)
    (case key
      [(|#%thread|) |#%thread-instance|]
      [(|#%rktio|) |#%rktio-instance|]
      [else #f]))

  (include "compiled/io.scm")
  
  ;; Initialize:
  (|#%app| 1/current-directory (current-directory))
  (|#%app| 1/current-directory-for-user (current-directory))
  (set-log-system-message! (lambda (level str)
                             (1/log-message (|#%app| 1/current-logger) level str #f)))
  (set-error-display-eprintf! (lambda (fmt . args)
                                (apply 1/fprintf (|#%app| 1/current-error-port) fmt args))))
