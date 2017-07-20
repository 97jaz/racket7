#lang racket/base
(require "../host/rktio.rkt"
         "../host/error.rkt"
         "../host/thread.rkt"
         "../sandman/main.rkt"
         "../file/error.rkt"
         "port.rkt"
         "input-port.rkt"
         "output-port.rkt"
         "peek-via-read-port.rkt"
         "file-stream.rkt"
         "file-truncate.rkt"
         "buffer-mode.rkt"
         "close.rkt")

(provide open-input-host
         open-output-host
         terminal-port?)

(struct host-data (host-fd) ; host-system file descriptor
  #:property prop:file-stream #t
  #:property prop:file-truncate (case-lambda
                                  [(hd pos)
                                   (check-rktio-error*
                                    (rktio_set_file_size rktio
                                                         (host-data-host-fd hd)
                                                         pos)
                                    "error setting file size")]))

;; in atomic mode
(define (host-close host-fd)
  (define v (rktio_close rktio host-fd))
  (when (rktio-error? v)
    (end-atomic)
    (raise-rktio-error #f v "error closing stream port")))

;; ----------------------------------------

;; in atomic mode
;; Current custodian must not be shut down.
(define (open-input-host host-fd name)
  (define-values (port buffer-control)
    (open-input-peek-via-read
     #:name name
     #:data (host-data host-fd)
     #:read-in
     ;; in atomic mode
     (lambda (dest-bstr start end copy?)
       (define n (rktio_read_in rktio host-fd dest-bstr start end))
       (cond
         [(rktio-error? n)
          (raise-filesystem-error #f n "error reading from stream port")]
         [(eqv? n RKTIO_READ_EOF) eof]
         [(eqv? n 0) (wrap-evt (fd-evt host-fd RKTIO_POLL_READ)
                               (lambda (v) 0))]
         [else n]))
     #:read-is-atomic? #t
     #:close
     ;; in atomic mode
     (lambda ()
       (host-close host-fd)
       (unsafe-custodian-unregister host-fd custodian-reference))
     #:file-position (make-file-position
                      host-fd
                      (case-lambda
                        [() (buffer-control)]
                        [(pos) (buffer-control pos)]))))
  (define custodian-reference
    (register-fd-close (current-custodian) host-fd port))
  port)

;; ----------------------------------------

;; in atomic mode
;; Current custodian must not be shut down.
(define (open-output-host host-fd name #:buffer-mode [buffer-mode 'infer])
  (define buffer (make-bytes 4096))
  (define buffer-start 0)
  (define buffer-end 0)
  (define flush-handle
    (plumber-add-flush! (current-plumber)
                        (lambda (h)
                          (flush-buffer-fully #f)
                          (plumber-flush-handle-remove! h))))
  
  (when (eq? buffer-mode 'infer)
    (if (rktio_fd_is_terminal rktio host-fd)
        (set! buffer-mode 'line)
        (set! buffer-mode 'block)))

  (define evt (fd-evt host-fd RKTIO_POLL_WRITE))

  ;; in atomic mode
  ;; Returns `#t` if the buffer is already or successfully flushed
  (define (flush-buffer)
    (cond
      [(not (= buffer-start buffer-end))
       (define n (rktio_write_in rktio host-fd buffer buffer-start buffer-end))
       (cond
         [(rktio-error? n)
          (end-atomic)
          (raise-filesystem-error #f n "error writing to stream port")]
         [(zero? n)
          #f]
         [else
          (define new-buffer-start (+ buffer-start n))
          (cond
            [(= new-buffer-start buffer-end)
             (set! buffer-start 0)
             (set! buffer-end 0)
             #t]
            [else
             (set! buffer-start new-buffer-start)
             #f])])]
      [else #t]))

  ;; in atomic mode
  (define (flush-buffer-fully enable-break?)
    (let loop ()
      (unless (flush-buffer)
        (end-atomic)
        (if enable-break?
            (sync/enable-break evt)
            (sync evt))
        (start-atomic)
        (when buffer ; in case it was closed
          (loop)))))

  ;; in atomic mode
  (define (flush-buffer-fully-if-newline src-bstr src-start src-end enable-break?)
    (for ([b (in-bytes src-bstr src-start src-end)])
      (define newline? (or (eqv? b (char->integer #\newline))
                           (eqv? b (char->integer #\return))))
      (when newline? (flush-buffer-fully enable-break?))
      #:break newline?
      (void)))

  (define port
    (make-core-output-port
     #:name name
     #:data (host-data host-fd)

     #:evt evt
     
     #:write-out
     ;; in atomic mode
     (lambda (src-bstr src-start src-end nonbuffer/nonblock? enable-break? copy?)
       (cond
         [(= src-start src-end)
          ;; Flush request
          (and (flush-buffer) 0)]
         [(and (not nonbuffer/nonblock?)
               (< buffer-end (bytes-length buffer)))
          (define amt (min (- src-end src-start) (- (bytes-length buffer) buffer-end)))
          (bytes-copy! buffer buffer-end src-bstr src-start (+ src-start amt))
          (set! buffer-end (+ buffer-end amt))
          (unless nonbuffer/nonblock?
            (when (eq? buffer-mode 'line)
              ;; can temporarily leave atomic mode:
              (flush-buffer-fully-if-newline src-bstr src-start src-end enable-break?)))
          amt]
         [(not (flush-buffer)) ; <- can temporarily leave atomic mode
          #f]
         [else
          (define n (rktio_write_in rktio host-fd src-bstr src-start src-end))
          (cond
            [(rktio-error? n)
             (end-atomic)
             (raise-filesystem-error #f n "error writing to stream port")]
            [else n])]))

     #:get-write-evt-via-write-out? #t

     #:close
     ;; in atomic mode
     (lambda ()
       (flush-buffer-fully #f) ; can temporarily leave atomic mode
       (when buffer ; <- in case a concurrent close succeeded
         (plumber-flush-handle-remove! flush-handle)
         (set! buffer #f)
         (host-close host-fd)
         (unsafe-custodian-unregister host-fd custodian-reference)))

     #:file-position (make-file-position
                      host-fd
                      (case-lambda
                        [()
                         (start-atomic)
                         (flush-buffer-fully #f)
                         (end-atomic)]
                        [(pos)
                         (+ pos (- buffer-end buffer-start))]))
     #:buffer-mode (case-lambda
                     [() buffer-mode]
                     [(mode) (set! buffer-mode mode)])))

  (define custodian-reference
    (register-fd-close (current-custodian) host-fd port))

  port)

;; ----------------------------------------

(define (terminal-port? p)
  (define data
    (core-port-data
     (cond
       [(input-port? p) (->core-input-port p)]
       [(output-port? p) (->core-output-port p)]
       [else
        (raise-argument-error 'terminal-port? "port?" p)])))
  (and (host-data? p)
       (rktio_fd_is_terminal (host-data-host-fd p))))

;; ----------------------------------------

(define (make-file-position host-fd buffer-control)
  (case-lambda
    [()
     (start-atomic)
     (define ppos (rktio_get_file_position rktio host-fd))
     (cond
       [(rktio-error? ppos)
        (end-atomic)
        (check-rktio-error* ppos "error getting stream position")]
       [else
        (define pos (rktio_filesize_ref ppos))
        (rktio_free ppos)
        (end-atomic)
        (buffer-control pos)])]
    [(pos)
     (buffer-control)
     (check-rktio-error*
      (rktio_set_file_position rktio
                               host-fd
                               (if (eof-object? pos)
                                   0
                                   pos)
                               (if (eof-object? pos)
                                   RKTIO_POSITION_FROM_END
                                   RKTIO_POSITION_FROM_START))
      "error setting stream position")]))

;; ----------------------------------------

(struct fd-evt (fd mode)
  #:property
  prop:evt
  (poller
   ;; This function is called by the scheduler for `sync` to check
   ;; whether the file descriptor has data available:
   (lambda (fde ctx)
     (define mode (fd-evt-mode fde))
     (start-atomic)
     (define ready?
       (or
        (and (eqv? RKTIO_POLL_READ (bitwise-and mode RKTIO_POLL_READ))
             (eqv? (rktio_poll_read_ready rktio (fd-evt-fd fde))
                   RKTIO_POLL_READY))
        (and (eqv? RKTIO_POLL_WRITE (bitwise-and mode RKTIO_POLL_WRITE))
             (eqv? (rktio_poll_write_ready rktio (fd-evt-fd fde))
                   RKTIO_POLL_READY))))
     (cond
       [ready?
        (end-atomic)
        (values (list fde) #f)]
       [else
        ;; If `sched-info` is not #f, then we can register this file
        ;; descriptor so that if no thread is able to make progress,
        ;; the Racket process will sleep, but it will wake up when
        ;; input is available. The implementation of external events
        ;; is from the current sandman, which will in turn be the
        ;; one (or build on the one) in "../sandman".
        (define sched-info (poll-ctx-sched-info ctx))
        (when sched-info
          (schedule-info-current-exts sched-info
                                      (sandman-add-poll-set-adder
                                       (schedule-info-current-exts sched-info)
                                       ;; Cooperate with the sandman by registering
                                       ;; a funciton that takes a poll set and
                                       ;; adds to it:
                                       (lambda (ps)
                                         (rktio_poll_add rktio (fd-evt-fd fde) ps mode)))))
        (end-atomic)
        (values #f fde)]))))

;; ----------------------------------------

(define (register-fd-close custodian host-fd port)
  (define closed (core-port-closed port))
  (unsafe-custodian-register custodian
                             host-fd
                             ;; in atomic mode
                             (lambda (host-fd)
                               (host-close host-fd)
                               (set-closed-state! closed))
                             #f
                             #f))