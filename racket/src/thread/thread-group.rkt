#lang racket/base
(require "engine.rkt"
         "check.rkt"
         "internal-error.rkt"
         "atomic.rkt")

(provide (struct-out node)
         
         thread-group?
         make-thread-group
         current-thread-group

         ;; Used by scheduler
         root-thread-group
         thread-group-next!
         
         ;; Called by thread creation and termination:
         thread-group-add!
         thread-group-remove!
         
         thread-group-all-threads
         num-threads-in-groups)

;; Threads and thread groups subtype `node`:
(struct node ([prev #:mutable]
              [next #:mutable]))
(define (child-node child) child) ; a child instantiates a `node` subtype
(define (node-child n) n)

(struct thread-group node (parent
                           [chain-start #:mutable] ; all children
                           [chain #:mutable] ; children remaining to be scheduled round-robin
                           [chain-end #:mutable]))

(define root-thread-group (thread-group #f #f #f #f #f #f))

(define num-threads-in-groups 0)

(define/who current-thread-group
  (make-parameter root-thread-group
                  (lambda (v)
                    (check who thread-group? v)
                    v)))

(define/who (make-thread-group [parent (current-thread-group)])
  (check who thread-group? parent)
  (define tg (thread-group #f #f parent #f #f #f))
  tg)

;; Called atomically in scheduler:
(define (thread-group-next! tg)
  (define n (thread-group-chain tg))
  (cond
   [(not n)
    (define n (thread-group-chain-start tg))
    (cond
     [(not n)
      ;; No children
      #f]
     [else
      (set-thread-group-chain! tg (node-next n))
      n])]
   [else
    (set-thread-group-chain! tg (node-next n))
    (node-child n)]))

(define (thread-group-add! parent child)
  (atomically
   (let loop ([parent parent] [child child])
     (define t (thread-group-chain-end parent))
     (define was-empty? (not t))
     (define n (child-node child))
     (set-node-prev! n t)
     (set-node-next! n #f)
     (if t
         (set-node-next! t n)
         (set-thread-group-chain-start! parent n))
     (set-thread-group-chain-end! parent n)
     (unless (thread-group? child)
       (set! num-threads-in-groups (add1 num-threads-in-groups)))
     (when was-empty?
       ;; added child to formerly empty parent => add the parent
       (define parent-parent (thread-group-parent parent))
       (when parent-parent
         (loop parent-parent parent))))))

(define (thread-group-remove! parent child)
  (atomically
   (let loop ([parent parent] [child child])
     (define n (child-node child))
     (if (node-next n)
         (set-node-prev! (node-next n) (node-prev n))
         (set-thread-group-chain-end! parent (node-prev n)))
     (if (node-prev n)
         (set-node-next! (node-prev n) (node-next n))
         (set-thread-group-chain-start! parent (node-next n)))
     (when (eq? n (thread-group-chain parent))
       (set-thread-group-chain! parent (node-next n)))
     (unless (thread-group? child)
       (set! num-threads-in-groups (sub1 num-threads-in-groups)))
     (when (not (thread-group-chain-end parent))
       ;; parent thread group is now empty, so remove it, too
       (define parent-parent (thread-group-parent parent))
       (when parent-parent
         (loop parent-parent parent))))))

(define (thread-group-all-threads parent accum)
  (cond
   [(not (thread-group? parent)) (cons parent accum)]
   [else
    (let loop ([n (thread-group-chain-start parent)] [accum accum])
      (cond
       [(not n) accum]
       [else (loop (node-next n)
                   (thread-group-all-threads (node-child n) accum))]))]))

