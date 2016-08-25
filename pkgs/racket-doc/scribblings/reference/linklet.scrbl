#lang scribble/doc
@(require "mz.rkt"
          (for-label racket/linklet))

@title[#:tag "linklets"]{Linklets and the Core Compiler}

@defmodule[racket/linklet]

A @deftech{linklet} is a primitive element of compilation, bytecode
marshaling, and evaluation. Racket's implementations of modules,
macros, and top-level evaluation are all built on linklets. Racket
programmers generally do not encounter linklets directly, but the
@racketmodname[racket/linklet] library provides access to linklet
facilities.

A single Racket module (or collection of top-level forms) is typically
implemented by multiple linklets. For example, each phase of
evaluation that exists in a module is implemented in a separate
linklet. A linklet is also used for metadata such as the @tech{module
path index}es for a module's @racket[require]s. These linklets, plus
some other metadata, are combined to form a @deftech{linklet bundle}.
Information in a @tech{linklet bundle} is keyed by either a symbol or
a @tech{fixnum}. A @tech{linklet directory} contiaining
@tech{linklet}s can be marshaled to and from a byte stream by
@racket[write] and (with @racket[read-accept-compiled] is enabled)
@racket[read].

When a Racket module has submodules, the @tech{linklet bundles} for
the module and the submodules are grouped together in a
@deftech{linklet directory}. A @tech{linklet directory} can have
nested linklet directories. Information in a linklet directory is
keyed by @racket[#f] or a symbol, where @racket[#f] must be mapped to
a @tech{linklet bundle} (if anything) and each symbol must be mapped
to a @tech{linklet directory}. A @tech{linklet directory} can be
equivalently viewed as a mapping from a lists of symbols to a
@tech{linklet bundle}. Like @tech{linklet bundles}, a @tech{linklet
directory} can be marshaled to and from a byte stream by
@racket[write] and @racket[read]; the marshaled form allows individual
@tech{linklet bundles} to be loaded independently.

A linklet consists of a set of variable definitions and expressions,
an exported subset of the defined variable names, a set of variables to export
from the linklet despite having no corresponding definition, and a set
of imports that provide other variables for the linklet to use. To run
a linklet, it is instantiated as as @deftech{linklet instance} (or
just @defterm{instance}, for short). When a linklet is instantiated,
it receives other @tech{linklet instances} for its imports, and it
extracts a specified set of variables that are exported from each of
the given instances. The newly created @tech{linklet instance}
provides its exported variables for use by other linklets or for
direct access via @racket[instance-variable-value]. A @tech{linklet
instance} can be synthesized directly with @racket[make-instance].

A linklet is created by compiling an enriched S-expression
representation of its source. Since linklets exist below the layer of
macros and syntax objects, linklet compilation does not use
@tech{syntax objects}. Instead, linklet compilation uses
@deftech{correlated objects}, which are like @tech{syntax objects}
without lexical-context information. Using an S-expression or
@tech{correlated object}, the grammar of a linklet as recognized by
@racket[compile-linklet] is

@specform[(linklet [[imported-id/renamed ...] ...]
                   [exported-id/renamed ...]
            defn-or-expr ...)
          #:grammar
          ([imported-id/renamed imported-id
                                (external-imported-id internal-imported-id)]
           [exported-id/renamed exported-id
                                (internal-exported-id external-exported-id)])]

Each import set @racket[[_imported-id/renamed ...]] refers to a single
imported instance, and each @racket[_import-id/renamed] corresponds to
a variable from that instance. If separate
@racket[_external-imported-id] and @racket[_internal-imported-id] are
specified, then @racket[_external-imported-id] is the name of the
variable as exported by the instance, and
@racket[_internal-imported-id] is the name used to refer to the
variable in the @racket[_defn-or-expr]s. For exports, separate
@racket[_internal-exported-id] and @racket[_external-exported-id]
names corresponds to the variable name as exported as referenced 
in the @racket[_defn-or-expr]s, respectively.

The grammar of an @racket[_defn-or-expr] is similar to the expander's
grammar of fully expanded expressions (see @secref["fully-expanded"])
with some exceptions: @racket[quote-syntax] and @racket[#%top] are not allowed;
@racket[#%plain-lambda] is spelled @racket[lambda];
@racket[#%plain-app] is omitted (i.e., application is implicit);
@racket[lambda], @racket[case-lambda], @racket[let-values], and
@racket[letrec-values] can have only a single body expression; and
numbers, booleans, strings, and byte strings are self-quoting.
Primitives are accessed directly by name, and shadowing is not allowed
within a @racketidfont{linklet} form for primitive names, imported
variables, defined variables, or local variables.

When a @racket[_exported-id/renamed] has no corresponding definition
among the @racket[_defn-or-expr]s, then the variable is effectively
defined as uninitialized; referencing the variable will trigger
@racket[exn:fail:contract:variable], the same as referencing a
variable before it is defined. When a target instance is provided to
@racket[instantiate-linklet], any existing variable with the same name
will be left as-is, instead of set to undefined. This treatment of
uninitialized variables provides core support for top-level evaluation
where variables may be referenced and then defined in a separate
element of compilation.

@history[#:added "6.6.1"]

@; --------------------------------------------------

@defproc[(linklet? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{linklet}, @racket[#f]
otherwise.}


@defproc*[([(compile-linklet [form (or/c correlated? any/c)]
                             [name any/c #f]
                             [import-keys #f #f]
                             [get-import #f #f])
            linklet?]
           [(compile-linklet [form (or/c correlated? any/c)]
                             [name any/c]
                             [import-keys vector?]
                             [get-import (or/c #f (any/c . -> . (values (or/c linklet? #f)
                                                                        (or/c vector? #f))))
                                         #f])
           (values linklet? vector?)])]{

Takes an S-expression or @tech{correlated object} for a
@schemeidfont{linklet} form and produces a @tech{linklet}. The
resulting linklet can be marshaled to and from a byte stream when it is
part of a @tech{linklet bundle}.

The optional @racket[name] is associated to the linklet for debugging
purposes and as the default name of the linklet's instance.

The optional @racket[import-keys] and @racket[get-import] arguments
support cross-linklet optimization. If @racket[import-keys] is a
vector, it must have as many elements as sets of imports in
@racket[form]. If the compiler becomes interested in optimizing a
reference to an imported variable, it passes back to
@racket[get-import] (if non-@racket[#f]) the element of @racket[import-keys] that
corresponds to the variable's import set. The @racket[get-import]
function can then return a linklet that represents an instance to be
provided to the compiled linklet when it is eventually instantiated;
ensuring consistency between reported linklet and the eventual
instance is up to the caller of @racket[compile-linklet]. If
@racket[get-import] returns @racket[#f] as its first value, the
compiler will be prevented from make any assumptions about the
imported instance. The second result from @racket[get-import] is an
optional vector of keys to provide transitive information on a
returned linklet's imports; the returned vector must have the same
number of elements as the linklet has imports. When vector elements
are @racket[eq?] and non-@racket[#f], the compiler can assume that
they correspond to the same run-time instance. A @racket[#f]
value for @racket[get-import] is equivalent to a function that
always returns two @racket[#f] results.

When @racket[import-keys] is not @racket[#f], then the compiler is
allowed to grow or shrink the set of imported instances for the
linklet. The result vector specifies the keys of the imports for the
returned linklet.}


@defproc*[([(recompile-linklet [linklet linklet?]
                               [name any/c #f]
                               [import-keys #f #f]
                               [get-import (any/c . -> . (values (or/c linklet? #f)
                                                                 (or/c vector? #f)))
                                           (lambda (import-key) (values #f #f))])
            linklet?]
           [(recompile-linklet [linklet linklet?]
                               [name any/c]
                               [import-keys vector?]
                               [get-import (any/c . -> . (values (or/c linklet? #f)
                                                                 (or/c vector? #f)))
                                           (lambda (import-key) (values #f #f))])
             (values linklet? vector?)])]{

Like @racket[compile-linklet], but takes an already-compiled linklet
and potentially optimizes it further.}


@defproc[(eval-linklet [linklet linklet?]) linklet?]{

Returns a variant of a @racket[linklet] that is prepared for JIT
compilation such that every later use of the result linklet with
@racket[instantiate-linklet] shares the JIT-generated code. However,
the result of @racket[eval-linklet] cannot be marshaled to a byte
stream as part of a @tech{linklet bundle}, and it cannot be used with
@racket[recompile-linklet].}



@defproc*[([(instantiate-linklet [linklet linklet?]
                                 [import-instances (listof instance?)]
                                 [target-instance? #f #f]
                                 [use-prompt? any/c #t])
            instance?]
           [(instantiate-linklet [linklet linklet?]
                                 [import-instances (listof instance?)]
                                 [target-instance instance?]
                                 [use-prompt? any/c #t])
            any])]{

Instantiates @racket[linklet] by running its definitions and
expressions, using the given @racket[import-instances] for its
imports. The number of instances in @racket[import-instances] must
match the number of import sets in @racket[linklet].

If @racket[target-instance] is @racket[#f] or not provided, the result
is a fresh instance for the linklet. If @racket[target-instance] is an
instance, then the instance is used and modified for the linklet
definitions and expressions, and the result is the value of the last
expression in the linklet.

The linklet's exported variables are accessible in the result instance
or in @racket[target-instance] using the linklet's external name for
each export. If @racket[target-instance] is provided as
non-@racket[#f], its existing variables remain intact if they are not
modified by a linklet definition.

If @racket[use-prompt?] is true, then the evaluation each definition
and expression in the linklet is wrapped in a @tech{prompt} in the
same ways as an expression in a module body.}


@defproc[(linklet-import-variables [linklet linklet?])
         (listof (listof symbol?))]{

Returns a description of a linklet's imports. Each element of the
result list corresponds to an import set as satisfied by a single
instance on instantiation, and each member of the set is a variable
name that is used from the corresponding imported instance.}

@defproc[(linklet-export-variables [linklet linklet?])
         (listof symbol?)]{

Returns a description of a linklet's exports. Each element of the list
corresponds to a variable that is made available by the linklet in its
instance.}


@defproc[(linklet-directory? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{linklet directory},
@racket[#f] otherwise.}


@defproc[(hash->linklet-directory [content (and/c hash? hash-eq? immutable? (not/c impersonator?))])
         linklet-directory?]{

Constructs a @tech{linklet directory} given mappings in the form of a
@tech{hash table}. Each key of @racket[content] must be either a
symbol or @racket[#f], each symbol must be mapped to a @tech{linklet
directory}, and @racket[#f] must be mapped to a @tech{linklet bundle}
or not mapped.}


@defproc[(linklet-directory->hash [linklet-directory linklet-directory?])
         (and/c hash? hash-eq? immutable? (not/c impersonator?))]{

Extracts the content of a @tech{linklet directory} into a @tech{hash
table}.}

         
@defproc[(linklet-bundle? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{linklet bundle},
@racket[#f] otherwise.}


@defproc[(hash->linklet-bundle [content (and/c hash? hash-eq? immutable? (not/c impersonator?))])
         linklet-bundle?]{

Constructs a @tech{linklet bundle} given mappings in the form of a
@tech{hash table}. Each key of @racket[content] must be either a
symbol or a @tech{fixnum}. Values in the hash table are unconstrained,
but the intent is that they are all @tech{linklets} or values that can
be recovered from @racket[write] output by @racket[read].}


@defproc[(linklet-bundle->hash [linklet-bundle linklet-bundle?])
         (and/c hash? hash-eq? immutable? (not/c impersonator?))]{

Extracts the content of a @tech{linklet bundle} into a @tech{hash
table}.}
         

@defproc[(instance? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a @tech{linklet instance},
@racket[#f] otherwise.}


@defproc[(make-instance [name any/c]
                        [data any/c #f]
                        [variable-name symbol?]
                        [variable-value any/c] ... ...)
         instance?]{

Constructs a @tech{linklet instance} directly. Besides associating an
arbitrary @racket[name] and @racket[data] value to the instance, the
instance is populated with variables as specified by
@racket[variable-name] and @racket[variable-value].}

@defproc[(instance-name [instance instance?]) any/c]{

Returns the value associated to @racket[instance] as its name---either
the first value provided to @racket[make-instance] or the name of a
linklet that was instantiated to create the instance.}


@defproc[(instance-data [instance instance?]) any/c]{

Returns the value associated to @racket[instance] as its data---either
the second value provided to @racket[make-instance] or the default
@racket[#f].}


@defproc[(instance-variable-names [instance instance?]) (list symbol?)]{

Returns a list of all names for all variables accessible from
@racket[instance].}


@defproc[(instance-variable-value [instance instance?]
                                  [name symbol?]
                                  [fail-k any/c (lambda () (error ....))])
         any]{

Returns the value of the variable exported as @racket[name] from
@racket[instance]. If no such variable is exported, then
@racket[fail-k] is used in the same way as by @racket[hash-ref].}


@defproc[(instance-set-variable-value! [instance instance?]
                                       [name symbol?]
                                       [v any/c]
                                       [constant? any/c #f])
          void?]{

Sets or creates the variable exported as @racket[name] in
@racket[instance] so that its value is @racket[v], as long as the
variable does not exist already as constant. If a variable for
@racket[name] exists as constant, the @exnraise[exn:fail:contract].

If @racket[constant?] is true, then the variable is creates or changed
to be constant.}

@defproc[(instance-unset-variable! [instance instance?]
                                   [name symbol?])
          void?]{

Changes @racket[instance] so taht it does not export a variable as
@racket[name], as long as @racket[name] does not exist as a constant
variable. If a variable for @racket[name] exists as constant, the
@exnraise[exn:fail:contract].}


@defproc[(variable-reference->instance [varref variable-reference?])
         instance?]{

Extracts the instance where @racket[varref] resides. This notion of
@tech{variable reference} is the same as at the module level and can
reflect the linklet instance that implements a particular phase of a
module instance.}

@deftogether[(
@defproc[(correlated? [v any/c]) boolean?]
@defproc[(correlated-source [stx correlated?]) any]
@defproc[(correlated-line [stx correlated?])
         (or/c exact-positive-integer? #f)]
@defproc[(correlated-column [stx correlated?])
         (or/c exact-nonnegative-integer? #f)]
@defproc[(correlated-position [stx correlated?])
         (or/c exact-positive-integer? #f)]
@defproc[(correlated-span [stx correlated?])
         (or/c exact-nonnegative-integer? #f)]
@defproc[(correlated-e [stx correlated?]) any]
@defproc[(correlated->datum [stx correlated?]) any]
@defproc[(datum->correlated [v any/c]
                        [srcloc (or/c correlated? #f
                                      (list/c any/c
                                              (or/c exact-positive-integer? #f)
                                              (or/c exact-nonnegative-integer? #f)
                                              (or/c exact-positive-integer? #f)
                                              (or/c exact-nonnegative-integer? #f))
                                      (vector/c any/c
                                               (or/c exact-positive-integer? #f)
                                               (or/c exact-nonnegative-integer? #f)
                                               (or/c exact-positive-integer? #f)
                                               (or/c exact-nonnegative-integer? #f)))
                                #f])
          correlated?]
@defproc*[([(correlated-property [stx correlated?]
                             [key (if preserved? (and/c symbol? symbol-interned?) any/c)])
             correlated?]
           [(correlated-property [stx correlated?] [key any/c]) any/c])]
@defproc[(correlated-property-symbol-keys [stx correlated?]) list?]
)]{

Like @racket[syntax?], @racket[syntax-source], @racket[syntax-line],
@racket[syntax-column], @racket[syntax-position],
@racket[syntax-span], @racket[syntax-e], @racket[syntax->datum],
@racket[datum->syntax], @racket[syntax-property], and
@racket[syntax-property-symbol-keys], but for @tech{correlated
objects}.}
