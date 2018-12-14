use Propositional;
use Propositional::CNF;

use SAT;

# TODO: Allow different SAT:: solver modules to be configured.

unit module Propositional::SAT;

role Job does Callable {
    method CALL-ME ($clauses) { … }
}

class Job::Solver does Job {
    has $.args;

    method CALL-ME ($DIMACS) {
        sat-solve $DIMACS, |$!args
    }
}

class Job::Counter does Job {
    has $.args;

    method CALL-ME ($DIMACS) {
        sat-solve $DIMACS, |$!args
    }
}

class Job::Enumerator does Job {
    has $.args;

    method CALL-ME ($DIMACS) {
        sat-solve $DIMACS, |$!args
    }
}

#|« Wrap a SAT::Job (usually a raw solver) with a DIMACS cnf encoding layer.
The DIMACS format requires variables to be encoded by unique integers in a
contiguous range starting at 1. Much of the difficulty comes from having to
encode our high-level formulas into this format so that SAT, #SAT and AllSAT
problems can be solved correctly.

If the C<$lookup> argument is given and of type C<Propositional::Lookup>,
then it is supposed to be the type of variables in the formula eventually
sent to the job. The lookup interface is used to obtain the variable to
number encoding.

Otherwise the layer maintains a cache where each new variable is inserted
to get its unique number. This method may be slower and more memory-heavy,
but you don't have to worry about ordering your variables yourself.
Unlike the C<Propositional::Lookup> interface, this method ensures that
the number of variables reported to the solver is the true number of variables
occuring in the formula, not the total number of variables allocated by the
variable lookup type. This can make a difference for #SAT and AllSAT responses.

For SAT and #SAT problems, encoding of the formula into DIMACS is enough.
If the job being wrapped is an AllSAT instance, this wrapper also installs
an output filter which turns the Bools in truth assignments back into the
corresponding variable object, using the same lookup object or cache.
»
sub DIMACSify (Job $job, :$lookup? --> Job) is export {
    $lookup ~~ Propositional::Lookup ??
        DIMACSify'lookup $job, $lookup !!
        DIMACSify'cached $job
}

sub DIMACSify'lookup ($job, $lookup --> Job) {
    
}

sub DIMACSify'cached ($clauses --> Job) {
    
}

# alternatively: add the option to return the cache...
# then encoding and decoding can be decoupled and have to be
# passed the same cache.
#
# DIMACSify'cached also has the problem (that's a general problem
# surfacing at DIMACSify) that the number of variables and clauses
# is unknown at encoding time. even DIMACSify'lookup can't guess
# the number of clauses, but that information must precede the
# payload that we encode. so it should be provided at the very
# beginning, when creating the job?

#|« Wrap a SAT::Job with an object decoder. All satisfying assignments,
as sets of variables (cf. DIMACSify) are turned into objects of the
given C<$type>, by calling $type.from-assignment.
»
sub TYPEify ($job, $type --> Job) {
    ;
}

multi sub satisfiable (Propositional::CNF(Propositional::Formula) \φ --> Promise) is export {
    satisfiable φ.clauses
}

multi sub count-satisfiables (Propositional::CNF(Propositional::Formula) \φ --> Promise) is export {
    count-satisfiables φ.clauses
}

multi sub all-satisfiables (Propositional::CNF(Propositional::Formula) \φ --> Supply) is export {
    all-satisfiables φ.clauses
}

multi sub satisfiable ($clauses, |c --> Job::Solver) is export {
    
}

multi sub count-satisfiables ($clauses --> Job::Counter) is export {
    
}

multi sub all-satisfiables ($clauses --> Job::Enumerator) is export {
    
}
