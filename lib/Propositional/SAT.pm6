use Propositional;
use Propositional::CNF;

use SAT;
# TODO: Allow different SAT:: solver modules to be configured.
# TODO: SAT::Solver::Lingeling to get witnesses.
use SAT::Solver::MiniSAT;
use SAT::Counter::DSHARP;
use SAT::Enumerator::Toda;

unit module Propositional::SAT;

#|« Convert a stream of Propositional::CNF::Clause objects into DIMACS cnf.

DIMACS cnf is the input format of SAT solvers. This plaintext, line-oriented
format requires variables to be encoded by unique integers in a contiguous
range starting at 1. This conversion is performed by the C<Propositional::Varible::Lookup>
structure passed in C<$lookup>, which defaults to a C<Propositional::Variable::Cache>.

You may want to pass a custom C<$lookup> in roughly one of two cases:

=begin item
Your variables permit a more efficient implementation of lookups than
caching. Refer to L<Propositional::Variable::Lookup> for how to implement
your own lookup.
=end item

=begin item
SAT and #SAT problems only require a conversion of the formula to DIMACS
to feed to the solver, so the default throw-away C<$lookup> argument is
sufficient. However, an AllSAT problem produces DIMACS-alike output:
the list of satisfying assignments are encoded using the same variable
numbers that were used in the input. Hence the same lookup (cache) is
again needed at the output of the solver. In this case, you have to
create your own lookup structure and pass it to DIMACSify, to not lose
access to it.
=end item
»
sub DIMACSify ($clauses, :$lookup = Propositional::Variable::Cache.new) is export {
    # A clause is represented in DIMACS cnf as a single line which lists all
    # literals appearing in it. A variable literal is its corresponding
    # integer and a negated literal is the (additively) negated integer.
    # The literals have to appear space-separated in increasing order of
    # magnitude and the lines ends in the special "0" literal.
    #
    # TODO: We have to cache the clauses because DIMACS needs the total
    # number of variables and clauses *in the header*. There should be an
    # option for the caller to provide these OR a patch to all SAT solvers
    # to take what they get. I think this header is an artifact of the
    # DIMACS cnf format being a competition format.
    my ($num-vars, $num-clauses) = 0 xx *;
    my @DIMACS = gather for |$clauses {
        my @vars = .vars.keys.map({ +$lookup.get-int($_) });
        my @nars = .nars.keys.map({ -$lookup.get-int($_) });

        # Behold the max=max operator
        $num-vars max=max (@vars, @nars).flat».abs;

        next if .tautology; # no way to format tautological clauses
        take sort(&abs, flat @vars, @nars).join(" ") ~ " 0";
        $num-clauses++;
    }

    gather {
        take "p cnf $num-vars $num-clauses";
        take $_ for @DIMACS;
    }
}

#|« Convert an array of Bools into an assignment.

This routine is the converse to DIMACSify. It takes the output of an
AllSAT solver, in the form of arrays of Bools, and turns them into
Sets of variables, representing the satisfying assignments.

See DIMACSify for details about the C<$lookup> structure.
»
sub UNDIMACSify ($assignments, :$lookup!) {
    gather for |$assignments {
        my @vars = 1 «+« .grep(*.so, :k);
        take @vars.map({ $lookup.get-var($_) }).Set;
    }
}

multi sub sat (Propositional::CNF(Propositional::Formula) \φ, |c) is export {
    sat φ.clauses, |c
}

multi sub count-sat (Propositional::CNF(Propositional::Formula) \φ, |c) is export {
    count-sat φ.clauses, |c
}

multi sub all-sat (Propositional::CNF(Propositional::Formula) \φ, |c) is export {
    all-sat φ.clauses, |c
}

# Tautological clauses cannot be converted to DIMACS. The empty formula
# (one clause consisting only of the end marker "0") is not interpreted
# as a tautology by every solver, so we catch this ourselves.
#
# Luckily, it is tractable. Since it is assumed that sat, count-sat and
# all-sat pass extraneous parameters like :now to the SAT module, we have
# to at least do their basic roles.

package Tautology {
    # FIXME: Would like to turn these into roles parameterized with the
    # $num-vars, but then SAT::Solver etc. role detection in the SAT
    # module breaks. Bug filed: R#2551.

    class Solver does SAT::Solver {
        has $.num-vars;
        multi method new (Solver:D: *% ()) { self.new(:$!num-vars) }

        multi method solve (Supply $lines, $witness is rw, *% () --> Promise) {
            $witness = Array[Bool];
            my $p = Promise.new;
            $p.keep(True); # or `so $!num-vars`?
            $p
        }
    }

    class Counter does SAT::Counter {
        has $.num-vars;
        multi method new (Counter:D: *% ()) { self.new(:$!num-vars) }

        multi method count (Supply $lines, *% () --> Promise) {
            my $p = Promise.new;
            $p.keep(2 ** $!num-vars); # or 0 if $!num-vars == 0?
            $p
        }
    }

    class Enumerator does SAT::Enumerator {
        has $.num-vars;
        multi method new (Enumerator:D: *% ()) { self.new(:$!num-vars) }

        multi method enumerate (Supply $lines, *% () --> Supply) {
            supply {
                emit $_ for cross [True, False] xx $!num-vars;
            }
        }
    }
}

# A tautology is identified by its DIMACS problem line having zero clauses.
# TODO: I would like to avoid the array here, but binding the Seq returned
# by DIMACSify errors with "iterator already in use".

my regex DIMACS-tautology { :s ^p cnf $<num-vars>=[\d+] 0$ }

multi sub sat ($clauses, |c) is export {
    my @lines = DIMACSify($clauses);
    my $*SAT-SOLVER = Tautology::Solver.new(num-vars => +$<num-vars>)
        if @lines.head ~~ &DIMACS-tautology;
    sat-solve @lines, |c
}

multi sub count-sat ($clauses, |c) is export {
    my @lines = DIMACSify($clauses);
    my $*SAT-COUNTER = Tautology::Counter.new(num-vars => +$<num-vars>)
        if @lines.head ~~ &DIMACS-tautology;
    sat-count @lines, |c
}

multi sub all-sat ($clauses, |c) is export {
    my $lookup = Propositional::Variable::Cache.new;
    my @lines = DIMACSify($clauses, :$lookup);
    my $*SAT-ENUMERATOR = Tautology::Enumerator.new(num-vars => +$<num-vars>)
        if @lines.head ~~ &DIMACS-tautology;
    UNDIMACSify(sat-enumerate(@lines, |c), :$lookup)
}
