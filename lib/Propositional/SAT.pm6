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
    my @DIMACS = gather for $clauses.grep(not *.tautology) {
        my @vars = .vars.keys.map({ +$lookup.get-int($_) });
        my @nars = .nars.keys.map({ -$lookup.get-int($_) });

        take sort(&abs, flat @vars, @nars).join(" ") ~ " 0";

        # Behold the max=max operator
        $num-vars max=max (@vars, @nars).flat».abs;
        $num-clauses++;
    }

    gather {
        take "p cnf $num-vars { $num-clauses max 1 }";
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
    gather for $assignments {
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

multi sub sat ($clauses, |c) is export {
    sat-solve DIMACSify($clauses), |c
}

multi sub count-sat ($clauses, |c) is export {
    sat-count DIMACSify($clauses), |c
}

multi sub all-sat ($clauses, |c) is export {
    my $lookup = Propositional::Variable::Cache.new;
    sat-enumerate(DIMACSify($clauses, :$lookup), |c)\
        .map: &UNDIMACSify.assuming(:$lookup)
}
