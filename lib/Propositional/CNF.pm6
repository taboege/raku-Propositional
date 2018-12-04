use Propositional;

#|« This class provides a dedicated type for CNF formulas. It is represented
exactly like a squished AST formula after calling its C<CNF> method, but
unlike an AST, a CNF object is immutable.
»
unit class Propositional::CNF does Propositional::Formula;

# A clause is two sets of variables which together form the set
# of literals in the clause: the (non-negated) variables vars
# and the negated variables nars.
our class Clause {
    has Set $.vars .= new;
    has Set $.nars .= new;
    has $.tautology;

    submethod TWEAK {
        $!tautology = so $!vars ∩ $!nars;
    }

    # timotimo++ https://colabti.org/irclogger/irclogger_log/perl6?date=2018-12-04#l49
    method WHICH {
        ValueObjAt.new("Propositional::CNF::Clause|$!vars.WHICH()|$!nars.WHICH()")
    }

    method eval (Set \α) {
        [or] |$!vars.keys».eval(α), |not« $!nars.keys».eval(α)
    }

    method Str {
        my @literals = [
            |$!vars.keys».Str,
            |$!nars.keys».Str.map({ "(¬ $_)" })
        ];
        "(∨ " ~ @literals.join(" ") ~ ")"
    }
}

has Clause @.clauses;
has Set $!variables; # cache

submethod BUILD (:@clauses) {
    # Tautology testing for a disjunction of literals can be done
    # syntactically in linear time: it is a tautology if and only if
    # vars and nars intersect.
    #
    # We ignore these clauses upfront because there is no way to
    # convert them to DIMACS. It also saves space.
    @!clauses = @clauses.grep: { not .tautology }
}

method variables {
    $!variables //= [∪] flat @!clauses.map({ .vars, .nars })
}

# Since we don't store tautology clauses, the only way for the
# CNF to be a tautology is to not have any clauses. I hope this
# isn't inconsistent with customary assumption about the empty
# formula...

method eval (Set \α) {
    return True unless @!clauses;
    [and] @!clauses».eval: α
}

multi method tautology {
    not @!clauses
}

method Str { "(∧ " ~ @!clauses».Str.join(" ") ~ ")" }

# TODO: operators...?
