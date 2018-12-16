use Propositional;

#|« This class provides a dedicated type for CNF formulas.

It is represented exactly like a squished AST formula after calling
its C<CNF> method, but unlike an AST, a CNF object is immutable.
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

# We store even tautological clauses because we want to be able to store
# tautologies. They cannot be converted to DIMACS but their SAT problems
# can still be answered easily. By not storing tautological clauses, we
# would conflate the empty formula with every tautology, but they have
# different properties like the number of satisfying assignments, which
# depend on information that would be lost if we didn't store these clauses.
has Clause @.clauses;
has Set $!variables; # cache

method variables {
    $!variables //= [∪] flat @!clauses.map({ .vars, .nars })
}

method eval (Set \α) {
    [and] @!clauses».eval: α
}

multi method tautology {
    none(@!clauses).tautology
}

method Str { "(∧ " ~ @!clauses».Str.join(" ") ~ ")" }

# TODO: operators...?
