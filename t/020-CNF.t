use Test;
use Test::Propositional;

use Propositional;
use Propositional::AST;
use Propositional::CNF;

plan 2;

sub eqv-clauses (Propositional::CNF() \φ, @clauses) {
    cmp-ok Set(φ.clauses), 'eqv', Set(@clauses), "clauses of {φ}";
}

subtest "syntax" => {
    constant CNF = Propositional::CNF;

    plan 4;
    eqv-clauses `:p ⇒ `:q, [
        CNF::Clause.new(
            vars => set(`:q),
            nars => set(`:p),
        ),
    ];
    eqv-clauses `:p ⇔ `:q, [
        CNF::Clause.new(
            vars => set(`:q),
            nars => set(`:p),
        ),
        CNF::Clause.new(
            vars => set(`:p),
            nars => set(`:q),
        ),
    ];
    eqv-clauses `:p ∧ (`:q ∨ `:r), [
        CNF::Clause.new(
            vars => set(`:p),
        ),
        CNF::Clause.new(
            vars => set(`:q, `:r),
        ),
    ];
    eqv-clauses `:p ∨ (`:q ∧ `:r), [
        CNF::Clause.new(
            vars => set(`:p, `:q),
        ),
        CNF::Clause.new(
            vars => set(`:p, `:r),
        ),
    ];
}

subtest "semantics" => {
    plan 4;

    for `:p ⇒ `:q, `:p ⇔ `:q, `:p ∧ (`:q ∨ `:r), `:p ∨ (`:q ∧ `:r) {
        subtest .Str => {
            plan 2;
            my $cnf = .'Propositional::CNF'();
            isa-ok $cnf, Propositional::CNF, 'CNF type';
            is-eqv .self, $cnf;
        }
    }
}
