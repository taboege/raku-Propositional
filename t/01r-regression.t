use Test;
use Test::Propositional;

use Propositional;
use Propositional::AST;

plan 3;

# 6bec259b: squish would cause chained non-binary operators like ¬ to be
# squished which isn't sensible and didn't match eval's implementation.
is (¬¬`:p), '(¬ (¬ p))', 'no regression on squishing unaries';

# a0445d9a: squish would stop recursing on non-binary operators,
# such as ¬.
my \φ = Propositional::AST::Operator::Not.new(operands => (
    Propositional::AST::Operator::And.new(operands => (
        `:p,
        Propositional::AST::Operator::And.new(operands => (
            `:q, `:r
        )),
    )),
));
is φ.squish, '(¬ (∧ p q r))', 'no regression on unary blocking squish';

# a92ab567: rewrite would sometimes not rewrite enough when pattern
# matching failed due to replacements producing non-spread formulas,
# which couldn't be matched by the always-spread patterns.
subtest 'no regression with too few rewrites' => {
    plan 8;

    # Forcing more rewrites (which calls spread once at the beginning)
    # continued the process, so this showed the bug:
    is ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q).NNF,
       ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q).NNF.NNF;
    is ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q).CNF,
       ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q).CNF.CNF;
    is ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q).DNF,
       ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q).DNF.DNF;

    # Check normal form patterns for good measure.
    ok-NNF ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q);
    ok-CNF ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q);
    ok-DNF ((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q);

    # f1c1c48c: it was still possible to create non-spread formulas
    # by replacements.
    is (¬`:p).rewrite((¬^:p) => { sink $:p; `:p ∧ `:q ∧ `:r }),
       (`:p ∧ `:q ∧ `:r).spread,
       'replacement is spread itself';

    is (`:p ∧ `:q ∧ `:r ∧ (`:s ∨ `:t)).rewrite(
            (^:x(quietly *.?name eq 's') ∨ ^:y(quietly *.?name eq 't')) => { $:x ∧ $:y }
    ), (`:p ∧ `:q ∧ `:r ∧ `:s ∧ `:t).spread,
    'rewritten formula is spread';
}
