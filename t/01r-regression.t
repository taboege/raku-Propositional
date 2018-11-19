use Test;

use Propositional;
use Propositional::AST;

class Var does Variable {
    has $.name;

    multi method new (Pair:D $p) {
        self.new: :name($p.key)
    }

    method Str  { $!name }
    method gist { $!name }
}

multi prefix:<`> (Pair $p) {
    state %VARS;
    %VARS{$p.key} //= Var.new($p)
}

plan 2;

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
