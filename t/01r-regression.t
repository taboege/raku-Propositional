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

plan 1;

# 6bec259b: squish would cause chained ¬ to be squished which
# isn't sensible and didn't match eval's implementation.
is (¬¬`:p), '(¬ (¬ p))', 'no regression on squish bug for unaries';
