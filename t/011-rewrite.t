use Test;

use Propositional;
use Propositional::AST;

class Var does Propositional::AST::Variable {
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

plan 10;

is `:p, `:p, 'variable caching works';

is (¬(¬`:p ∧ `:q)).rewrite((^:p ∧ `:q) => { $:p }),
    "(¬ (¬ p))",
    "rewrite does not swallow operators";

is (¬¬¬`:p).rewrite((¬¬^:p) => { ¬$:p }),
    "(¬ p)",
    "performs multiple rewrites";

is (¬¬`:p).rewrite((¬¬^:p) => { $:p }, :1ce),
    "p",
    "operator can produce variable";

subtest 'matcher' => {
    plan 4;

    is (¬¬`:p).rewrite((¬^:p) => { $:p ∧ $:p }),
    "(∧ (∧ p p) (∧ p p))",
    "default matcher is True";

    is (¬¬`:p).rewrite((¬^:p(Propositional::Variable)) => { $:p ∧ $:p }),
    "(¬ (∧ p p))",
    "variable matcher restricts correctly";

    is (`:a ∧ `:m ∧ `:n ∧ `:z).rewrite(:1ce, (^:p(subset :: of Var where *.name.ord ≤ 109)) => { ¬$:p }).squish,
    "(∧ (¬ a) (¬ m) n z)",
    "non-trivial subset matcher";

    is (`:a ∧ `:m ∧ `:n ∧ `:z).rewrite(:1ce, (^:p({ quietly .?name ~~ /^<[a..m]>$/ })) => { ¬$:p }).squish,
    "(∧ (¬ a) (¬ m) n z)",
    "non-trivial callable matcher";
}

subtest 'rewrite times' => {
    plan 4;

    is (¬`:p ⇒ `:q).rewrite(:1ce,
        (  ^:p(Propositional::Variable)) => { ¬$:p },
        (¬¬^:p(Propositional::Variable)) => {  $:p },
        ),
        "(⇒ p (¬ q))",
        ":1ce";

    is (¬`:p ⇒ `:q).rewrite(:2ce,
        (  ^:p(Propositional::Variable)) => { ¬$:p },
        (¬¬^:p(Propositional::Variable)) => {  $:p },
        ),
        "(⇒ (¬ p) q)",
        ":2ce";

    is (¬`:p ⇒ `:q).rewrite(:3ce,
        (  ^:p(Propositional::Variable)) => { ¬$:p },
        (¬¬^:p(Propositional::Variable)) => {  $:p },
        ),
        "(⇒ p (¬ q))",
        ":3ce";

    is (¬`:p ⇒ `:q).rewrite(:4times,
        (  ^:p(Propositional::Variable)) => { ¬$:p },
        (¬¬^:p(Propositional::Variable)) => {  $:p },
        ),
        "(⇒ (¬ p) q)",
        ":4times";
}

is (¬`:p ⇒ `:q)\
    .rewrite((  ^:p(Propositional::Variable)) => { ¬$:p }, :1ce)
    .rewrite((¬¬^:p(Propositional::Variable)) => {  $:p }, :1ce),
    "(⇒ p (¬ q))",
    "toggle negations at variables";

is (¬(¬`:p ⇒ `:q))\
    .rewrite((  ^:p(Propositional::Variable)) => { ¬$:p }, :1ce)
    .rewrite((¬¬^:p(Propositional::Variable)) => {  $:p }, :1ce),
    "(¬ (⇒ p (¬ q)))",
    "toggle negations at variables only";

subtest "listy operators" => {
    plan 3;

    is (`:p ∧ `:q ∧ `:r).rewrite((^:p ∧ ^:q) => { $:p ∨ $:q }).squish,
        "(∨ p q r)",
        "rewrite works on listy operators";

    is (`:p ∧ `:q ∧ `:r).spread.rewrite((^:p ∧ ^:q ∧ ^:r) => { $:p ∨ $:q ∨ $:r }).squish,
        "(∨ p q r)",
        "rewrite works with listy pattern";

    is (`:p ∧ `:q ∧ (¬`:p ∨ `:r ∨ `:s) ∧ `:t).rewrite(
        (^:p ∧ ^:__ ∧ (^:r ∨ ^:__) ∧ ^:t) => {
            # Touch them all to give this callable the right signature
            sink $:p, $:r, $:t, $:__;
            $:p ∨ $:r ∨ $:t
        }).squish,
        "(∨ p (¬ p) r t)",
        "complex listy rewrite";
}

is (`:x ⇔ `:y ∨ (`:z ∧ `:x)).rewrite(
    (  ^:p ⇔ ^:q)       => { ($:p ⇒  $:q) ∧ ($:q ⇒ $:p) },
    (  ^:p ⇒ ^:q)       => { ¬$:p ∨  $:q                },
    (¬(^:p ∨ ^:q))      => { ¬$:p ∧ ¬$:q                },
    (¬(^:p ∧ ^:q))      => { ¬$:p ∨ ¬$:q                },
    (¬¬^:p)             => {  $:p                       },
    (^:p ∨ (^:q ∧ ^:r)) => { ($:p ∨  $:q) ∧ ($:p ∨ $:r) },
    ((^:q ∧ ^:r) ∨ ^:p) => { ($:p ∨  $:q) ∧ ($:p ∨ $:r) },
    ).squish,
    "(∧ (∨ z (¬ x) y) (∨ z (¬ y) x) (∨ x (¬ x) y) (∨ x (¬ y) x))",
    "CNF with all rewrite rules at once";
