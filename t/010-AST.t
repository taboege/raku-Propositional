use Test;
use Test::Propositional;

use Propositional;
use Propositional::AST;

plan 7;

is `:p, `:p, 'variable caching works';

subtest 'variables' => {
    plan 2;

    is-deeply (¬`:p ⇔ `:q).variables, set(`:p, `:q), '¬p ⇔ q';
    is-deeply (`:a ∨ ¬(¬`:b ⇒ `:z) ∧ `:b).variables, set(`:a, `:b, `:z), 'a ∨ ¬(¬b ⇒ z) ∧ b';
}

subtest 'associativity and listiness' => {
    plan 5;

    # This is one indicator for the difference between (p ⇒ q) ⇒ r and p ⇒ (q ⇒ r).
    todo "Right-associativity of ⇒ doesn't work";
    is (`:p ⇒ `:q ⇒ `:r).eval(Set(`:p => False, `:q => False, `:r => False)), True, '⇒ is right-associative';

    is-deeply (`:p ∧ `:q ∧ `:r), Propositional::AST::Operator::And.new\ (:operands(`:p, `:q, `:r)), '∧ is listy';
    is-deeply (`:p ∨ `:q ∨ `:r), Propositional::AST::Operator::Or.new\  (:operands(`:p, `:q, `:r)), '∨ is listy';
    is-deeply (`:p ⇒ `:q ⇒ `:r), Propositional::AST::Operator::Imply.new(:operands(`:p, `:q, `:r)), '⇒ is listy';
    is-deeply (`:p ⇔ `:q ⇔ `:r), Propositional::AST::Operator::Equiv.new(:operands(`:p, `:q, `:r)), '⇔ is listy';
}

subtest 'eval - primitives' => {
    plan 6;

    subtest 'p' => { given `:p {
        is .eval(Set(`:p => False)), False, 'f → f';
        is .eval(Set(`:p => True)),  True,  't → t';
    }}

    subtest '¬p' => { given ¬`:p {
        is .eval(Set(`:p => False)), True, 'f → t';
        is .eval(Set(`:p => True)), False, 't → f';
    }}

    subtest 'p ∧ q' => { given `:p ∧ `:q {
        is .eval(Set(`:p => False, `:q => False)), False, 'f f → f';
        is .eval(Set(`:p => False, `:q => True)),  False, 'f t → f';
        is .eval(Set(`:p => True,  `:q => False)), False, 't f → f';
        is .eval(Set(`:p => True,  `:q => True)),  True,  't t → t';
    }}

    subtest 'p ∨ q' => { given `:p ∨ `:q {
        is .eval(Set(`:p => False, `:q => False)), False, 'f f → f';
        is .eval(Set(`:p => False, `:q => True)),  True,  'f t → t';
        is .eval(Set(`:p => True,  `:q => False)), True,  't f → t';
        is .eval(Set(`:p => True,  `:q => True)),  True,  't t → t';
    }}

    subtest 'p ⇒ q' => { given `:p ⇒ `:q {
        is .eval(Set(`:p => False, `:q => False)), True,  'f f → t';
        is .eval(Set(`:p => False, `:q => True)),  True,  'f t → t';
        is .eval(Set(`:p => True,  `:q => False)), False, 't f → f';
        is .eval(Set(`:p => True,  `:q => True)),  True,  't t → t';
    }}

    subtest 'p ⇔ q' => { given `:p ⇔ `:q {
        is .eval(Set(`:p => False, `:q => False)), True,  'f f → t';
        is .eval(Set(`:p => False, `:q => True)),  False, 'f t → f';
        is .eval(Set(`:p => True,  `:q => False)), False, 't f → f';
        is .eval(Set(`:p => True,  `:q => True)),  True,  't t → t';
    }}
}

subtest 'eval - sample formulas' => {
    plan 5;

    subtest '¬¬¬¬¬¬¬p - ¬ stacks' => { given ¬¬¬¬¬¬¬`:p {
        is .eval(Set(`:p => False)), True, 'f → t';
        is .eval(Set(`:p => True)), False, 't → f';
    }}

    subtest '(p ∨ r) ∧ ((p ⇒ q) ∧ (r ⇒ q)) ⇒ q - tautology' => { given (`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q {
        diag .Str;
        is .eval(Set(`:p => False, `:q => False, `:r => False)), True, 'f f f → t';
        is .eval(Set(`:p => False, `:q => False, `:r => True)),  True, 'f f t → t';
        is .eval(Set(`:p => False, `:q => True,  `:r => False)), True, 'f t f → t';
        is .eval(Set(`:p => False, `:q => True,  `:r => True)),  True, 'f t t → t';
        is .eval(Set(`:p => True,  `:q => False, `:r => False)), True, 't f f → t';
        is .eval(Set(`:p => True,  `:q => False, `:r => True)),  True, 't f t → t';
        is .eval(Set(`:p => True,  `:q => True,  `:r => False)), True, 't t f → t';
        is .eval(Set(`:p => True,  `:q => True,  `:r => True)),  True, 't f t → t';
    }}

    subtest '(p ⇔ r) ∧ (r ⇔ ¬q) ∧ (q ⇔ p) - contradiction' => { given (`:p ⇔ `:r) ∧ (`:r ⇔ ¬`:q) ∧ (`:q ⇔ `:p) {
        diag .Str;
        is .eval(Set(`:p => False, `:q => False, `:r => False)), False, 'f f f → f';
        is .eval(Set(`:p => False, `:q => False, `:r => True)),  False, 'f f t → f';
        is .eval(Set(`:p => False, `:q => True,  `:r => False)), False, 'f t f → f';
        is .eval(Set(`:p => False, `:q => True,  `:r => True)),  False, 'f t t → f';
        is .eval(Set(`:p => True,  `:q => False, `:r => False)), False, 't f f → f';
        is .eval(Set(`:p => True,  `:q => False, `:r => True)),  False, 't f t → f';
        is .eval(Set(`:p => True,  `:q => True,  `:r => False)), False, 't t f → f';
        is .eval(Set(`:p => True,  `:q => True,  `:r => True)),  False, 't f t → f';
    }}

    subtest '(p ∨ r) ∧ ((p ⇒ q) ∨ (r ⇒ q)) ⇒ q - neither' => { given (`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∨ (`:r ⇒ `:q)) ⇒ `:q {
        diag .Str;
        is .eval(Set(`:p => False, `:q => False, `:r => False)), True,  'f f f → t';
        is .eval(Set(`:p => False, `:q => False, `:r => True)),  False, 'f f t → f';
        is .eval(Set(`:p => False, `:q => True,  `:r => False)), True,  'f t f → t';
        is .eval(Set(`:p => False, `:q => True,  `:r => True)),  True,  'f t t → t';
        is .eval(Set(`:p => True,  `:q => False, `:r => False)), False, 't f f → f';
        is .eval(Set(`:p => True,  `:q => False, `:r => True)),  True,  't f t → t';
        is .eval(Set(`:p => True,  `:q => True,  `:r => False)), True,  't t f → t';
        is .eval(Set(`:p => True,  `:q => True,  `:r => True)),  True,  't f t → t';
    }}

    todo "Right-associativity of ⇒ doesn't work";
    subtest 'p ⇒ q ⇒ r - neither' => { given `:p ⇒ `:q ⇒ `:r {
        diag .Str;
        is .eval(Set(`:p => False, `:q => False, `:r => False)), True,  'f f f → t';
        is .eval(Set(`:p => False, `:q => False, `:r => True)),  True,  'f f t → t';
        is .eval(Set(`:p => False, `:q => True,  `:r => False)), True,  'f t f → t';
        is .eval(Set(`:p => False, `:q => True,  `:r => True)),  True,  'f t t → t';
        is .eval(Set(`:p => True,  `:q => False, `:r => False)), True,  't f f → t';
        is .eval(Set(`:p => True,  `:q => False, `:r => True)),  True,  't f t → t';
        is .eval(Set(`:p => True,  `:q => True,  `:r => False)), False, 't t f → f';
        is .eval(Set(`:p => True,  `:q => True,  `:r => True)),  True,  't f t → t';
    }}
}

subtest 'truth-table' => {
    plan 6;

    is-deeply set(truth-table(¬`:p).map({ .value ?? .key !! Empty })),
        set(Set(`:p => False)),
        '¬p';

    is-deeply set(truth-table((`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∨ (`:r ⇒ `:q)) ⇒ `:q).map({ .value ?? Empty !! .key })),
        set(Set(`:r), Set(`:p)),
        '(p ∨ r) ∧ ((p ⇒ q) ∨ (r ⇒ q)) ⇒ q';

    subtest '(p ∨ r) ∧ ((p ⇒ q) ∧ (r ⇒ q)) ⇒ q' => { given (`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q {
        ok  .satisfiable,   'satisfiable';
        ok  .tautology,     'tautology';
        nok .contradiction, 'not contradiction';
    }}

    subtest '(p ⇔ r) ∧ (r ⇔ ¬q) ∧ (q ⇔ p)' => { given (`:p ⇔ `:r) ∧ (`:r ⇔ ¬`:q) ∧ (`:q ⇔ `:p) {
        nok .satisfiable,   'not satisfiable';
        nok .tautology,     'not tautology';
        ok  .contradiction, 'contradiction';
    }}

    subtest '(p ∨ r) ∧ ((p ⇒ q) ∨ (r ⇒ q)) ⇒ q' => { given (`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∨ (`:r ⇒ `:q)) ⇒ `:q {
        ok  .satisfiable,   'satisfiable';
        nok .tautology,     'not tautology';
        nok .contradiction, 'not contradiction';
    }}

    subtest 'p ⇒ q ⇒ r' => { given `:p ⇒ `:q ⇒ `:r {
        ok  .satisfiable,   'satisfiable';
        nok .tautology,     'not tautology';
        nok .contradiction, 'not contradiction';
    }}
}

subtest 'squish and spread' => {
    plan 5;

    is Propositional::AST::Operator::And.new(operands => (
        Propositional::AST::Operator::And.new(operands => (
            `:p, `:q,
        )),
        `:r,
    )).squish,
    Propositional::AST::Operator::And.new(operands => (`:p, `:q, `:r)),
    "squish works on left-associative";

    is Propositional::AST::Operator::Imply.new(operands => (
        `:p,
        Propositional::AST::Operator::Imply.new(operands => (
            `:q, `:r,
        )),
    )).squish,
    Propositional::AST::Operator::Imply.new(operands => (`:p, `:q, `:r)),
    "squish works on right-associative";

    is Propositional::AST::Operator::And.new(operands => (
        `:p,
        Propositional::AST::Operator::And.new(operands => (
            `:q, `:r,
        )),
    )).squish,
    (`:p ∧ `:q ∧ `:r),
    "operators squish automatically";

    is (`:p ∧ `:q ∧ `:r).spread,
    Propositional::AST::Operator::And.new(operands => (
        Propositional::AST::Operator::And.new(operands => (
            `:p, `:q,
        )),
        `:r,
    )),
    "spread works on left-associative";

    is (`:p ⇒ `:q ⇒ `:r).spread,
    Propositional::AST::Operator::Imply.new(operands => (
        `:p,
        Propositional::AST::Operator::Imply.new(operands => (
            `:q, `:r
        )),
    )),
    "spread works on right-associative";
}
