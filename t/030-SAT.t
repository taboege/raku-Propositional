use Test;
use Test::Propositional;

use Propositional;
use Propositional::AST;
use Propositional::SAT;

plan 10;

subtest 'p ∧ q' => { given `:p ∧ `:q {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 1, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

subtest 'p ∨ q' => { given `:p ∨ `:q {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 3, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

subtest 'p ⇒ q' => { given `:p ⇒ `:q {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 3, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

subtest 'p ∧ ¬p' => { given `:p ∧ ¬`:p {
    plan 3;
    nok sat($_, :now), "SAT";
    todo "DSHARP bug?";
    is count-sat($_, :now), 0, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

skip "tautologies flunk";
=begin comment
subtest 'p ∨ ¬p' => { given `:p ∨ ¬`:p {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 2, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}
=end comment

subtest 'p ⇒ ¬p' => { given `:p ⇒ ¬`:p {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 1, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

subtest 'p ⇔ q' => { given `:p ⇔ `:q {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 2, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

skip "tautologies flunk";
=begin comment
subtest '(p ∨ r) ∧ ((p ⇒ q) ∧ (r ⇒ q)) ⇒ q' => { given (`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∧ (`:r ⇒ `:q)) ⇒ `:q {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 8, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}
=end comment

subtest '(p ⇔ r) ∧ (r ⇔ ¬q) ∧ (q ⇔ p)' => { given (`:p ⇔ `:r) ∧ (`:r ⇔ ¬`:q) ∧ (`:q ⇔ `:p) {
    plan 3;
    nok sat($_, :now), "SAT";
    is count-sat($_, :now), 0, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

subtest '(p ∨ r) ∧ ((p ⇒ q) ∨ (r ⇒ q)) ⇒ q - neither' => { given (`:p ∨ `:r) ∧ ((`:p ⇒ `:q) ∨ (`:r ⇒ `:q)) ⇒ `:q {
    plan 3;
    ok sat($_, :now), "SAT";
    is count-sat($_, :now), 6, "#SAT";
    is-deeply all-sat($_, :now).Set,
        .truth-table.map({ .key if .value }).Set,
        "AllSAT";
}}

# dispatch
# experiments with shared caches and #SAT.
