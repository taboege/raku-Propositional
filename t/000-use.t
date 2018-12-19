use Test;
use Test::META;

plan 5;

meta-ok;

use-ok 'Propositional';
use-ok 'Propositional::AST';
use-ok 'Propositional::CNF';
use-ok 'Propositional::SAT';
