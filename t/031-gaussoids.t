use Test;

use Propositional;
use Propositional::AST;
use Propositional::CNF;
use Propositional::SAT;

use lib 't/lib';
use Cube;

class Square is Cube::Face does Propositional::Variable {
    multi method new (Cube::Face \Δ) {
        # Save space by preventing "redundant" instances, in the sense
        # of this being a value type.
        state %cache;
        my $request = "Square|{Δ.WHICH}";
        %cache{$request} //= self.bless: :n(.n), :I(.I), :K(.K) with Δ
    }

    method WHICH {
        ValueObjAt.new: "Square|{callsame}"
    }

    method Str  { "■<{ callsame }>" }
    method gist { "■<{ callsame }>" }
}

sub Squares ($n) { Faces($n, 2).map: { Square.new($_) } }

# An activated square corresponds to a false Boolean variable.
# This is for consistency with gaussoids.de
multi prefix:<□> (Str $s) {
    Square.new(Cube::Face.from-word($s))
}

multi prefix:<■> (Str $s) {
    ¬□$s
}

class Gaussoid {
    has $.n;
    has $.faces;

    our proto axioms (|) { * }
    multi axioms ($n = 3) {
        state $cache;
        return $cache if $cache;
        my \φ = .CNF with [∧] gather {
            take (■<**0> ∧ ■<*1*>) ⇒ (■<*0*> ∧ ■<**1>);
            take (■<**1> ∧ ■<*1*>) ⇒ (■<**0> ∧ ■<*0*>);
            take (■<**0> ∧ ■<*0*>) ⇒ (■<**1> ∧ ■<*1*>);
            take (■<**0> ∧ ■<**1>) ⇒ (■<*0*> ∨ ■<0**>);
        }

        my \ψ = φ.rewrite(:1ce,
            (^:s(Square)) => { $:s° }
        );

        $cache = [∧] gather for (1,2,3).permutations -> \π {
            take (φ ∧ ψ).rewrite(:1ce,
                (^:s(Square)) => { $:s ⤩ π }
            )
        }
    }
    multi axioms ($n where * > 3) {
        gather for axioms.'Propositional::CNF'().clauses X Faces($n, 3) -> ($c, \Δ) {
            take Propositional::CNF::Clause.new:
                vars => $c.vars.keys.map(* ↗ Δ).Set,
                nars => $c.nars.keys.map(* ↗ Δ).Set,
            ;
        }
        # Too memory-hungry.
        #my \Φ = axioms;
        #[∧] gather for Faces($n, 3) -> \Δ {
        #    take Φ.rewrite(:1ce,
        #        (^:s(Square)) => { $:s ↗ Δ }
        #    )
        #}
    }

    method Str {
        Squares($!n).map({ $_ ∈ $!faces ?? <■> !! <□> }).join
    }

    method gist { self.Str }
}

plan 4;

my \GAUSSIANS = set(
    <□□□□□□>,
    <□■■■■■>, <■■□■■■>, <■■■■□■>,
    <■□■■■■>, <■■■□■■>, <■■■■■□>,
    <■■□□□□>, <□□■■□□>, <□□□□■■>,
    <■■■■■■>,
);

is count-sat(Gaussoid::axioms(3), :now),           11, "number of 3-gaussoids";
if %*ENV<PROPOSITIONAL_INTENSE_TESTING> {
    is count-sat(Gaussoid::axioms(4), :now),      679, "number of 4-gaussoids";
    # TODO: Lnenicka/Matus axioms
    is count-sat(Gaussoid::axioms(5), :now), 60212776, "number of 5-gaussoids";
}
else {
    skip('PROPOSITIONAL_INTENSE_TESTING is not set') xx 2;
}

is-deeply all-sat(Gaussoid::axioms).map({
        Gaussoid.new: n => 3, faces => $_
    })».Str.Set,
    GAUSSIANS,
    "list of 3-gaussoids"
;
