use Test;

use Propositional;
use Propositional::AST;
use Propositional::CNF;
use Propositional::SAT;

use lib 't/lib';
use Cube;

# In the n-cube there are 3*binom(n,2)*2**(n-2) WrapSquare variables,
# one for every 2-face and every one of the three kinds.
class WrapSquare is Cube::Face does Propositional::Variable {
    has $.kind is required;

    # Catch operators defined for Cube::Face and sneak in our $!kind.
    multi method new (::?CLASS:D: *%_) {
        callwith |%_, :$!kind;
    }

    multi method new (Cube::Face \Δ, :$kind) {
        $kind //= self.kind if self.DEFINITE;

        # Save space by preventing "redundant" instances, in the sense
        # of this being a value type.
        state %cache;
        my $request = "WrapSquare|$kind|{Δ.WHICH}";
        %cache{$request} //= self.bless: :$kind, :n(.n), :I(.I), :K(.K) with Δ
    }

    method WHICH {
        ValueObjAt.new: "WrapSquare|$!kind|{callsame}"
    }

    method Str  { "{$!kind}<{ callsame }>" }
    method gist { self.Str                 }
}

sub WrapSquares ($n) {
    Faces($n, 2).map: -> \δ {
        slip do WrapSquare.new(δ, kind => $_) for <□ ■ 🎀>
    }
}

multi prefix:<□> (Str $s) {
    WrapSquare.new: :kind<□>,
        Cube::Face.from-word($s)
}

multi prefix:<■> (Str $s) {
    WrapSquare.new: :kind<■>,
        Cube::Face.from-word($s)
}

multi prefix:<🎀> (Str $s) {
    WrapSquare.new: :kind<🎀>,
        Cube::Face.from-word($s)
}

class Giftoid {
    has $.n;
    has $.deco;

    # Definition of a gift. A gift is a mapping from 2-faces
    # of the 3-cube to gift wrap (□), ribbon (■) or bow (🎀),
    # which fulfills the following properties:
    #
    #   (Just wrapping) it can have no ribbon or bow at all
    #   (Glued bow) it can have a single bow and no ribbon,
    #   (Ribbon belt) if there is ribbon, each ribbon must
    #     be on a "belt" of ribbon around the cube,
    #   (Bow belt) if there is a bow and ribbon, each ribbon
    #     and bow must be on a belt of ribbon or bow,
    #   (One bow) there may be at most one bow,
    #   (Disambiguation) if all sides have ribbon, there
    #     must be a bow.
    #
    our proto axioms (|) { * }
    multi axioms ($n = 3) {
        state $cache;
        return $cache if $cache;
        # Get a CNF of a special case axiomatizing all gifts where
        # only the face <**0> could have a bow.
        my \φ = .CNF with [∧] gather {
            # At least one of the variables for <**0> must be set.
            # The only case when more than one of them can be set
            # is when bow implies ribbon.
            take □<**0> ∨ ■<**0> ∨ 🎀<**0>;
            take □<**0> ⇒ ¬(■<**0> ∨ 🎀<**0>);
            take ■<**0> ⇒ ¬(□<**0> ∨ 🎀<**0>);
            take 🎀<**0> ⇒ ¬(□<**0> ∨ ■<**0>);

            # Ribbon belt and Bow belt are similar enough to axiomatize
            # them together. The bow plays the same role as a ribbon
            # in that one.
            #
            # For each ribbon, the opposite ribon must also be taken or
            # the opposite is a bow.
            take ■<**0> ⇒ (■<**1> ∨ 🎀<**1>);
            # If <**0> and its opposite <**1> have ribbon/bow, at least
            # one of the two belts through them must have ribbon/bow.
            take (■<**0> ∧ ■<**1>) ⇒ (■<*0*> ∨ 🎀<*0*> ∨ ■<0**> ∨ 🎀<0**>);
            take (🎀<**0> ∧ ■<**1>) ⇒ (■<*0*> ∨ ■<0**>);
            # If there is a bow and ribbon on another belt, the Bow belt
            # axiom still requires the opposite of the bow to be ribbon.
            take (🎀<**0> ∧ (■<*0*> ∨ ■<0**>)) ⇒ ■<**1>;

            # One bow axiom
            take 🎀<**0> ⇒ ¬(🎀<**1> ∨ 🎀<*0*> ∨ 🎀<*1*> ∨ 🎀<0**> ∨ 🎀<1**>);

        }
        # The conjunction over the orbit of the above special case under
        # the action of the hyperoctahedral group gives the full
        # axiomatization of gifts. First act with duality, then permute.
        my \ψ = φ.rewrite(:1ce,
            (^:s(WrapSquare)) => { $:s° }
        );
        $cache = [∧] gather for (1,2,3).permutations -> \π {
            take (φ ∧ ψ).rewrite(:1ce,
                (^:s(WrapSquare)) => { $:s ⤩ π }
            );

            # The disambiguation axiom is already symmetric. It didn't have
            # to be included and needlessly repeated above.
            LAST take ¬(■<**0> ∧ ■<**1> ∧ ■<*0*> ∧ ■<*1*> ∧ ■<0**> ∧ ■<1**>);
        }
    }

    # To axiomatize $n-giftoids, the 3-cube axiomatization has to
    # be replicated in every 3-face of the $n-cube.
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
        #        (^:s(WrapSquare)) => { $:s ↗ Δ }
        #    )
        #}
    }

    method Str {
        WrapSquares($!n).map({ .kind if $_ ∈ $!deco }).join
    }

    method gist { self.Str }
}

plan 4;

my \GIFTS = set(
    <□□□□□□>,
    <🎀□□□□□>, <□🎀□□□□>, <□□🎀□□□>, <□□□🎀□□>, <□□□□🎀□>, <□□□□□🎀>,
    <■■■■□□>, <🎀■■■□□>, <■🎀■■□□>, <■■🎀■□□>, <■■■🎀□□>,
    <■■□□■■>, <🎀■□□■■>, <■🎀□□■■>, <■■□□🎀■>, <■■□□■🎀>,
    <□□■■■■>, <□□🎀■■■>, <□□■🎀■■>, <□□■■🎀■>, <□□■■■🎀>,
    <🎀■■■■■>, <■🎀■■■■>, <■■🎀■■■>, <■■■🎀■■>, <■■■■🎀■>, <■■■■■🎀>,
);

is count-sat(Giftoid::axioms(3), :now),           28, "number of gifts";
if %*ENV<PROPOSITIONAL_INTENSE_TESTING> {
    is count-sat(Giftoid::axioms(4), :now),     1848, "number of 4-giftoids";
    is count-sat(Giftoid::axioms(5), :now), 58213276, "number of 5-giftoids";
}
else {
    skip('PROPOSITIONAL_INTENSE_TESTING is not set') xx 2;
}

is-deeply all-sat(Giftoid::axioms).map({
        Giftoid.new: n => 3, deco => $_
    })».Str.Set,
    GIFTS,
    "list of gifts"
;
