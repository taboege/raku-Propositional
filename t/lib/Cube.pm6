unit module Cube;

multi circumfix:<[ ]> (Int $n) { 1..$n }

# This is a k-face of the n-cube, which might as well be the
# entire cube.
class Face {
    has Int $.n is required; # ambient dimension
    has Int $.k;             # face dimension

    # The following three sets must be a partition of [n].
    has Int @.I is required; # positions of *
    has Int @.K is required; # positions of 1
    has Int @.Z;             # positions of 0

    method WHICH {
        ValueObjAt.new: "Cube::Face|$!n|$!k|{@!I.sort.join(',')}|{@!K.sort.join(',')}"
    }

    method from-word (Str $w where m/^ <[01*]>+ $/) {
        # XXX: Indexing with IntStr <0> won't work unless we
        # store :into a regular Hash (Str --> Any) because the
        # hash returned by categorize is Any --> Any otherwise
        # and doesn't coerce <0> and <1> correctly.
        with $w.comb.antipairs.categorize(*.key, :as(1 + *.value), :into(my %)) {
            self.new: :n($w.chars),
                :I(*.Slip with .<*>),
                :K(*.Slip with .<1>),
                :Z(*.Slip with .<0>),
        }
    }

    submethod TWEAK {
        $!k = @!I.elems;
        @!Z = ([$!n] ∖ @!I ∖ @!K).keys;
        # Sanity check
        die "Inconsistent face definition"
            unless [$!n] == @!I ⊎ @!K ⊎ @!Z;
    }

    # Represent the face as a string of length $!n over {0,1,*}
    # with exactly |I|-many '*' symbols.
    method Str {
        # XXX: This doesn't use the indices stored in @!I, @!K, @!Z
        # but their relative positions to each other.
        my @map = @!I => '*', @!K => '1', @!Z => '0';
        @map.map: { slip .key X .value } ==>
        sort *[0] ==> map *[1] ==>
        join '' ==> my $word;
        $word
    }

    method gist { self.Str }
}

# Authoritative ordering of the k-faces of the n-cube
# used to convert between set of faces and binary string.
# It is crucial that this yields the same ordering as the
# one on https://www.gaussoids.de/gaussoids.html because
# we use those as input files.
sub Faces($n, $k) is export {
    return gather {
        for [$n].combinations($k) -> @I {
            for ([$n] ⊖ @I).keys.sort.combinations -> @K {
                take Face.new: :$n, :$k,
                    :I(@I.sort), :K(@K.sort);
            }
        }
    }
}

# Returns whether the face Δ embeds the face δ
# on the n-cube.
multi sub infix:<⊆> (Face \δ, Face \Δ) is export {
    δ.I ⊆ Δ.I and
    δ.K ⊆ Δ.I ∪ Δ.K and
    δ.Z ⊆ Δ.I ∪ Δ.Z
}

# Get all faces contained in Δ, then project down to the
# free coordinates of Δ. This takes a Δ.k-dimensional slice
# out of @faces.
multi sub infix:<↘> (@faces, Face \Δ) is export {
    my @contained = @faces.grep: * ⊆ Δ;
    return gather {
        for @contained -> \δ {
            my (@I, @K);
            my $i = 1;
            for Δ.I {
                # TODO: `given $_' seems like a no-op.
                # Can't we use `when' clauses directly
                # and NEXT $i++?
                given $_ {
                    when * ∈ δ.I { @I.push: $i }
                    when * ∈ δ.K { @K.push: $i }
                }
                $i++;
            }
            take δ.new: :n(Δ.k), :@I, :@K;
        }
    }
}

# The inverse to ↘: it takes a set of faces of the Δ.k-cube
# and embeds them into the Δ.n-cube, precisely into the
# Δ.k-face Δ.
multi sub infix:<↗> (@faces, Face \Δ) is export {
    return @faces.map(* ↗ Δ)
}

multi sub infix:<↗> (Face \δ, Face \Δ) is export {
    my (@I, @K);
    @I =  Δ.I[δ.I »-» 1];
    @K = |Δ.I[δ.K »-» 1], |Δ.K;
    δ.new: :n(Δ.n), :@I, :@K;
}

# Compute the dual face by exchanging K and Z.
multi sub postfix:<°> (Face \Δ) is tighter(&infix:<↘>) is export {
    .new: :n(.n), :I(.I), :K(.Z) with Δ;
}

# Permute the axes of the cube.
multi sub infix:<⤩> (Face \Δ, @π) is export {
    .new: :n(.n), :I(@π[.I »-» 1]), :K(@π[.K »-» 1]) with Δ
}
