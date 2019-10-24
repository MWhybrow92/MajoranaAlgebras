# Compute an orbital structure which has the
# following properties
#
# Input: G acting on Omega via Act

# Output: Orbital Structure
#         - A set of representatives of orbitals
#         - For any pair (i,j) efficiently
#           determine which orbital it belongs to
#         - For any pair (i,j) efficiently
#           compute an element g in G that takes (i,j)
#           to a representative in the set of
#           representatives
#         - iterate over orbit given a rep
#         - iterate over a transversal for
#           a stabilizer of a pair

InstallGlobalFunction( OrbitalStructure,
# gens  - generators of a group acting on Omega
# Omega - the domain
# Act   - action of Group(gens) on Omega
function(gens, Omega, Act)
    local o, so, i, res;

    # Result will be an orbital structure that allows
    # some stuff to be done with orbitals
    res := rec( gens := gens, group := Group(gens), act := Act );

    # Orbits. Currently we'll just choose the
    # first element in each orbit as orbit rep
    res.orbits := Orbits( res.group, Omega, Act );

    # This is so we're able to determine which orbit the
    # first point of a pair is in, and then get an element
    # of G that maps said point to the orbit rep
    # Really what we want is a schreier trees/vectors here
    res.orbreps := [];
    res.orbrepact := [];
    res.orbnums := HashMap(Size(Omega));
    res.orbstabs := [];
    for o in [1..Length(res.orbits)] do
        Add(res.orbreps, res.orbits[o][1]);
        res.orbstabs[o] := rec( );
        res.orbstabs[o].act := Act;
        res.orbstabs[o].group := Stabilizer(res.group, res.orbits[o][1], Act);
        res.orbstabs[o].orbits := Orbits(res.orbstabs[o].group, Omega, Act);
        res.orbstabs[o].orbnums := HashMap(Size(Omega));
        res.orbstabs[o].orbreps := [];
        res.orbstabs[o].orbrepact := [];
        for so in [1..Length(res.orbstabs[o].orbits)] do
            Add(res.orbstabs[o].orbreps, res.orbstabs[o].orbits[so][1]);
            for i in res.orbstabs[o].orbits[so] do
                res.orbstabs[o].orbnums[i] := so;
            od;
        od;

        for i in res.orbits[o] do
            res.orbnums[i] := o;
        od;
    od;

    return Objectify(OrbitalStructureType, res);
end);

InstallMethod( ViewObj, "for orbital structures",
               [ IsOrbitalStructure ],
function(os)
    Print("<orbital structure>");
end);

InstallMethod( PrintObj, "for orbital structures",
               [ IsOrbitalStructure ],
function(os)
    Print("<orbital structure>");
end);

# This could be a lot prettier still...
InstallGlobalFunction( OS_OrbitRepresentative,
function(os, pt)
    return os!.orbreps[os!.orbnums[pt]];
end);

InstallGlobalFunction( OS_CanonisingElement,
function(os, pt)
    if not IsBound(os!.orbrepact[pt]) then
        os!.orbrepact[pt] := RepresentativeAction( os!.group
                            , pt
                            , os!.orbreps[os!.orbnums[pt]]
                            , os!.act);
    fi;
    return os!.orbrepact[pt];
end);

InstallGlobalFunction( OS_CanonisingElement2,
function(os, pt, fo, so)
    if not IsBound(os!.orbstabs[fo].orbrepact[pt]) then
        os!.orbstabs[fo].orbrepact[pt] := RepresentativeAction( os!.orbstabs[fo].group
                                                              , pt
                                                              , os!.orbstabs[fo].orbreps[so]
                                                              , os!.act);
    fi;
    return os!.orbstabs[fo].orbrepact[pt];
end);


InstallGlobalFunction( OS_CanonisingElementAndRepresentative,
function(os, pt)
    return [ os!.orbreps[os!.orbnums[pt]]
           , OS_CanonisingElement(os, pt) ];
end);

InstallGlobalFunction( OS_StabilizerOf,
function(os, pt)
    return os!.orbstabs[os!.orbnums[pt]];
end);

InstallGlobalFunction(OrbitalRepresentative,
function(os, pair)
    local fo, so, p;

    # Returns a representative (as a pair of elements of the G set) for the
    # orbital that contains <pair>.

    fo := os!.orbnums[pair[1]];
    p := OS_CanonisingElement(os, pair[1]);
    so := os!.orbstabs[fo].orbnums[os!.act(pair[2], p)];
    return [ os!.orbreps[fo], os!.orbstabs[fo].orbreps[so] ];
end);

InstallGlobalFunction(AllOrbitalRepresentatives,
function(os)
    return Union(List(os!.orbreps, i -> [i,i])
                , ListX( [1..Length(os!.orbreps)]
                       , k -> os!.orbstabs[k].orbreps
                       , {x,y} -> [os!.orbreps[x],y] ) );
end);


# TODO: fix this.
InstallGlobalFunction(OrbitalCanonizingElement,
function(os, pair)

    # Returns a group elements that maps <pair> to its orbital representative
    # (as given by MAJORANA_OrbitalRep).

    local fo, so, p1, p2;

    fo := os!.orbnums[pair[1]];
    p1 := OS_CanonisingElement(os, pair[1]);
    so := os!.orbstabs[fo].orbnums[os!.act(pair[2], p1)];
    p2 := OS_CanonisingElement2(os, os!.act(pair[2], p1), fo, so);

    return p1 * p2;
end);

InstallGlobalFunction(OrbitalCanonizingElementInverse,
function(os, pair)
    return OrbitalCanonizingElement(os, pair)^-1;
    # Returns a group elements that maps the orbital representative of <pair>
    # to <pair> itself. This will be the inverse of the output of
    # MAJORANA_OrbitalCanonizingElement( os, pair )
end);

# Acting on sets of size 2
InstallGlobalFunction(UnorderedOrbitalRepresentative,
function(os, p)
    local a, b, oa, ob, r1, r2, p1, p2, tmp, tmp2;

    a := p[1];
    b := p[2];

    oa := os!.orbnums[a];
    ob := os!.orbnums[b];

    r1 := os!.orbreps[oa];
    r2 := os!.orbreps[ob];

    if r1 = r2 then
        # a and b are in the same orbit
        p1 := OS_CanonisingElement(os, a);
        # RepresentativeAction(os!.group, a, r1, os!.act);
        p2 := OS_CanonisingElement(os, b);

        tmp := [r1, os!.act(b,p1)];
        ob := os!.orbstabs[oa].orbnums[tmp[2]];
        tmp[2] := os!.orbstabs[oa].orbreps[ob];

        tmp2 := [r1, os!.act(a, p2)];
        ob := os!.orbstabs[oa].orbnums[tmp2[2]];
        tmp2[2] := os!.orbstabs[oa].orbreps[ob];

        return Minimum(tmp,tmp2);
    elif r2 < r1 then
        # b has the smaller orbrep, i.e. in the orbitalrep
        # has the smaller representative. We swap roles of a and b
        tmp := b; b := a; a := tmp;
        tmp := r2; r2 := r1; r1 := tmp;
        tmp := ob; ob := oa; oa := tmp;
    fi;

    # Move a to the smaller rep
    p1 := OS_CanonisingElement(os, a);
    # Now look in the point stabiliser of r1 what
    # element we can map b^p1 to
    ob := os!.orbstabs[oa].orbnums[os!.act(b, p1)];
    return [ r1, os!.orbstabs[oa].orbreps[ob]];
end);

InstallGlobalFunction(UnorderedOrbitalCanonizingElement,
function(os, pair)
    local a, b, oa, ob, r1, r2, p1, p2, tmp;

    a := pair[1];
    b := pair[2];

    r1 := OS_OrbitRepresentative(os, a);
    r2 := OS_OrbitRepresentative(os, b);
    if r1 = r2 then
        p1 := OS_CanonisingElement(os, a);
        p2 := OS_CanonisingElementAndRepresentative(OS_StabilizerOf(os, r1), os!.act(b, p1));

        tmp := [ [r1, p2[1]], p1 * p2[2] ];

        p1 := OS_CanonisingElement(os, b);
        p2 := OS_CanonisingElementAndRepresentative(OS_StabilizerOf(os, r1), os!.act(a, p1));

        if p2[1] < tmp[1][2] then
            tmp := [ [r1, p2[1]], p1 * p2[2] ];
        fi;
        return tmp[2];
    elif r2 < r1 then
        p1 := OS_CanonisingElement(os, b);
        return p1 * OS_CanonisingElement(OS_StabilizerOf(os, r2), os!.act(a, p1));
    else
        p1 := OS_CanonisingElement(os, a);
        return p1 * OS_CanonisingElement(OS_StabilizerOf(os, r1), os!.act(b, p1));
    fi;
end);

InstallGlobalFunction(UnorderedOrbitalCanonizingElementInverse,
     {os, pair} -> UnorderedOrbitalCanonizingElement(os, pair) ^ -1);

InstallGlobalFunction(AllUnorderedOrbitalRepresentatives,
function(os)
    local reps, reps2, p, q;

    reps := Set(Union( List( [1..Length(os!.orbreps)]
                       , k -> ListX(os!.orbreps, os!.orbstabs[k].orbreps
                                    , {x,y} -> UnorderedOrbitalRepresentative(os, [x,y]) ) ) ) );
    return reps;
end);

InstallGlobalFunction(OrbitalTransversalIterator,
function( os, rep )
    local r, fo, so;

    # Make sure we have *the* rep, not *a* rep
    rep := OrbitalRepresentative(os, rep);

    r := rec( orb := HashMap()
            , new := [ [ rep, [] ] ]
            , NextIterator := function(iter)
                local i, pntp, pnt, npntp, npnt;

                pntp := Remove(iter!.new, 1);
                pnt := pntp[1];

                for i in [1..Length(os!.gens)] do
                    npnt := OnTuples(pnt, os!.gens[i]);
                    if not npnt in iter!.orb then
                        npntp := [ npnt, Concatenation(pntp[2], [i]) ];
                        iter!.orb[npnt] := npntp[2];
                        Add(iter!.new, npntp);
                    fi;
                od;
                if Length(pntp[2]) = 0 then
                    return One(os!.group);
                else
                    return Product(List(pntp[2], i -> os!.gens[i]));
                fi;
            end
            , IsDoneIterator := iter -> iter!.new = []
            , ShallowCopy := iter -> rec( orb := StructuralCopy(iter!.orb)
                                        , new := ShallowCopy(iter!.new) )
            );
    r.orb[rep] := [];
    return IteratorByFunctions(r);
end);

# For now, a disguised orbit algorithm which is probably better
# than computing RepresentativeAction all the time!
InstallGlobalFunction(UnorderedOrbitalTransversalIterator,
function( os, rep )
    local r, fo, so;

    # Make sure we have *the* rep, not *a* rep
    rep := UnorderedOrbitalRepresentative(os, rep);

    r := rec( orb := HashMap()
            , new := [ [ rep, [] ] ]
            , NextIterator := function(iter)
                local i, pntp, pnt, npntp, npnt;

                pntp := Remove(iter!.new, 1);
                pnt := pntp[1];

                for i in [1..Length(os!.gens)] do
                    npnt := Set(pnt, x -> os!.act(x, os!.gens[i]));
                    if not npnt in iter!.orb then
                        npntp := [ npnt, Concatenation(pntp[2], [i]) ];
                        iter!.orb[npnt] := npntp[2];
                        Add(iter!.new, npntp);
                    fi;
                od;
                if Length(pntp[2]) = 0 then
                    return One(os!.group);
                else
                    return Product(List(pntp[2], i -> os!.gens[i]));
                fi;
            end
            , IsDoneIterator := iter -> iter!.new = []
            , ShallowCopy := iter -> rec( orb := StructuralCopy(iter!.orb)
                                        , new := ShallowCopy(iter!.new) )
            );
    r.orb[rep] := [];
    return IteratorByFunctions(r);
end);

BindGlobal("UnorderedOrbitalTest",
function(os, domain)
    local o, orbs, reps, muoreps;
    orbs := Orbits(os!.group, Combinations(domain, 2), OnSets);
    reps := List(orbs, Minimum);

    muoreps := AllUnorderedOrbitalRepresentatives(os);
    for o in domain do
        if o in os!.orbreps then
            if not ([o,o] in muoreps) then
                Error("The element ", o, " is an orbit representative, but its diagonal is not a representative");
            fi;
            Remove(muoreps, Position(muoreps, [o,o]));
        else
            if [o,o] in muoreps then
                Error("The element ", o, " is not an orbit representative, but its diagonal is a representative");
            fi;
        fi;
    od;
    if not IsSet(muoreps) then
        Error("Representatives do not form a set");
    fi;
    if not Set(muoreps) = Set(reps) then
        Print("Elements in muoreps that are not in reps: ", Difference(muoreps, reps), "\n");
        Print("Elements in reps that are not in muoreps: ", Difference(reps, muoreps), "\n");
        Error("differences between orbital reps and reps");
    fi;
    return true;
end);

BindGlobal("UnorderedOrbitalTransversalTest",
function(os, domain)
    local o, orbs, r, reps, i, iter, e, p;

    orbs := Orbits(os!.group, Combinations(domain, 2), OnSets);
    reps := List(orbs, Minimum);

    for r in reps do
        o := ShallowCopy(Filtered(orbs, x -> r in x)[1]);
        iter := UnorderedOrbitalTransversalIterator(os, r);
        for i in iter do
            e := OnSets(r, i);
            p := Position(o, e);
            if p = fail then
                Print("element ", e, " = ", r, "^", i, " not found\n");
            else
                Remove(o, p);
            fi;
        od;
        if not IsEmpty(o) then
            Error("leftover elements in orbit: ", o, " with rep ", r, "\n");
        fi;
    od;
    return true;
end);

BindGlobal("UnorderedOrbitalCanonizingTest",
function(os, domain)
    local o, orbs, r, rep, i, iter, e, p, can;

    orbs := Orbits(os!.group, Combinations(domain, 2), OnSets);
    for o in orbs do
        for i in o do
            rep := UnorderedOrbitalRepresentative(os, i);
            can := UnorderedOrbitalCanonizingElement(os, i);
            if rep <> OnSets(i, can) then;
                Error("element ", i, " is not canonized by ", can, "\n");
            fi;
        od;
    od;
    return true;
end);

BindGlobal("OrbitalTest",
function(os, domain)
    local o, orbs, reps, muoreps;
    orbs := Orbits(os!.group, Tuples(domain, 2), OnTuples);
    reps := List(orbs, Minimum);

    muoreps := AllOrbitalRepresentatives(os);
    if not IsSet(muoreps) then
        Error("Representatives do not form a set");
    fi;
    if not Set(muoreps) = Set(reps) then
        Print("Elements in muoreps that are not in reps: ", Difference(muoreps, reps), "\n");
        Print("Elements in reps that are not in muoreps: ", Difference(reps, muoreps), "\n");
        Error("differences between orbital reps and reps");
    fi;
    return true;
end);

BindGlobal("OrbitalTransversalTest",
function(os, domain)
    local o, orbs, r, reps, i, iter, e, p;

    orbs := Orbits(os!.group, Arrangements(domain, 2), OnTuples);
    reps := List(orbs, Minimum);

    for r in reps do
        o := ShallowCopy(Filtered(orbs, x -> r in x)[1]);
        iter := OrbitalTransversalIterator(os, r);
        for i in iter do
            e := OnTuples(r, i);
            p := Position(o, e);
            if p = fail then
                Print("element ", e, " = ", r, "^", i, " not found\n");
                Error("");
            else
                Remove(o, p);
            fi;
        od;
        if not IsEmpty(o) then
            Error("leftover elements in orbit: ", o, " with rep ", r, "\n");
        fi;
    od;
    return true;
end);

BindGlobal("OrbitalCanonizingTest",
function(os, domain)
    local o, orbs, r, rep, i, iter, e, p, can;

    orbs := Orbits(os!.group, Combinations(domain, 2), OnTuples);
    for o in orbs do
        for i in o do
            rep := OrbitalRepresentative(os, i);
            can := OrbitalCanonizingElement(os, i);
            if rep <> OnTuples(i, can) then;
                Print("element ", i, " is not canonized by ", can, "\n");
            fi;
        od;
    od;
    return true;
end);

