
##
## The main setup function for the algorithm <MajoranaRepresentation>
##

#
# Input: a group,
#        a set of involutions,
#        an index into the list of shapes,
#        which axioms to assume
#
InstallGlobalFunction( MAJORANA_SetUp,

    function( input, index, options )

    local rep, s, t, i, dim, algebras, ev, orbs, gens;

    if not IsBound(options.axioms) then options.axioms := "AllAxioms"; fi;
    if not IsBound(options.form) then options.form := true; fi;

    algebras := MAJORANA_DihedralAlgebras;

    rep         := rec( group       := input.group,
                        involutions := input.involutions,
                        eigenvalues := [0, 1/4, 1/32], # The eigenvalues not equal to one
                        generators  := StructuralCopy(input.generators),
                        shape       := input.shapes[index],
                        axioms      := options.axioms,
                      );

    t := Size(rep.involutions);

    rep.setup   := rec( coords          := [1..t],
                        coordmap        := HashMap( t*t ),
                        pairrepsmap     := HashMap( t*t ),
                        pairorbit       := StructuralCopy(input.pairorbit),
                        pairconj        := StructuralCopy(input.pairconj),
                        pairconjelts    := StructuralCopy(input.pairconjelts),
                        pairreps        := ShallowCopy(input.pairreps)       );

    # coordmap gives the position in coords of the coord
    for i in [1..t] do
        rep.setup.coordmap[i] := i;
        rep.setup.coordmap[rep.involutions[i]] := i;
    od;

    orbs := MAJORANA_Orbits(input.generators, rep.setup);

    rep.setup.conjelts := orbs.conjelts;
    rep.setup.orbitreps := orbs.orbitreps;

    ## Set up products and eigenvectors

    # One algebra product for every pair
    # One inner product for every pair
    # eigenvector decomposition for ...?
    s := Size(rep.setup.pairreps);

    rep.algebraproducts := List([1..s], x -> false);
    rep.evecs           := [];
    if options.form = true then
        rep.innerproducts   := List([1..s], x -> false);
    fi;

    for i in rep.setup.orbitreps do
        rep.evecs[i] := rec(  );
        for ev in rep.eigenvalues do
            rep.evecs[i].(String(ev)) := SparseMatrix(0, t, [], [], Rationals);
        od;
    od;

    ## Embed dihedral algebras
    algebras := MAJORANA_DihedralAlgebras;

    for i in Positions(rep.shape, "4B") do
        MAJORANA_EmbedDihedralAlgebra( i, rep, algebras.4B );
    od;

    for i in Positions(rep.shape, "6A") do
        MAJORANA_EmbedDihedralAlgebra( i, rep, algebras.6A );
    od;

    for i in PositionsProperty(rep.shape, x -> not x in [ "1A", "4B", "6A" ]) do
        MAJORANA_EmbedDihedralAlgebra( i, rep, algebras.(rep.shape[i]) );
    od;

    ## Finish off setup
    # why dimension? isn't this just a spanning set right now?
    dim := Size(rep.setup.coords);

    rep.setup.nullspace := rec( heads := [1 .. dim]*0,
                                vectors := SparseMatrix( 0, dim, [], [], Rationals) );

    MAJORANA_AddConjugateEvecs(rep);

    for i in rep.generators do MAJORANA_ExtendPerm(i, rep); od;

    MAJORANA_FindOrbitals(rep, rep.generators, [1 .. dim]);

    ## Fill in the unknown algebra and inner products with the value false

    for i in [1..Size(rep.setup.pairreps)] do
        if not IsBound(rep.algebraproducts[i]) then
            rep.algebraproducts[i] := false;
            if IsBound(rep.innerproducts) then
                rep.innerproducts[i] := false;
            fi;
        elif rep.algebraproducts[i] <> false then
            rep.algebraproducts[i]!.ncols := dim;
        fi;
    od;

    return rep;
end);

##
## Given the dihedral algebra generated by the axes in <rep.setup.pairreps[i]>,
## adds any new 2A, 3A, 4A or 5A axes to <rep.setup.coords> and <rep.setup.coordmap>
## and adds any new products and eigenvectors coming from the dihedral algebra.
##

InstallGlobalFunction( MAJORANA_EmbedDihedralAlgebra,
function( i, rep, subrep )
    local gens, inv, elts, emb;

    inv := rep.setup.pairreps[i];

    ## Add new basis vector(s) and their orbit(s) and extend pairconj and pairorbit matrices
    MAJORANA_AddNewVectors(rep, subrep, inv);

    ## Find the embedding of the subrep into the main algebra
    emb := MAJORANA_FindEmbedding( rep, subrep, inv );

    ## Add any new orbits
    gens := List( GeneratorsOfGroup(rep.group), g -> MAJORANA_FindPerm(g, rep, rep) );
    MAJORANA_FindOrbitals(rep, gens, [1 .. Size(rep.setup.coords)]);

    ## Embed products and evecs
    MAJORANA_Embed( rep, subrep, emb );

    end );

##
## Finds the embedding of a dihedral algebra <subrep> into <rep>
##

InstallGlobalFunction( MAJORANA_FindEmbedding,
function( rep, subrep, inv)
    local imgs, emb, pos, x, gens;

    ## Find the images of the embedding of the subrep into the main rep
    gens := GeneratorsOfGroup(subrep.group);

    imgs := List(subrep.setup.coords, w -> MAJORANA_MappedWord(rep, subrep, w, gens, inv) );

    emb := [];

    for x in imgs do
        pos := rep.setup.coordmap[x];
        if pos = fail then
            pos := rep.setup.coordmap[ Product( rep.involutions{x} )];
        fi;

        Add(emb, pos);
    od;

    return emb;
end);

##
## If new vectors have been added to <setup.coords> then extend the action
## of an existing perm to these new vectors.
##

InstallGlobalFunction( MAJORANA_ExtendPerm,

    function(perm, rep)

    local dim, new_dim, i, im, sign, pos;

    new_dim := Size(rep.setup.coords);
    dim := Size(perm);

    for i in [dim + 1 .. new_dim] do
        im := perm{rep.setup.coords[i]};

        ## Keep track of sign changes

        sign := 1;

        if im[1] < 0 then im[1] := -im[1]; sign := -sign; fi;
        if im[2] < 0 then im[2] := -im[2]; sign := -sign; fi;

        if im[1] > im[2] then
            im := im{[2,1]};
        fi;

        ## Find the new vector in <setup.coords>

        pos := rep.setup.coordmap[im];

        if pos = fail then
            pos := rep.setup.coordmap[ Product( rep.involutions{im} ) ];
        fi;

        Add(perm, sign*pos);
    od;

    end);

##
## Adds any additional 2A, 3A, 4A or 5A vectors coming from the dihedral
## algebra <subrep>.
##
InstallGlobalFunction( MAJORANA_AddNewVectors,
function(rep, subrep, inv)
    local i, list, list_5A, new, new_5A, x, vec, g, im, k, dim, gens;

    dim := Size(rep.setup.coords);
    gens := GeneratorsOfGroup(subrep.group);

    # Take the additional basis vectors (if they exists) from the dihedral alg <subrep>
    for i in [Size(subrep.involutions) + 1 .. Size(subrep.setup.coords)] do

        ## Find the new vectors to be added to <setup.coordmap>
        ## TODO - do we want to change this to hashmaps?
        list := Positions(subrep.setup.poslist, i);
        list_5A := Positions(subrep.setup.poslist, -i);

        new := []; new_5A := [];

        for x in subrep.setup.longcoords{list} do
            Add( new, MAJORANA_MappedWord(rep, subrep, x, gens, inv));
        od;

        for x in subrep.setup.longcoords{list_5A} do
            Add( new_5A, MAJORANA_MappedWord(rep, subrep, x, gens, inv));
        od;

        MAJORANA_AddConjugateVectors( rep, new, new_5A );
    od;

    for g in rep.setup.conjelts do MAJORANA_ExtendPerm( g, rep); od;
    for g in rep.generators do MAJORANA_ExtendPerm( g, rep); od;

    end );

##
## When adding a new set of vectors to <rep.setup.coordmap>, also adds
## all of their images under the group action.
##
InstallGlobalFunction( MAJORANA_AddConjugateVectors,
function( rep, new, new_5A )
    local vec, g, im, im_5A, k, elts, x, transversal;

    # new and new_5A are pairs of indices

    ## Find which (if any) new vectors are not yet in <setup.coordmap>

    vec := First(new, x -> x in rep.setup.coordmap);

    if vec <> fail then
        new := Filtered(new, x -> not x in rep.setup.coordmap);
        new_5A := Filtered(new_5A, x -> not x in rep.setup.coordmap);
    fi;

    if vec = fail and rep.axioms <> "NoAxioms" then
        vec := First(new, x -> Product( rep.involutions{x} ) in rep.setup.coordmap );

        if vec <> fail then
            new := Filtered(new, x -> not Product( rep.involutions{x} ) in rep.setup.coordmap);
            new_5A := Filtered(new_5A, x -> not Product( rep.involutions{x} ) in rep.setup.coordmap);
        fi;
    fi;

    if new = [] then return; fi;

    ## If vec = fail then all vectors are new and a new rep will be added
    ## to <setup.coords>. Otherwise, there are some new vectors but these
    ## are equal to an existing element of <setup.coords>

    transversal := MAJORANA_UnorderedOrbitalTransversalIterator( rep.setup.orbitalstruct, new[1]);

    # g is a permutation represented as a list
    for g in transversal do

        g := ListSignedPerm(g, Size(rep.setup.coords));

        # new/new_5A is a list of pairs
        # this computes all conjugates of these pairs
        # is this pointless?
        # it adds [i,j]^g for all new "vectors"
        im := List(new, x -> SortedList( g{ x } ));
        im := Filtered( im, x -> not x in rep.setup.coordmap );

        if rep.axioms = "AllAxioms" then
            im := Filtered( im, x -> not Product( rep.involutions{x} ) in rep.setup.coordmap);
        fi;

        if im <> [] then

            im_5A := List(new_5A, x -> SortedList( g{ x } ));

            ## If need be, add a new vector to coords, otherwise find index of existing vector

            if vec = fail then
                Add( rep.setup.coords, im[1] );
                k := Size(rep.setup.coords);
            else
                k := rep.setup.coordmap[ SortedList( g{ vec } )];
                if k = fail then
                    k := rep.setup.coordmap[ Product(rep.involutions{ g{ vec } }) ];
                fi;
            fi;

            ## Add new vectors to <setup.coordmap>

            for x in im do rep.setup.coordmap[ x ] := k; od;
            for x in im_5A do rep.setup.coordmap[ x ] := -k; od;

            if rep.axioms = "AllAxioms" then
                for x in im do
                    rep.setup.coordmap[ Product( rep.involutions{ x } )] := k;
                od;
                for x in im_5A do
                    rep.setup.coordmap[ Product( rep.involutions{ x } )] := -k;
                od;
            fi;
        fi;
    od;

    end );

##
##  Use the group action to find more eigenvectors
##

InstallGlobalFunction( MAJORANA_AddConjugateEvecs,

    function(rep)

    local i, new, ev, v, g, im;

    for i in rep.setup.orbitreps do

        # Setup a record to record the new evecs
        new := rec();

        # Loop over eigenvalues
        for ev in RecNames(rep.evecs[i]) do
            new.(ev) := SparseMatrix(0, Size(rep.setup.coords), [], [], Rationals);

            for v in Iterator(rep.evecs[i].(ev)) do
                for g in Filtered(rep.setup.pairconjelts, h -> h[i] = i) do
                    # Find the image of each eigenvector under g
                    im := MAJORANA_ConjugateVec(v, g);

                    # Add the image to the new eigenspaces
                    if not _IsRowOfSparseMatrix(new.(ev), im) then
                        new.(ev) := UnionOfRows(new.(ev), im);
                    fi;
                od;
            od;

            # Find a basis of the new eigenspaces
            rep.evecs[i].(ev) := ReversedEchelonMatDestructive(new.(ev)).vectors;
        od;
    od;
end );

##
## <MappedWord> for indices or pairs of indices referring to elements of coords
##

#
InstallGlobalFunction(MAJORANA_MappedWord,

    function(rep, subrep, w, gens, inv)

    local im, imgs;

    imgs := rep.involutions{inv};

    if IsRowVector(w) then
        im := List(w, i -> MappedWord(subrep.setup.coords[i], gens, imgs));
        return SortedList(List(im, x -> Position(rep.involutions, x )));
    else

        return Position(rep.involutions, MappedWord(w, gens, imgs) );
    fi;
end);

##
## This is used only the the main algorithm to record algebra products once found
##

InstallGlobalFunction(SP_Inverse,

    function(perm)

    local l, inv, i;

    if perm = [] then return []; fi;

    l := Length(perm);

    inv := [1..l];

    for i in [1..l] do
        if perm[i] > 0 then
            inv[perm[i]] := i;
        else
            inv[-perm[i]] := -i;
        fi;
    od;

    return inv;

    end);

##
## Not currently in use, here for reference
##

InstallGlobalFunction(SP_Product,

    function( perm1, perm2) # Perms must be of same length!

    local prod, i;

    prod := [];

    for i in perm1 do
        if i > 0 then
            Add(prod, perm2[i]);
        else
            Add(prod, -perm2[-i]);
        fi;
    od;

    return prod;

    end );
