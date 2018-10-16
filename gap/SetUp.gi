InstallGlobalFunction(ShapesOfMajoranaRepresentationAxiomM8,
    
    function(G,T)
    
    local   gens, g, perm,
            t,              # size of T
            i,              # indices
            j,
            k,
            x,              # result of orbitals
            shape,          # one shape
            RepsSquares6A,  # (ts)^2 where o(ts) = 6
            unknowns,       # indices of 3X axes
            pos,            # positions
            Binaries,       # used to loop through options for shapes
            input;          #
    
    t := Size(T);

    # Check that T obeys axiom M8

    for i in [1..t] do
        for j in [1..t] do
            if Order(T[i]*T[j]) = 6 and not (T[i]*T[j])^3 in T then
                Error("The set T does not obey axiom M8");
            fi;
        od;
    od;
    
    # Construct orbitals of  on T x T
    
    gens := [];
    
    for g in GeneratorsOfGroup(G) do 
        perm := [];
        for i in [1..t] do 
            Add(perm, Position(T, T[i]^g));
        od;
        Add(gens, perm);
    od;
    
    input := rec();
    
    input.pairorbit := NullMat(t,t);
    input.pairconj  := NullMat(t,t);
    input.pairreps  := [];
    input.orbitals  := [];
    input.pairconjelts := [ [1..t] ];
    input.coords := T;
    
    MAJORANA_Orbitals(gens, 0, input);
    
    input.orbitals := List( input.orbitals, x -> List(x, y -> T{y}) );

    # Determine occurances of 1A, 2A, 2B, 4A, 4B 5A, 6A in shape

    shape := NullMat(1,Size(input.pairreps))[1];

    RepsSquares6A := [];
    unknowns := [];;

    for i in [1..Size(input.pairreps)] do
    
        x := T{input.pairreps[i]};
        
        if Order(x[1]*x[2]) = 1 then 
            shape[i] := "1A";
        elif Order(x[1]*x[2]) = 2 and x[1]*x[2] in T then
            shape[i]:="2A";
        elif Order(x[1]*x[2]) = 2 and not x[1]*x[2] in T then
            shape[i]:="2B";
        elif Order(x[1]*x[2]) = 3 then
            shape[i]:="3X";
            Add(unknowns,i);
        elif Order(x[1]*x[2]) = 4 and not (x[1]*x[2])^2 in T then
            shape[i]:="4A";
        elif Order(x[1]*x[2]) = 4 and (x[1]*x[2])^2 in T then
            shape[i]:="4B";
        elif Order(x[1]*x[2]) = 5 then
            shape[i]:="5A";
        elif Order(x[1]*x[2])=6 then
            shape[i]:="6A";
            Add(RepsSquares6A,(x[1]*x[2])^2);
        else 
            Error("This is not a 6-transposition group");
        fi;
    od;

    # Check for inclusions of 2A and 3A in 6A

    for i in unknowns do
        if ForAny(input.orbitals[i], x -> x[1]*x[2] in RepsSquares6A) then
            shape[i]:="3A";;
            unknowns := Difference(unknowns, [i]);            
        fi;
    od;
    
    Binaries := AsList(FullRowSpace(GF(2),Size(unknowns)));
    
    input.shapes := [];

    # Add new values in the shape

    for i in [1..Size(Binaries)] do
        
        for j in [1..Size(unknowns)] do
            k := unknowns[j];
            if Binaries[i][j] = 1*Z(2) then
                shape[k]:="3A";
            else
                shape[k]:="3C";
            fi;            
        od;
        
        Add(input.shapes,ShallowCopy(shape));
    od;
    
    input.group       := G;
    input.involutions := T;
    
    return input;

    end );
    
InstallGlobalFunction(ShapesOfMajoranaRepresentation,
    
    function(G,T)
    
    local   gens,
            t,              # size of T
            i,              # indices
            j,
            k,
            x,              # result of orbitals
            ind,            # list of indices  
            orbs,           # orbitals on T
            shape,          # one shape
            RepsSquares4X,  # (ts)^2 where o(ts) = 4
            RepsSquares6A,  # (ts)^2 where o(ts) = 6
            RepsCubes6A,    # (ts)^3 where o(ts) = 6
            gph,            # digraph of 2X, 4X inclusions
            cc,             # connected components of gph
            pos,            # positions
            Binaries,       # used to loop through options for shapes
            input;          #
    
    t := Size(T);
    
    # Construct orbitals of  on T x T
    
    gens := List( GeneratorsOfGroup(G), g -> MAJORANA_FindTauMap(g, T) );
    
    input := rec();
    
    input.pairorbit := NullMat(t,t);
    input.pairconj  := NullMat(t,t);
    input.pairreps  := [];
    input.orbitals  := [];
    input.pairconjelts := [ [1..t] ];
    input.coords := T;
    
    MAJORANA_Orbitals(gens, 0, input);
    
    input.orbitals := List( input.orbitals, x -> List(x, y -> T{y}) );

    # Determine occurances of 1A, 2A, 2B, 4A, 4B 5A, 6A in shape

    shape := NullMat(1,Size(input.pairreps))[1];

    RepsSquares4X := [];
    RepsSquares6A := [];
    RepsCubes6A := [];
    
    ind := NullMat(6,0);;

    for i in [1..Size(input.pairreps)] do
    
        x := T{input.pairreps[i]};
        
        if Order(x[1]*x[2]) = 1 then 
            shape[i] := "1A";
        elif Order(x[1]*x[2]) = 2 then
            shape[i]:="2X";
            Add(ind[2],i);
        elif Order(x[1]*x[2]) = 3 then
            shape[i]:="3X";
            Add(ind[3],i);
        elif Order(x[1]*x[2]) = 4 then
            shape[i]:="4X";
            Add(ind[4],i);
            Add(RepsSquares4X, (x[1]*x[2])^2);
        elif Order(x[1]*x[2]) = 5 then
            shape[i]:="5A";
        elif Order(x[1]*x[2])=6 then
            shape[i]:="6A";
            Add(ind[6],i);
            Add(RepsSquares6A,(x[1]*x[2])^2);
            Add(RepsCubes6A,(x[1]*x[2])^3);
        fi;
    od;
    
    # Check for inclusions of 2X in 4X
    
    gph := NullMat(Size(input.orbitals), 0);
    
    for i in ind[2] do 
        for x in input.orbitals[i] do
            pos := Positions(RepsSquares4X, x[1]*x[2]);
            
            if pos <> [] then
                Append(gph[i], ind[4]{pos} + Size(ind[2]));
            fi;
        od;
    od;
    
    gph := List(gph, DuplicateFreeList);
    
    cc := AutoConnectedComponents(gph);

    # Check for inclusions of 2A and 3A in 6A

    for i in ind[3] do
        if ForAny(input.orbitals[i], x -> x[1]*x[2] in RepsSquares6A) then
            shape[i]:="3A";;
            ind[3] := Difference(ind[3], [i]);            
        fi;
    od;
    
    for i in ind[2] do 
        if ForAny(input.orbitals[i], x -> x[1]*x[2] in RepsCubes6A) then
        
            shape[i]:="2A";;
            
            for x in cc do 
                if i in x then 
                    for j in Intersection(ind[2],x) do 
                        shape[j] := "2A";
                    od;
                    for j in Intersection(ind[4],x - Size(ind[2])) do 
                        shape[j] := "4B";
                    od;
                    
                    cc := Difference(cc, [x]);
                    
                fi;
            od; 
        fi;
    od;
    
    cc := Filtered(cc, x -> Size(Intersection(x,ind[2])) > 0);

    Binaries := AsList(FullRowSpace(GF(2),Size(ind[3]) + Size(cc)));
    
    input.shapes := [];

    # Add new values in the shape

    for i in [1..Size(Binaries)] do
        
        for j in [1..Size(ind[3])] do
            k:=ind[3][j];
            if Binaries[i][j] = 1*Z(2) then
                shape[k]:="3A";
            else
                shape[k]:="3C";
            fi;            
        od;
        
        for j in [1 .. Size(cc)] do 
            
            if Binaries[i][j + Size(ind[3])] = 1*Z(2) then 
                for k in Intersection(ind[2],cc[j]) do 
                    shape[k] := "2A";
                od;
                for k in Intersection(ind[4],cc[j] - Size(ind[2])) do 
                    shape[k] := "4B";
                od;
            else
                for k in Intersection(ind[2],cc[j]) do 
                    shape[k] := "2B";
                od;
                for k in Intersection(ind[4],cc[j] - Size(ind[2])) do 
                    shape[k] := "4A";
                od;
            fi;
        od;            
        
        Add(input.shapes,ShallowCopy(shape));
    od;
    
    input.group       := G;
    input.involutions := T;
    
    return input;

    end );
    
InstallGlobalFunction( MAJORANA_SetUp,

    function(input, index, axioms)
    
    local rep, s, t, i, j, k, gens, orbs, dim, algebras;
    
    rep         := rec( group       := input.group,
                        involutions := input.involutions,
                        shape       := input.shapes[index], 
                        axioms      := axioms   );
                        
    t := Size(rep.involutions);
                        
    rep.setup   := rec( coords          := [1..t], 
                        coordmap        := HashMap( t*t ),
                        pairorbit       := StructuralCopy(input.pairorbit),
                        pairconj        := StructuralCopy(input.pairconj),
                        pairconjelts    := StructuralCopy(input.pairconjelts),
                        pairreps        := ShallowCopy(input.pairreps)       );
                        
    for i in [1..t] do rep.setup.coordmap[i] := i; od;
    
    algebras := MAJORANA_DihedralAlgebras;
    
    ## Orbits on axes for eigenvectors
    
    gens := GeneratorsOfGroup(input.group);
    gens := List(gens, x -> MAJORANA_FindTauMap(x, rep.involutions));

    orbs := MAJORANA_Orbits(gens, t, rep.setup);

    rep.setup.conjelts := orbs.conjelts;
    rep.setup.orbitreps := orbs.orbitreps;
    
    ## Set up products and eigenvectors
    
    s := Size(rep.setup.pairreps);
    
    rep.algebraproducts := List([1..s], x -> false);
    rep.innerproducts   := List([1..s], x -> false);
    rep.evecs           := NullMat(t,3);

    for j in [1..t] do
        if j in rep.setup.orbitreps then
            for k in [1..3] do
                rep.evecs[j][k] := SparseMatrix(0, t, [], [], Rationals);
            od;
        else
            for k in [1..3] do
                rep.evecs[j][k] := false;
            od;
        fi;
    od;
    
    ## Embed dihedral algebras
    
    for i in Positions(rep.shape, "4B") do  
        MAJORANA_EmbedDihedralAlgebra( i, rep, algebras.4B );
    od;
    
    for i in Positions(rep.shape, "6A") do  
        MAJORANA_EmbedDihedralAlgebra( i, rep, algebras.6A );
    od;
    
    for i in PositionsProperty(rep.shape, x -> not x in [ "1A", "4B", "6A" ]) do
        MAJORANA_EmbedDihedralAlgebra( i, rep, algebras.(rep.shape[i]) );
    od;
    
    dim := Size(rep.setup.coords);
    
    rep.setup.nullspace := rec(     heads := [1 .. dim]*0,
                                    vectors := SparseMatrix( 0, dim, [], [], Rationals) );
    
    for i in rep.setup.orbitreps do
        for j in [1..3] do 
            rep.evecs[i][j]!.ncols := dim;
            rep.evecs[i][j] := MAJORANA_BasisOfEvecs(rep.evecs[i][j]);
        od; 
    od;
    
    for i in gens do MAJORANA_NClosedExtendPerm( i, rep); od;
    
    MAJORANA_Orbitals( gens, t, rep.setup);
    
    for i in [1..Size(rep.setup.pairreps)] do
    
        if not IsBound(rep.algebraproducts[i]) then 
            rep.algebraproducts[i] := false;
            rep.innerproducts[i] := false;
        elif rep.algebraproducts[i] <> false then 
            rep.algebraproducts[i]!.ncols := dim; 
        fi;
    od;
    
    return rep; 

    end );

InstallGlobalFunction( MAJORANA_EmbedDihedralAlgebra, 

    function( i, rep, subrep )
    
    local   dim, t, gens, x, inv, elts, emb, j, im, orbit, y, k, sign;
    
    dim := Size(rep.setup.coords);
    t := Size(rep.involutions);
    gens := GeneratorsOfGroup(subrep.group);
    
    x := rep.setup.pairreps[i];
    inv := rep.involutions{x};
    
    ## Embed the dihedral algebra
    
    emb := MAJORANA_FindEmbedding( rep, subrep, gens, inv );
        
    ## Add new vector(s) and their orbit(s) and extend pairconj and pairorbit matrices
    
    MAJORANA_AddNewVectors( rep, subrep, gens, inv);
    
    ## Embed the dihedral algebra
    
    emb := MAJORANA_FindEmbedding( rep, subrep, gens, inv );
    
    ## Add any new orbits
    
    gens := GeneratorsOfGroup(rep.group);
    gens := List( gens, g -> MAJORANA_FindTauMap(g, rep.involutions) );
    for j in gens do MAJORANA_NClosedExtendPerm( j, rep); od;

    for j in [1 .. Size(subrep.setup.pairreps)] do 
        
        im := emb{subrep.setup.pairreps[j]};
        
        if im[1] < 0 then im[1] := -im[1]; fi;        
        if im[2] < 0 then im[2] := -im[2]; fi;
        
        orbit := rep.setup.pairorbit[im[1]][im[2]];
        
        ## If need be, add a new orbit
        
        if orbit = 0 then 
            MAJORANA_NewOrbital(im, gens, rep.setup);
        fi;
    od;

    ## Embed products and evecs
    
    MAJORANA_Embed( rep, subrep, emb );

    end );

InstallGlobalFunction( MAJORANA_FindEmbedding, 

    function( rep, subrep, gens, inv)
    
    local imgs, emb, pos, x;
    
    imgs := List(subrep.setup.coords, w -> MAJORANA_MappedWord(rep, subrep, w, gens, inv) );
    
    emb := [];
    
    for x in imgs do
        pos := rep.setup.coordmap[x];
        if pos = fail then
            pos := rep.setup.coordmap[ Product( rep.involutions{x} )];
        fi;
        
        Add( emb, pos); 
    od;
    
    return emb;
    
    end );
    
InstallGlobalFunction( MAJORANA_AddNewVectors, 

    function(rep, subrep, gens, inv)
    
    local i, list, list_5A, new, new_5A, x, vec, g, im, k, dim;
    
    dim := Size(rep.setup.coords);
    
    for i in [Size(subrep.involutions) + 1 .. Size(subrep.setup.coords)] do
    
        ## Find the new vectors to be added to longcoords
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
    
    for x in rep.setup.pairorbit do 
        Append(x, [dim + 1 .. Size(rep.setup.coords)]*0 );
    od;
    
    for x in rep.setup.pairconj do 
        Append(x, [dim + 1 .. Size(rep.setup.coords)]*0 );
    od;
    
    Append(rep.setup.pairorbit, NullMat( Size(rep.setup.coords) - dim , Size(rep.setup.coords) ));
    Append(rep.setup.pairconj, NullMat( Size(rep.setup.coords) - dim , Size(rep.setup.coords) ));
    
    for g in rep.setup.pairconjelts do  MAJORANA_NClosedExtendPerm( g, rep); od;
    
    for g in rep.setup.conjelts do MAJORANA_NClosedExtendPerm( g, rep); od;
    
    end );
    
InstallGlobalFunction( MAJORANA_AddConjugateVectors,

    function( rep, new, new_5A )
    
    local   vec, g, im, im_5A, k, elts, x;
    
    ## Check if any new vectors have already been added
 
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
    
    for g in rep.setup.pairconjelts do
    
        im := List(new, x -> SortedList( g{ x } ));
        im := Filtered( im, x -> not x in rep.setup.coordmap );
        
        if rep.axioms = "AllAxioms" then 
            im := Filtered( im, x -> not Product( rep.involutions{x} ) in rep.setup.coordmap);
        fi;
        
        if im <> [] then 
        
            im_5A := List(new_5A, x -> SortedList( g{ x } ));
    
            if vec = fail then 
                Add( rep.setup.coords, im[1] );
                k := Size(rep.setup.coords);
            else
                k := rep.setup.coordmap[ SortedList( g{ vec } )];
                if k = fail then
                    k := rep.setup.coordmap[ Product(rep.involutions{ g{ vec } }) ];
                fi;
            fi;
            
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
    
InstallGlobalFunction( MAJORANA_FindPerm, 
    
    function(g, rep, subrep)
    
    local   dim, j, list, im, sign, vec;
    
    if IsRowVector(g) then return g; fi;
    
    dim := Size(subrep.setup.coords);
    list := [1..dim]*0;
        
    for j in [1..dim] do 
        
        vec := subrep.setup.coords[j];
    
        if IsRowVector(vec) then 
        
            im := list{vec};
            
            sign := 1;
            
            if im[1] < 0 then sign := -sign; im[1] := -im[1]; fi;
            if im[2] < 0 then sign := -sign; im[2] := -im[2]; fi;
            
            if im[1] > im[2] then im := im{[2,1]}; fi;
            
            list[j] := rep.setup.coords[ im ]; 

        else 
            list[j] := rep.setup.coordmap[ OnPoints( vec, g) ]; 
        fi;
    od;

    return list;
    
    end);
    
InstallGlobalFunction( MAJORANA_RemoveDuplicateShapes, 

    function(input)
    
    local autgp, inner_autgp, outer_auts, perm, g, i, pos, im;
    
    autgp := AutomorphismGroup(input.group);
    inner_autgp := InnerAutomorphismsAutomorphismGroup(autgp);
    outer_auts := [];
    
    for g in RightTransversal(autgp, inner_autgp) do 
        if AsSet(OnTuples(input.involutions, g)) = AsSet(input.involutions) then 
            perm := [];
            
            for i in [1..Size(input.orbitals)] do 
            
                im := OnPairs(Representative(input.orbitals[i]), g);
                
                pos := PositionProperty(input.orbitals, x -> im in x);
                
                if pos = fail then pos := PositionProperty(input.orbitals, x -> Reversed(im) in x); fi;
                
                if pos = fail then Error(); fi;
                
                Add(perm, pos);
            od;
        
            Add(outer_auts, perm);
        fi;
    od;
    
    for i in [1..Size(input.shapes)] do 
        if IsBound(input.shapes[i]) then 
            for g in outer_auts do 
                pos := Position(input.shapes, input.shapes[i]{g});
                if pos <> fail and pos <> i then 
                    Unbind(input.shapes[pos]);
                fi;
            od;
        fi;
    od;
    
    input.shapes := Compacted(input.shapes);
    
    end );
    
InstallGlobalFunction(MAJORANA_MappedWord,

    function(rep, subrep, w, gens, imgs)
    
    local im;
    
    if IsRowVector(w) then 
        im := List(w, i -> MappedWord(subrep.setup.coords[i], gens, imgs));
    
        return SortedList(List(im, x -> Position(rep.involutions, x )));
    else
        return Position(rep.involutions, MappedWord(w, gens, imgs) );
    fi;
    
    end );
    
InstallGlobalFunction( MAJORANA_FindTauMap,

    function(g, involutions)

    local perm,t;
    
    perm := [];
    
    for t in involutions do 
        Add(perm, Position(involutions, t^g) );
    od;
    
    return perm;
    
    end );
    
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

