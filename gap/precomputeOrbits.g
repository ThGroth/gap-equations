#Precompute the 90 orbits of Q⁶/Stab(R₆)
#
# Directory for Saved results. Needs a trailing /
#
dirRep := "~/Repositories/GrigorchukCommutatorWidth/";
#
dir := Concatenation(dirRep,"gap/90orbs/");
################################################################
# action on images of automorphism.
# typical usage: action on tuples of images of generators.
OnImages := function(list,aut)
    local gens;
    gens := GeneratorsOfGroup(Source(aut));
    return List(gens,g->MappedWord(g^aut,gens,list));
end;

################################################################
# surface relator of a free group F.
surface_relator := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    return Product([2,4..Length(gens)],i->Comm(gens[i-1],gens[i]),One(F));
end;

################################################################
# the pure mapping class group of a surface group F / surface_relator,
# written in terms of automorphisms of F.
pure_mcg := function(F)
    local gens, d, L, i, imgs, x;
    gens := GeneratorsOfGroup(F);
    d := Length(gens);
    L := [];

    for i in [2,4..d] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i-1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [1,3..d-1] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i+1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [1,3..d-3] do
        imgs := ShallowCopy(gens);
        x := gens[i+1]/gens[i+2];
        imgs[i] := x*gens[i];
        imgs[i+1] := x*gens[i+1]/x;
        imgs[i+2] := x*gens[i+2]/x;
        imgs[i+3] := x*gens[i+3];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;

    #Switch two neighbours 
    #added by Thorsten prob. already contained in mcg
    for i in [1,3..d-3] do
        imgs := ShallowCopy(gens);
        imgs[i+2] := gens[i]^Comm(gens[i+2],gens[i+3]);
        imgs[i+3] := gens[i+1]^Comm(gens[i+2],gens[i+3]);
        imgs[i] := gens[i+2];
        imgs[i+1] := gens[i+3];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;

    # check that indeed the surface relator is preserved
    x := surface_relator(F);
    Assert(0,ForAll(L,g->x^g=x));
    
    return Group(L);
end;


# a larger group, containing the "flip" (x_i -> y_{g+1-i}, y_i -> x_{g+1-i})
extended_mcg := function(F)
    local gens;
    gens := GeneratorsOfGroup(F);
    
    return ClosureGroup(pure_mcg(F),GroupHomomorphismByImages(F,F,Reversed(gens)));
end;

################################################################
# construct orbits on Q^{2n}
BS := BranchStructure(GrigorchukGroup);
F6 := FreeGroup(6);
#
#orbits of pure mcg
#
#The following lines take about 12h
orbits := OrbitsDomain(DirectProduct(pure_mcg(F6),BS.group),
                  Cartesian(ListWithIdenticalEntries(6,BS.group)),
                  function(list,elm)
    return OnTuples(OnImages(list,elm![1]),elm![2]);
end);;
Print("Orbits computed; there are ",Size(orbits)," orbits\n");
orbits := List(orbits,ShallowCopy);;
#The following lines take about 5min
for i in orbits do Sort(i); MakeImmutable(i); od; # for fast lookup
MakeImmutable(orbits);;

##################################################################
# Find Representatives with maximal number of ones and one in last coord.
MinimalReprOrbit := function(O)
    local cone,o,L,R,max,elm;
    cone := function(L)
        return Size(Filtered(L,IsOne));
    end;
    R := [];
    for o in O do
        max := 0;
        elm := 0;
        for L in o do
            if IsOne(L[6]) and cone(L) > max then
                max:=cone(L);
                elm := L;
            fi;
        od;
        if elm = 0 then
            Error("No fitting element found in orbit\n");
        fi;
        Add(R,elm);
    od;
    return R;
end;
orbitReps := MinimalReprOrbit(orbits);

#
# Save the orbit Representations to a file.
# Needs the following lines to be read again properly
#
orbitRepsFile := Concatenation(dir,"orbitReps.go");
PrintTo(orbitRepsFile,orbitReps);
#Replace <identy>.... by One(Q)
Exec("sed","-i","\"s/<identity> of .../One(Q)/g\"",orbitRepsFile);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitRepsFile);
Exec("sed","-i","\"\\$a ;\"",orbitRepsFile);
Q:= BS.group;
f4:= Q.1; # = a^π
f2 := Q.2; # = b^π
f1 := Q.3; # = c^π
f3 := f1*f2*f4*f1*f2; # = (dad)^π
Assert(0,ReadAsFunction(orbitRepsFile)()=orbitReps);


#
# Save a map which assigns to each element of Q⁵ the corresponding orbit.
#
hash := function(q)
	if q in Q then
		return Position(List(Q),q);
	else 
		Error("Can't compute hash ",q," is not in Q.");
	fi;
end;
ComputeTable := function(O)
	local Values,i,q1,q2,q3,q4,q5,o;
	i := 0;
	Values := ListWithIdenticalEntries(16,0);
	for q1 in Q do 
		Values[hash(q1)]:=ListWithIdenticalEntries(16,0);
		for q2 in Q do
			Values[hash(q1)][hash(q2)]:=ListWithIdenticalEntries(16,0);
			for q3 in Q do
				Values[hash(q1)][hash(q2)][hash(q3)]:=ListWithIdenticalEntries(16,0);
				for q4 in Q do
					Values[hash(q1)][hash(q2)][hash(q3)][hash(q4)]:=ListWithIdenticalEntries(16,0);
					for q5 in Q do
						Values[hash(q1)][hash(q2)][hash(q3)][hash(q4)][hash(q5)] := PositionProperty(O,o->[q1,q2,q3,q4,q5,One(Q)] in o);
						if i mod 1000 =0 then
							Print(i," Done ", Int(i*100/16^5),"%.\r");
						fi;
						i := i+1;
	od;od;od;od;od;
	Print("Done\n");
	return Values;
end;
#Takes ~10 Minutes 
orbitTable := ComputeTable(orbits);;

orbitTableFile := Concatenation(dir,"orbitTable.go");
PrintTo(orbitTableFile,orbitTable);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitTableFile);
Exec("sed","-i","\"\\$a ;\"",orbitTableFile);

#Check that everything worked as expected
Assert(0,orbitTable=ReadAsFunction(Concatenation(dir,"orbitTable.go"))());
#######################################################################################
#######################################################################################
#######################################################################################
#					Computation of the orbits now done
#######################################################################################
#######################################################################################
#######################################################################################