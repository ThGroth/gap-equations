#Precompute the 90 orbits of Q⁶/Stab(R₆)
#
# Directory for Saved results. 
#
if not IsBound(dir) then
    dir := Directory("gap");
fi;
################################################################

if not IsBound(DeclarationsLoadedFR)  then
    LoadPackage("fr");
    Read(Filename(dir,"declarationsFR.g"));
    Read(Filename(dir,"functionsFR.g"));
fi;

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
    #already contained in mcg !
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

################################################################
# construct orbits on Q^{2n}
#orbits of pure mcg
#
#The following lines take about 12h
Info(InfoCW,1,"Start computing the orbits. This will take about 12 hours.\n");
orbits := OrbitsDomain(pure_mcg(FreeGroup(6)),
                  Cartesian(ListWithIdenticalEntries(6,BS.group)),
                  OnImages);;

orbits2 := OrbitsDomain(pure_mcg(FreeGroup(4)),
                  Cartesian(ListWithIdenticalEntries(4,BS.group)),
                  OnImages);;

#orbits := OrbitsDomain(DirectProduct(pure_mcg(FreeGroup(6)),BS.group),
#                  Cartesian(ListWithIdenticalEntries(6,BS.group)),
#                  function(list,elm)
#    return OnTuples(OnImages(list,elm![1]),elm![2]);
#end);;
#orbits2 := OrbitsDomain(DirectProduct(pure_mcg(FreeGroup(4)),BS.group),
#                  Cartesian(ListWithIdenticalEntries(4,BS.group)),
#                  function(list,elm)
#    return OnTuples(OnImages(list,elm![1]),elm![2]);
#end);;
Info(InfoCW,1,"Orbits computed; there are ",Size(orbits)," orbits for Aut(F₆)/Stab(R₃)\n");
Info(InfoCW,1,"and there are ",Size(orbits2)," orbits for Aut(F₄)/Stab(R₂)\n");
orbits := List(orbits,ShallowCopy);;
orbits2 := List(orbits2,ShallowCopy);;
#The following lines take about 5min
Info(InfoCW,1,"Start sorting and saving the orbits. This will take about 30 Minutes\n");
for i in orbits do Sort(i); MakeImmutable(i); od; # for fast lookup
for i in orbits2 do Sort(i); MakeImmutable(i); od; # for fast lookup
MakeImmutable(orbits);;
MakeImmutable(orbits2);;

##################################################################
# Find Representatives with maximal number of ones and one in last coord.
MinimalReprOrbit := function(O)
    local cone,o,L,R,max,elm;
    cone := function(L)
        return Size(Filtered(L,IsOne));
    end;
    R := [];
    for o in O do
        max := -1;
        elm := 0;
        for L in o do
            if (Size(L)<6 or IsOne(L[6])) and cone(L) > max then
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
orbitReps2 := MinimalReprOrbit(orbits2);

#
# Save the orbit Representations to a file.
# Needs the following lines to be read again properly
#
orbitRepsFile := Filename(dir,"PCD/orbitReps.go");
orbitRepsFile2 := Filename(dir,"PCD/orbitReps2.go");
PrintTo(orbitRepsFile,orbitReps);
PrintTo(orbitRepsFile2,orbitReps2);
#Replace <identy>.... by One(Q)
Exec("sed","-i","\"s/<identity> of .../One(Q)/g\"",orbitRepsFile);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitRepsFile);
Exec("sed","-i","\"\\$a ;\"",orbitRepsFile);
Exec("sed","-i","\"s/<identity> of .../One(Q)/g\"",orbitRepsFile2);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitRepsFile2);
Exec("sed","-i","\"\\$a ;\"",orbitRepsFile2);
Q:= BS.group;
f4:= Q.1; # = a^π
f2 := Q.2; # = b^π
f1 := Q.3; # = c^π
f3 := f1*f2*f4*f1*f2; # = (dad)^π
Assert(0,ReadAsFunction(orbitRepsFile)()=orbitReps);
Assert(0,ReadAsFunction(orbitRepsFile2)()=orbitReps2);


ComputeTable := function(O)
	local Values,i,q1,q2,q3,q4,q5,o;
	i := 0;
	Values := ListWithIdenticalEntries(16,0);
	for q1 in Q do 
		Values[hashInQ(q1)]:=ListWithIdenticalEntries(16,0);
		for q2 in Q do
			Values[hashInQ(q1)][hashInQ(q2)]:=ListWithIdenticalEntries(16,0);
			for q3 in Q do
				Values[hashInQ(q1)][hashInQ(q2)][hashInQ(q3)]:=ListWithIdenticalEntries(16,0);
				for q4 in Q do
					Values[hashInQ(q1)][hashInQ(q2)][hashInQ(q3)][hashInQ(q4)]:=ListWithIdenticalEntries(16,0);
					for q5 in Q do
						Values[hashInQ(q1)][hashInQ(q2)][hashInQ(q3)][hashInQ(q4)][hashInQ(q5)] := [PositionProperty(O,o->[q1,q2,q3,q4,q5,One(Q)] in o)];
						if i mod 1000 =0 then
							Info(InfoCW,1,i," Done ", Int(i*100/16^5),"%.\r");
						fi;
						i := i+1;
	od;od;od;od;od;
	Info(InfoCW,1,"Done\n");
	return Values;
end;
ComputeTable2 := function(O)
    local Values,i,q1,q2,q3,q4,o;
    i := 0;
    Values := ListWithIdenticalEntries(16,0);
    for q1 in Q do 
        Values[hashInQ(q1)]:=ListWithIdenticalEntries(16,0);
        for q2 in Q do
            Values[hashInQ(q1)][hashInQ(q2)]:=ListWithIdenticalEntries(16,0);
            for q3 in Q do
                Values[hashInQ(q1)][hashInQ(q2)][hashInQ(q3)]:=ListWithIdenticalEntries(16,0);
                for q4 in Q do
                    Values[hashInQ(q1)][hashInQ(q2)][hashInQ(q3)][hashInQ(q4)] := PositionProperty(O,o->[q1,q2,q3,q4] in o);
                    if i mod 1000 =0 then
                        Info(InfoCW,1,i," Done ", Int(i*100/16^4),"%.\r");
                    fi;
                    i := i+1;
    od;od;od;od;
    Info(InfoCW,1,"Done\n");
    return Values;
end;

#Takes ~20 Minutes 
orbitTable := ComputeTable(orbits);;
orbitTable2 := ComputeTable2(orbits2);;

orbitTableFile := Filename(dir,"PCD/orbitTable.go");
PrintTo(orbitTableFile,orbitTable);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitTableFile);
Exec("sed","-i","\"\\$a ;\"",orbitTableFile);

orbitTableFile2 := Filename(dir,"PCD/orbitTable2.go");
PrintTo(orbitTableFile2,orbitTable2);
#Add a return and a semicolon
Exec("sed","-i","\"1i return \"",orbitTableFile2);
Exec("sed","-i","\"\\$a ;\"",orbitTableFile2);

#Check that everything worked as expected
Assert(0,orbitTable=ReadAsFunction(orbitTableFile)());
Assert(0,orbitTable2=ReadAsFunction(orbitTableFile)());
#######################################################################################
#######################################################################################
#######################################################################################
#					Computation of the orbits now done
#######################################################################################
#######################################################################################
#######################################################################################