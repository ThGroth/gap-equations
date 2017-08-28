#TODO clean this up for publishing. Remove prints etc.
inter_pure_mcg_gens := function(F)
    local gens, d, L, i, imgs, x;
    gens := GeneratorsOfGroup(F);
    d := Length(gens);
    L := [];

    for i in [8] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i-1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [7] do
        imgs := ShallowCopy(gens);
        imgs[i] := gens[i+1]*gens[i];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;
    for i in [5] do
        imgs := ShallowCopy(gens);
        x := gens[i+1]/gens[i+2];
        imgs[i] := x*gens[i];
        imgs[i+1] := x*gens[i+1]/x;
        imgs[i+2] := x*gens[i+2]/x;
        imgs[i+3] := x*gens[i+3];
        Add(L,GroupHomomorphismByImages(F,F,imgs));
    od;

    # check that indeed the surface relator is preserved
    x := surface_relator(F);
    Assert(0,ForAll(L,g->x^g=x));
    
    return L;
end;




gens := inter_pure_mcg_gens(FreeGroup(8));

Firstpa := PCD.orbitReps2;;
Secondpa:= Cartesian(ListWithIdenticalEntries(4,BS.group));;

size := Size(Firstpa)*Size(Secondpa);
# Storing the results in a lookup dictionary doesn't help. 
# The lookup of all elements is not much faster.
TheTest := function()
    local gamma,gamma1,gamma2,theta,count,ind1,ind2;
    count := 1;
    for gamma1 in Secondpa do
        for gamma2 in Firstpa do
            gamma := Concatenation(gamma1,gamma2);
            for theta in gens do
                if not ReducedConstraint8(OnImages(gamma,theta)).index=ind2:=ReducedConstraint8(gamma).index then
                    Print("Claim not true for gamma:",gamma," and theta:",theta,"\n\n");
                    return [gamma,theta];
                fi;
            od;
            Print(count," that are ",Int(100*count/size),"% done\r");
            count := count +1;
    od;od;
    Print("\nClaim true\n");
    return [];
end;
res:=TheTest();
tt := time;
Int(tt/(60*60*1000));


