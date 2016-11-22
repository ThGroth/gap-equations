if not IsBound(dirRep) then
    dirRep := "~/Repositories/GrigorchukCommutatorWidth/";
    #
    dir := Concatenation(dirRep,"gap/90orbs/");
fi;
if not IsBound(DeclarationsLoaded)  then
    Read(Concatenation(dirRep,"gap/declarations.g"));
    Read(Concatenation(dirRep,"gap/functions.g"));
fi;
IsCommutatorInFiniteGroup := function(G,x)
	local tbl,irr,s,g,h;
	tbl :=  CharacterTable(G);
	irr := Irr(tbl);
	s := Sum( irr, chi -> x^chi/(One(G)^chi) );
	return s<>0;
end;


findNonCommutator:= function()
	local i,g,rad,sphere;
	i := 0;
	Unbind(Gp!.FRData);
	SEARCH@fr.INIT(Gp);
	Gp!.FRData.pifunc := EpimorphismPermGroup;
	while true do
		for g in List(ConjugacyClasses(Range(Gp!.FRData.pi)),Representative) do
			if not IsCommutatorInFiniteGroup(Range(EpimorphismPermGroup(G,Gp!.FRData.level)),g) then 
				return [Gp!.FRData.level,Gp!.FRData.pi,g];
			fi;
		od;
        if SEARCH@fr.EXTEND(Gp,SEARCH@fr.QUOTIENT)=fail then
			Error("Preset limits reached.");
        fi;
	od;
end;
nonCom := findNonCommutator();
nonComG := PreImagesRepresentative(nonCom[2],nonCom[3]);
hom := EpimorphismFromFreeGroup(G);
elmInGGen := PreImagesRepresentative(hom,nonComG);
