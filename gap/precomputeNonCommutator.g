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
	s := Sum(irr, chi -> x^chi/(One(G)^chi));
	return s<>0;
end;

quot := EpimorphismGermGroup(G,4);
GQ := Range(quot);
GQp := DerivedSubgroup(GQ);
#	CC := ConjugacyClasses(GQ);;
#	tbl := CharacterTable(GQ);;
#	irr:= Irr( tbl );;
#	derived:= Intersection(List(LinearCharacters( tbl ),ClassPositionsOfKernel) );;
#	commut:= Filtered([1 .. Length( irr )],i->not Sum( irr, chi -> chi[i]/chi[1] )=0);;
#	noncommut:= List( Difference(derived,commut), i->IdentificationOfConjugacyClasses(tbl)[i]);;
#	#gives [628,644]
#	noncoms := Concatenation(List([628, 644],i->List(CC[i])));;
#	noncomsG := List(noncoms,e->PreImagesRepresentative(quot,e));;
#	min := Minimum(List(noncomsG,e->Size(States(e))));
#	noncomMinStates := First(noncomsG,e->Size(States(e))=min);

#	noncomGens := List(noncomsG,e->PreImagesRepresentative(EpimorphismFromFreeGroup(G),e));
#	minGens := Minimum(List(noncomGens,e->Length(e)));
#	noncomMinGens := First(noncomsG,e->Length(e)=minGens);
noncomMinStates := (a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*(a*c*a*b)^3*a*c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^3*a*b*a*c*a*d*(a*c*a*b)^2\
	)^5*a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*(a*c*a*b*a*c*a*d*a*c)^2*(a*b*a*c)^3*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^2*(a*c*a*b*(a*c)^3*a*b\
	*a*c*a*d)^2*a*c*a*b*a*c*a*d*((a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^2*a*c*a*b*a*c*a*d*(a*c*a*b)^3*a*c*a*d*a*c*a*b*(a*c)^2)^2*((a*c*a*b*a*c*a*d)^3*a*c*a*b)^2*a*c*a*b*(a*c*a*b\
	*a*c*a*d)^2*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^3*a*b*a; #29 states
noncommMinGens := c*(a*c*a*b)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^2*a*c*a*b*(a*c*a*d)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^3*(a*c*a*b*a*c*a*d)^2*a*b*a*c*a*d*(a*c*a*b)^3*(a*c)^3*a*b*a*c*a*\
	d*(a*c*a*b)^3*a*c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*a*c*a*b*(a*c*a*d*(a*c*a*b)^3*a*c*a*d)^2*(a*c*a*b*a*c*a*d)^2*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*(a*c*a*b)^3*a*\
	c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^3*a*b*a*c*a*d*(a*c*a*b)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^2*a*c*a*b*a*c*a*d*a*c; #34 states
Assert(2,not IsCommutatorInFiniteGroup(GQ,noncomMinStates^quot) and noncomMinStates in GQp);
Assert(2,not IsCommutatorInFiniteGroup(GQ,noncomMinGens^quot) and noncomMinStates in GQp);