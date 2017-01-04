if not IsBound(dir) then
    dir := Directory("gap");
fi;
################################################################

if not IsBound(DeclarationsLoadedFR)  then
    LoadPackage("fr");
    Read(Filename(dir,"declarationsFR.g"));
    Read(Filename(dir,"functionsFR.g"));
fi;

IsCommutatorInFiniteGroup := function(G,x)
	local tbl,irr,s,g,h,i,chi;
	tbl :=  CharacterTable(G);
	irr := Irr(tbl);
	s := 0;
	i := 0;
	for chi in irr do
		s := s+ x^chi/(One(G)^chi);
		Info(InfoCW,1,"Check if element is commutator: ",Int((i*100)/Size(irr)),"% done\r");
		i := i+1;
	od;
	Info(InfoCW,1,"Check if element is commutator: 100% done\n");
	return s<>0;
end;

quot := EpimorphismGermGroup(G,4);
GQ := Range(quot);
GQp := DerivedSubgroup(GQ);
CC := ConjugacyClasses(GQ);;
tbl := CharacterTable(GQ);
chTblFile := Filename(dir,"PCD/IrrGermGroup4.go");
irr := List(ReadAsFunction(chTblFile)(),L->Character(tbl,L));
SetIrr(tbl,irr);
#	irr:= Irr( tbl );;
derived:= Intersection(List(LinearCharacters( tbl ),ClassPositionsOfKernel) );;
commut:= Filtered([1 .. Length( irr )],i->not Sum( irr, chi -> chi[i]/chi[1] )=0);;
noncommut:= List( Difference(derived,commut), i->IdentificationOfConjugacyClasses(tbl)[i]);;
#	#gives [628,644]
noncoms := Concatenation(List(noncommut,i->List(CC[i])));;
noncomsG := List(noncoms,e->PreImagesRepresentative(quot,e));;
min := Minimum(List(noncomsG,e->Size(States(e))));
noncomMinStates := First(noncomsG,e->Size(States(e))=min);
Assert(0,not IsCommutatorInFiniteGroup(GQ,noncomMinStates^quot) and noncomMinStates in GQp);
noncomFile := Filename(dir,"PCD/noncommutator.go");
PrintTo(noncomFile,Concatenation("return ",String(noncomMinStates^isoGtoGLP),";"));

#	noncomGens := List(noncomsG,e->PreImagesRepresentative(EpimorphismFromFreeGroup(G),e));
#	minGens := Minimum(List(noncomGens,e->Length(e)));
#	noncomMinGens := First(noncomsG,e->Length(e)=minGens);

#noncomMinStates := (a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*(a*c*a*b)^3*a*c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^3*a*b*a*c*a*d*(a*c*a*b)^2\
#	)^5*a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*(a*c*a*b*a*c*a*d*a*c)^2*(a*b*a*c)^3*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^2*(a*c*a*b*(a*c)^3*a*b\
#	*a*c*a*d)^2*a*c*a*b*a*c*a*d*((a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^2*a*c*a*b*a*c*a*d*(a*c*a*b)^3*a*c*a*d*a*c*a*b*(a*c)^2)^2*((a*c*a*b*a*c*a*d)^3*a*c*a*b)^2*a*c*a*b*(a*c*a*b\
#	*a*c*a*d)^2*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^3*a*b*a; #29 states
#noncommMinGens := c*(a*c*a*b)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^2*a*c*a*b*(a*c*a*d)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^3*(a*c*a*b*a*c*a*d)^2*a*b*a*c*a*d*(a*c*a*b)^3*(a*c)^3*a*b*a*c*a*\
#	d*(a*c*a*b)^3*a*c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^2*a*c*a*b*(a*c*a*d*(a*c*a*b)^3*a*c*a*d)^2*(a*c*a*b*a*c*a*d)^2*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*(a*c*a*b)^3*a*\
#	c*a*d*a*c*a*b*(a*c)^2*(a*c*a*b*a*c*a*d)^3*a*c*a*b*(a*c)^3*a*b*a*c*a*d*(a*c*a*b)^2*(a*c*a*b*a*c*a*d*a*c*a*b*(a*c)^2)^2*a*c*a*b*a*c*a*d*a*c; #34 states
#Assert(2,not IsCommutatorInFiniteGroup(GQ,noncomMinGens^quot) and noncomMinStates in GQp);

# Show there is an element g ∈ G such that g@2⋅g@1 = noncomMinStates
# This is needed to show that noncomMinStates is not a product of 4 conjugates of a. 
noncomMinStatesList := [a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,b,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,d,a,c,a,b,a,c,a,c,a,c,a,b,a];
Assert(0,noncomMinStates=Product(noncomMinStatesList));
pifast := GroupHomomorphismByImagesNC(G,Q,[a,b,c,d],[a^pi,b^pi,c^pi,d^pi]);
noncomMinStatesListQ := List(noncomMinStatesList,x->x^pifast);
i := First([1..Length(noncomMinStatesList)],i-> ForAny(Source(BS.epi),
			wrE->wrE![2]=Product(noncomMinStatesListQ{[1..i]}) and 
				 wrE![1]=Product(noncomMinStatesListQ{[i+1..Length(noncomMinStatesList)]}) and
				 IsOne(wrE^BS.epi) ));
Assert(0,not i = fail);
x2 := Product(noncomMinStatesList{[1..i]});
x1 := x2^-1*noncomMinStates;
#i=2; x2 = a*c
#So by the properties of the branch structure the it holds that <<x1,x2>>∈ K < G'
nonConjugacyProduct := UnderlyingMealyElement(FRElement([[[x1],[x2]]],[()],[1]));