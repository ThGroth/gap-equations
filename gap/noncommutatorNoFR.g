#Polycyclic version
local GermGroup0,PermGroup4,isoToPC,GG,GermGroup4,noncom,IsCommutatorInFiniteGroup;

GermGroup0 := Image(IsomorphismPcGroup(Group([(1,2),(3,4)])));
PermGroup4 := Group([ 
	(1,9)(2,10)(3,11)(4,12)(5,13)(6,14)(7,15)(8,16),
	(1,5)(2,6)(3,7)(4,8)(9,11)(10,12), 
	(1,5)(2,6)(3,7)(4,8)(13,14), 
	(9,11)(10,12)(13,14) ]);
isoToPC := IsomorphismPcGroup(PermGroup4);
GG := WreathProduct(GermGroup0,Range(isoToPC),InverseGeneralMapping(isoToPC),16);
GermGroup4 := Group(
		[GG.6,
		GG.2*GG.4*GG.6*GG.43,
		GG.1*GG.2*GG.4*GG.6*GG.11*GG.44,
		GG.1*GG.11*GG.43*GG.44]);
#Epi := GroupHomomorphismByImagesNC(GrigorchukGroup,GermGroup4);
noncom := Product([13,14,15,16,17,18,19,20,22,24,26,28,31,35,37,38,40,41,42,44],i->GG.(i));

IsCommutatorInFiniteGroup := function(G,x)
	local tbl,irr,s,g,h;
	tbl :=  CharacterTable(G);
	irr := Irr(tbl);
	s := Sum(irr, chi -> x^chi/(One(G)^chi));
	return s<>0;
end;
Assert(2,not IsCommutatorInFiniteGroup(GermGroup4,noncom) and
		noncom in DerivedSubgroup(GermGroup4));
return rec(GermGroup4:=GermGroup4, noncom := noncom);

###Permutation Group version (Too slow for computations)

#GermGroup0 := Group([(1,2),(3,4)]);
#PermGroup4 := Group([ 
#	(1,9)(2,10)(3,11)(4,12)(5,13)(6,14)(7,15)(8,16),
#	(1,5)(2,6)(3,7)(4,8)(9,11)(10,12), 
#	(1,5)(2,6)(3,7)(4,8)(13,14), 
#	(9,11)(10,12)(13,14) ]);
#GG := WreathProduct(GermGroup0,PermGroup4);
#GermGroup4 := Group(
#		[(1,33)(2,34)(3,35)(4,36)(5,37)(6,38)(7,39)(8,40)(9,41)(10,42)(11,43)(12,44)(13,45)(14,46)(15,47)(16,48)(17,49)(18,50)(19,51)(20,52)(21,53)(22,54)(23,55)(24,56)(25,57)(26,58)(27,59)(28,60)(29,61)(30,62)(31,63)(32,64),
#		(1,17,2,18)(3,19)(4,20)(5,21)(6,22)(7,23)(8,24)(9,25)(10,26)(11,27)(12,28)(13,29)(14,30)(15,31)(16,32)(33,41)(34,42)(35,43)(36,44)(37,45)(38,46)(39,47)(40,48),
#		(1,17)(2,18)(3,19)(4,20)(5,21)(6,22)(7,23)(8,24)(9,29)(10,30)(11,31)(12,32)(13,25)(14,26)(15,27)(16,28)(33,41,34,42)(35,43)(36,44)(37,45)(38,46)(39,47)(40,48)(49,57,53,61)(50,58,54,62)(51,59,55,63)(52,60,56,64),
#		(1,2)(9,13)(10,14)(11,15)(12,16)(25,29)(26,30)(27,31)(28,32)(33,34)(49,57,53,61)(50,58,54,62)(51,59,55,63)(52,60,56,64) ]);
#Epi := GroupHomomorphismByImagesNC(GrigorchukGroup,GermGroup4);
