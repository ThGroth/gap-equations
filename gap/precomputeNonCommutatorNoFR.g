if not IsBound(dir) then
    dir := Directory("gap");
fi;


NonCom := ReadAsFunction(Filename(dir,"noncommutatorNoFR.g"))();
GermGroup4 := NonCom.GermGroup4;
noncom := NonCom.noncom;

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

Assert(0,not IsCommutatorInFiniteGroup(GermGroup4,noncom) and
		noncom in DerivedSubgroup(GermGroup4));