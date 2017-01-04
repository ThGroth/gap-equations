if not IsBound(dir) then
    dir := Directory("gap");
fi;

ignoreIrr := true;
NonCom := ReadAsFunction(Filename(dir,"noncommutatorNoFR.g"))();
GermGroup4 := NonCom.GermGroup4;
noncom := NonCom.noncom;
ignoreIrr := false;

tbl := CharacterTable(GermGroup4);
chTblFile := Filename(dir,"PCD/IrrGermGroup4noFR.go");
PrintTo(chTblFile,Concatenation("return ",String(Irr(tbl)),";"));

IsCommutatorInFiniteGroup := function(G,x)
	local tbl,irr,s,g,h;
	tbl :=  CharacterTable(G);
	irr := Irr(tbl);
	s := Sum(irr, chi -> x^chi/(One(G)^chi));
	return s<>0;
end;

Assert(0,not IsCommutatorInFiniteGroup(GermGroup4,noncom) and
		noncom in DerivedSubgroup(GermGroup4));