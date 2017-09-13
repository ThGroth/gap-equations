Info(InfoCW,1,"Compute character Table of Germ group. Will take about 3h\n");
GermGroup4 := Range(EpimorphismGermGroup(G,4));
tbl := CharacterTable(GermGroup4);
chTblFile := Filename(dir,"PCD/IrrGermGroup4.go");
PrintTo(chTblFile,Concatenation("return ",String(Irr(tbl)),";"));

