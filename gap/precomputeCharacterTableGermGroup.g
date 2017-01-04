
GermGroup4 := Range(EpimorphismGermGroup(G,4));
tbl := CharacterTable(GermGroup4);
chTblFile := Filename(dir,"PCD/IrrGermGroup4.go");
PrintTo(chTblFile,Concatenation("return ",String(Irr(tbl)),";"));

