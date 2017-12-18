LoadPackage("equations");
SetInfoLevel(InfoEQFP,1);
dirs := DirectoriesPackageLibrary("equations","tst");
Test(Filename(dirs,"equations.tst"));
Test(Filename(dirs,"normalform.tst"));