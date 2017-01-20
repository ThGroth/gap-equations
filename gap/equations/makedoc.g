dir := "doc/";
main := "equations.xml";
files := [	"../PackageInfo.g",
			"../lib/freeproducts.gd",
			"../lib/equations.gd",
			"../lib/normalform.gd" ];
bookname := "Equations";
MakeGAPDocDoc(dir,main,files,bookname,"../../");