DeclareInfoClass("InfoExamples");
SetInfoLevel(InfoExamples,2);

#Changes here to allow Info messages without a newline.
SetInfoHandler(InfoExamples,function( infoclass, level, list )
  local cl, out, fun, s;
  cl := InfoData.LastClass![1];
  if IsBound(InfoData.Output[cl]) then
    out := InfoData.Output[cl];
  else
    out := DefaultInfoOutput;
  fi;
  if out = "*Print*" then
    if IsBoundGlobal( "PrintFormattedString" ) then
      fun := function(s)
        if (IsString(s) and Length(s) > 0) or IsStringRep(s) and
                 NARG_FUNC(ValueGlobal("PrintFormattedString")) <> -1 then
          ValueGlobal( "PrintFormattedString" )(s);
        else
          Print(s);
        fi;
      end;
    else
      fun := Print;
    fi;
    fun("#I  ");
    for s in list do
      fun(s);
    od;
    #fun("\n"); No newlines. Otherwise progress information is not printed.
  else
    AppendTo(out, "#I  ");
    for s in list do
      AppendTo(out, s);
    od;
    #AppendTo(out, "\n");
  fi;
end);


if not TestPackageAvailability( "LPRES","0.3") = fail then
	LoadPackage("lpres");
else
	SetPackagePath("lpres","extern/lpres/");
fi;

if not TestPackageAvailability( "fr","2.3") = fail then
	LoadPackage("fr");
else
	Info(InfoExamples,0,"For some functionality the fr package must be availabil in version at least 2.3\n");
	if TestPackageAvailability("fr") then
		Info(InfoExamples,0,"Try to use Verion ",InstalledPackageVersion("fr")," instead.\n");
		LoadPackage("fr");	
	else
		SetPackagePath("fr","extern/fr/");
	fi;
fi;
if not TestPackageAvailability("equations","0.1.3") = fail then
	LoadPackage("equations");
else
	SetPackagePath("equations","../");
	LoadPackage("equations");
fi;

