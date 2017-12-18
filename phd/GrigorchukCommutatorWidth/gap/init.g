if not IsBound(dir) then
    dir := Directory("gap");
fi;
DeclareInfoClass("InfoCW");
SetInfoLevel(InfoCW,2);
SetInfoHandler(InfoCW,function( infoclass, level, list )
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
          #XXX this is a temporary hack, we would need a
          # IsInstalledGlobal instead of IsBoundGlobal here
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
DeclarationsLoadedFR := false;
DeclarationsLoaded := false;

