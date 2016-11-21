if not FileExists("./gap/declarations.g") then
    Error("Please start this 'testall.g' script in the main directory of the archive.");
fi;

dir := Directory("gap");

Read(File(dir,"declarations.g"));

etc.
