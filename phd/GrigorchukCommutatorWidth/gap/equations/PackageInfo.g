#############################################################################
##  
##  PackageInfo.g for the package `Equations'                   Thorsten Groth
##                                                                
##  (created from Frank Lübeck's PackageInfo.g template file)
##  
##
##  With a new release of the package at least the entries .Version, .Date 
##  and .ArchiveURL must be updated.

SetPackageInfo( rec(

PackageName := "Equations",

Subtitle := "Equations in groups",

Version := "0.1.3",

Date := "15/03/2017",
##  <#GAPDoc Label="PKGVERSIONDATA">
##  <!ENTITY VERSION "0.1.2">
##  <!ENTITY RELEASEDATE "15 March 2017">
##  <#/GAPDoc>

#PackageWWWHome := "http://",

#ArchiveURL := Concatenation( ~.PackageWWWHome, "example-", ~.Version ),
#ArchiveFormats := ".tar.gz",

TextFiles := ["init.g","equations.gd","equations.gi","freeproducts.gd","freeproducts.gi","normalform.gd","normalform.gi","decomposable.gd","decomposable.gi"],
#BinaryFiles := ["doc/manual.dvi", ......],
#TextBinaryFilesPatterns := [ "TGPLv3", "Texamples/*", "B*.in", ......],


##  Information about authors and maintainers is contained in the `Persons'
##  field which is a list of records, one record for each person; each 
##  person's record should be as per the following example: 
##  
##     rec(
##     # these are compulsory, the strings can be encoded in UTF-8 or latin1,
##     # so using German umlauts or other special characters is ok:
##     LastName := "Müller",
##     FirstNames := "Fritz Eduard",
##  
##     # At least one of the following two entries must be given and set 
##     # to 'true' (an entry can be left out if value is not 'true'):
##     IsAuthor := true;
##     IsMaintainer := true;
##  
##     # At least one of the following three entries must be given 
##     # for each maintainer of the package:
##     # - preferably email address and WWW homepage
##     # - postal address not needed if email or WWW address available
##     # - if no contact known, specify postal address as "no address known"
##     Email := "Mueller@no.org",
##     # complete URL, starting with protocol
##     WWWHome := "http://www.no.org/~Mueller",
##     # separate lines by '\n' (*optional*)
##     PostalAddress := "Dr. F. Müller\nNo Org Institute\nNo Place 13\n\
##     12345 Notown\nNocountry"
##     
##     # If you want, add one or both of the following entries (*optional*)
##     Place := "Notown",
##     Institution := "Institute for Nothing"
##     )
##  
Persons := [
  rec( 
    LastName      := "Groth",
    FirstNames    := "Thorsten",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email         := "thorsten.groth@mathematik.uni-goettingen.de",
    #WWWHome       := "http://www.",
    #PostalAddress := "",
    Place         := "Göttingen",
    Institution   := "Georg August Universität"
  ),
],

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed 
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages 
##    "other"         for all other packages
##
# Status := "accepted",
Status := "other",

##  You must provide the next two entries if and only if the status is 
##  "accepted" because is was successfully refereed:
# format: 'name (place)'
# CommunicatedBy := "Mike Atkinson (St. Andrews)",
#CommunicatedBy := "",
# format: mm/yyyy
# AcceptDate := "08/1999",
#AcceptDate := "",

##  For a central overview of all packages and a collection of all package
##  archives it is necessary to have two files accessible which should be
##  contained in each package:
##     - A README file, containing a short abstract about the package
##       content and installation instructions.
##     - The PackageInfo.g file you are currently reading or editing!
##  You must specify URLs for these two files, these allow to automate 
##  the updating of package information on the GAP Website, and inclusion
##  and updating of the package in the GAP distribution.
#
#README_URL := 
#  Concatenation( ~.PackageWWWHome, "README" ),
#PackageInfoURL := 
#  Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),

AbstractHTML := Concatenation( [
  "The <span class=\"pkgname\">Equation</span> package, allows to",
  "define equation in a group G as elements of a free product",
  "of a free group F and the group G."]),


#PackageDoc := rec(
#  # use same as in GAP            
#  BookName  := "Example",
#  # format/extension can be one of .tar.gz, .tar.bz2, -win.zip, .zoo.
#  ArchiveURLSubset := ["doc"],
#  HTMLStart := "doc/chap0.html",
#  PDFFile   := "doc/manual.pdf",
#  # the path to the .six file used by GAP's help system
#  SixFile   := "doc/manual.six",
#  # a longer title of the book, this together with the book name should
#  # fit on a single text line (appears with the '?books' command in GAP)#
#  LongTitle := "Elementary Divisors of Integer Matrices",
#  LongTitle := "Example/Template of a GAP Package",
#),


##  Are there restrictions on the operating system for this package? Or does
##  the package need other packages to be available?
Dependencies := rec(
  # GAP version, use the version string for specifying a least version,
  # prepend a '=' for specifying an exact version.
  GAP := "4.5.3",

  # list of pairs [package name, version], package name is case
  # insensitive, exact version denoted with '=' prepended to version string.
  # without these, the package will not load
  # NeededOtherPackages := [["GAPDoc", "1.5"]],
  NeededOtherPackages := [["GAPDoc", "1.5"]],

  # list of pairs [package name, version] as above,
  # these package are will be loaded if they are available,
  # but the current package will be loaded if they are not available
  # SuggestedOtherPackages := [],
  SuggestedOtherPackages := [["FR", "2.2"]],                      
),

##  Provide a test function for the availability of this package.
##  For packages containing nothing but GAP code, just say 'ReturnTrue' here.
##  For packages which may not work or will have only partial functionality,
##  use 'LogPackageLoadingMessage( PACKAGE_WARNING, ... )' statements to
##  store messages which may be viewed later with `DisplayPackageLoadingLog'.
##  Do not call `Print' or `Info' in the `AvailabilityTest' function of the 
##  package.
##
##  With the package loading mechanism of GAP >=4.4, the availability
##  tests of other packages, as given under .Dependencies above, will be 
##  done automatically and need not be included in this function.
##
AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",
));

