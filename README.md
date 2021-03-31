# cade-28
This directory contains software related to the CADE-28 conference.

Compiling the files SCIDTMain.hs, SCILTMain.hs, and SCILTMainurf.hs with a Haskell compiler will produce the corresponding executables, with the same names except for the extension.

Instructions for use:

Each program will accept two arguments. The first is a single letter indicating the desired output format, and the second one is an SCI formula, which the program will attempt to prove. The arguments can be given on the command line, if desired; otherwise, the program will ask for them. Please note that the formula must be enclosed in quotes if given on the command line.

The output formats are "short", "normal", and "long", abbreviated as "s", "n", and "l", respectively. Additionally, the format letter "h" (for "help") will output a short reminder of the usage.

Any string of letters that is not a reserved word can be used as a variable name. Every connective can be given either as a word or as a symbol, as follows:

~   not
&   and
|   or
->  implies
<-> equiv
=   ident

The programs sometimes require parentheses in cases where they are usually omitted in normal mathematical text. For instance, "a & b & c" must be written as "(a & b) & c".

Any questions about the software can be directed to its author, Taneli Huuskonen, by e-mail to taneli (at) op (dot) pl .
