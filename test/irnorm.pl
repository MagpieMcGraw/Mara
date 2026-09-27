#!/usr/bin/perl
# irnorm.pl — canonical form of a Mara .ll file, for comparing codegen output
# modulo naming: inside each function, locals and labels are renamed by order
# of first appearance (%v0, %v1, ...); string globals are replaced by their
# contents. Named types (%class.X = type ...) are left alone.
# Usage: irnorm.pl file.ll > file.norm
use strict; use warnings;
my @lines = <>;
s/\r$// for @lines;
my (%str, %type);
for (@lines) {
    $str{$1}  = $2 if /^(@\.[\w.]*str\.[\w]+) = private unnamed_addr constant (.*)$/;
    $type{$1} = 1  if /^(%[-\w.\$]+) = type /;
}
my ($in_fn, %map, $n) = (0);
for (@lines) {
    if (/^define /) { $in_fn = 1; %map = (); $n = 0; }
    if ($in_fn) {
        s/^([-\w.\$]+):/($map{$1} \/\/= "v" . $n++) . ":"/e;          # label definition
        s/%([-a-zA-Z\$._][-\w.\$]*|\d+)/
            exists $type{"%$1"} ? "%$1" : "%" . ($map{$1} \/\/= "v" . $n++)/gex;
    }
    $in_fn = 0 if /^}/;
    # After renaming, so a string's own %s / %d stay as written.
    s/(@\.[\w.]*str\.[\w]+)/exists $str{$1} ? "\@STR<$str{$1}>" : $1/ge;
}
print @lines;
